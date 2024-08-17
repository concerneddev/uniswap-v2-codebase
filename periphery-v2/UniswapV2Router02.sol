pragma solidity =0.6.6;

import "@uniswap/v2-core/contracts/interfaces/IUniswapV2Factory.sol";
import "@uniswap/lib/contracts/libraries/TransferHelper.sol";

import "./interfaces/IUniswapV2Router02.sol";
import "./libraries/UniswapV2Library.sol";
import "./libraries/SafeMath.sol";
import "./interfaces/IERC20.sol";
import "./interfaces/IWETH.sol"; /// @dev: Returns WTH in exchange of ETH. It is ERC20 version of ETH

/**
@title UniswpV2Router02
@dev This contract is used to interact with the core contracts. UniswapV2Router01 has some issues, and has since been deprecated
 */
contract UniswapV2Router02 is IUniswapV2Router02 {
    using SafeMath for uint;

    address public immutable override factory;
    address public immutable override WETH;

    /// @dev This modifier makes sure that time limited transactions dont happen after their time limit.
    modifier ensure(uint deadline) {
        require(deadline >= block.timestamp, "UniswapV2Router: EXPIRED");
        _;
    }

    /// @dev This contstructor sets immutable state-variables
    constructor(address _factory, address _WETH) public {
        factory = _factory;
        WETH = _WETH;
    }

    /// @dev This function is called when we redeem tokens from the WETH contract back into ETH. Only the WETH contract is authorised to do that.
    receive() external payable {
        assert(msg.sender == WETH); // only accept ETH via fallback from the WETH contract
    }

    // **** ADD LIQUIDITY ****
    /// @dev Internal function to calculate and add the optimal amounts of two tokens for liquidity provision.
    /// This function ensures that the liquidity provided meets the desired and minimum amounts specified by the caller.
    /// If the trading pair does not exist, it creates the pair through the Uniswap V2 factory.
    /// @param tokenA The address of the ERC-20 token contract for Token A.
    /// @param tokenB The address of the ERC-20 token contract for Token B.
    /// @param amountADesired The desired amount of Token A to be added as liquidity.
    /// @param amountBDesired The desired amount of Token B to be added as liquidity.
    /// @param amountAMin The minimum acceptable amount of Token A to be added as liquidity.
    /// @param amountBMin The minimum acceptable amount of Token B to be added as liquidity.
    /// @notice **amountAMin and amountBMin** are critical for protecting against unfavourable market conditions.
    /// @return amountA The actual amount of Token A that was added as liquidity.
    /// @return amountB The actual amount of Token B that was added as liquidity.
    /// @notice This functions returns amounts of liquidity the provider should deposit to have a ratio equal to current ratio between reserves.
    function _addLiquidity(
        address tokenA,
        address tokenB,
        uint amountADesired,
        uint amountBDesired,
        uint amountAMin,
        uint amountBMin
    ) internal virtual returns (uint amountA, uint amountB) {
        // If there is no exchange pair yet, create it.
        if (IUniswapV2Factory(factory).getPair(tokenA, tokenB) == address(0)) {
            IUniswapV2Factory(factory).createPair(tokenA, tokenB);
        }

        // Get current reserves that are present in the pair.
        (uint reserveA, uint reserveB) = UniswapV2Library.getReserves(
            factory,
            tokenA,
            tokenB
        );

        // If current reserves are empty, this is a new pair.
        // Amounts to be deposited must be exactly same as those LP wants to provide.
        if (reserveA == 0 && reserveB == 0) {
            (amountA, amountB) = (amountADesired, amountBDesired);
        } else {
            // If we need to see what the amount will be, we get the optimal amount from this function.
            // We want the same ratios as current reserves.
            uint amountBOptimal = UniswapV2Library.quote(
                amountADesired,
                reserveA,
                reserveB
            );

            // If amountBOptimal is smaller, it means that token B is more valuable than the depositor thinks.
            // Meaning, there is more qty of token B in the pool in relation to token A
            // Hence, amountB to deposit is lesser than amountBDesired
            if (amountBOptimal <= amountBDesired) {
                require(
                    amountBOptimal >= amountBMin,
                    "UniswapV2Router: INSUFFICIENT_B_AMOUNT"
                );
                (amountA, amountB) = (amountADesired, amountBOptimal);

                // Else, if amountBOptimal is greater than amountBDesired, it means that token B is less valuable currently
                // than the depositer thinks.
                // Meaning, there is less qty of token B in the pool in relation to token A
                // Hence, higher amountB is required.
                // But amountBDesired is maximum, hence we cannot do that.
                // Hence, calculate amountAOptimal for amountBDesired
            } else {
                uint amountAOptimal = UniswapV2Library.quote(
                    amountBDesired,
                    reserveB,
                    reserveA
                );
                assert(amountAOptimal <= amountADesired);
                require(
                    amountAOptimal >= amountAMin,
                    "UniswapV2Router: INSUFFICIENT_A_AMOUNT"
                );
                (amountA, amountB) = (amountAOptimal, amountBDesired);
            }
        }
    }

    /**
    @dev This function can be called by a transaction to deposit liquidity. 
    @param tokenA The address of the ERC-20 token contract for Token A.
    @param tokenB The address of the ERC-20 token contract for Token B.
    @param amountADesired The desired amount of Token A to be added as liquidity.
    @param amountBDesired The desired amount of Token B to be added as liquidity.
    @param amountAMin The minimum acceptable amount of Token A to be added as liquidity.
    @param amountBMin The minimum acceptable amount of Token B to be added as liquidity.
    @param to This is the address that gets the new liquidity tokens minted to show the liquidity provider's portion
    of the pool.
    @param deadline The natural time limit on the transaction
    @return amountA, amountB The amounts actually deposited
    @return liquidity The amount of liquidity tokens minted in turn for amounts deposited.
     */
    function addLiquidity(
        address tokenA,
        address tokenB,
        uint amountADesired,
        uint amountBDesired,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    )
        external
        virtual
        override
        ensure(deadline)
        returns (uint amountA, uint amountB, uint liquidity)
    {
        // Calculate amounts to actually deposit
        (amountA, amountB) = _addLiquidity(
            tokenA,
            tokenB,
            amountADesired,
            amountBDesired,
            amountAMin,
            amountBMin
        );

        // Find the address of the liquidity pool
        // To save gas, instead of asking the factory directly, we use pairFor library function
        address pair = UniswapV2Library.pairFor(factory, tokenA, tokenB);

        // Transfer correct amounts of tokens from the user into the pair exchange
        TransferHelper.safeTransferFrom(tokenA, msg.sender, pair, amountA);
        TransferHelper.safeTransferFrom(tokenB, msg.sender, pair, amountB);

        // Give the "to" address liquidity tokens for partial ownership of the pool.
        // .mint() sees the number of tokens in "to" address and mints liquidity accordingly.
        liquidity = IUniswapV2Pair(pair).mint(to);
    }

    /**
    @dev This function is used to provide liquidity to TOKEN/ETH pair exchange.
    The user sends the ETH with the transaction, hence it is not specifed in the params.
    The contract handles the wrapping of ETH for the liquidity provider.
    @param token The address of the ERC-20 token.
    @param amountTokenDesired The amount of ERC-20 tokens LP desires to deposit.
    @param amountTokenMin The minimum amount the LP can deposit.
    @param amountETHMin The minimum amount of ETH LP can deposit.
    @param to The address where the liquidity tokens will mint to.
    @param deadline The natural time limit on the transaction
    @return amountA, amountB The amounts actually deposited
    @return liquidity The amount of liquidity tokens minted in turn for amounts deposited.
    */
    function addLiquidityETH(
        address token,
        uint amountTokenDesired,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    )
        external
        payable
        virtual
        override
        ensure(deadline)
        returns (uint amountToken, uint amountETH, uint liquidity)
    {
        // Calculate amounts to actually deposit.
        (amountToken, amountETH) = _addLiquidity(
            token,
            WETH,
            amountTokenDesired,
            msg.value,
            amountTokenMin,
            amountETHMin
        );

        // The address of the liquidity pool while saving on gas
        address pair = UniswapV2Library.pairFor(factory, token, WETH);

        // Transfer correct amounts of tokens
        TransferHelper.safeTransferFrom(token, msg.sender, pair, amountToken);

        // To deposit ETH, the contract wraps the ETH into WETH ...
        IWETH(WETH).deposit{value: amountETH}();

        // ... then transfers the WETH into the pair.
        // Transfer call is wrapped in assert, meaning if transfer fails this contract call also fails.
        assert(IWETH(WETH).transfer(pair, amountETH));

        // The amount of liqudity tokens minted
        liquidity = IUniswapV2Pair(pair).mint(to);

        // Refund if there is any extra ETH left.
        if (msg.value > amountETH)
            TransferHelper.safeTransferETH(msg.sender, msg.value - amountETH);
    }

    // **** REMOVE LIQUIDITY ****
    /**
    @dev This function will remove liquidity and pay back the LP
    @param tokenA_tokenB The addresses of token A and B
    @param liquidity The amount of liquidity tokens to burn
    @param amountAMin_amountBMin The minimum amount of each token the LP agrees to accept
    @param to The address where to send the tokens
    @param deadline The deadline of the transaction
     */
    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    )
        public
        virtual
        override
        ensure(deadline)
        returns (uint amountA, uint amountB)
    {
        // Get address of the pool with gas efficiency.
        address pair = UniswapV2Library.pairFor(factory, tokenA, tokenB);

        // Send liquidity tokens to the pair
        IUniswapV2Pair(pair).transferFrom(msg.sender, pair, liquidity);

        // Burn the liquidity and pay the user back the tokens. Handled by the core contract.
        (uint amount0, uint amount1) = IUniswapV2Pair(pair).burn(to);

        // Get address of token A
        (address token0, ) = UniswapV2Library.sortTokens(tokenA, tokenB);

        // Translate the way the contract returns the values to the way user expects them.
        // The contract returns them by lower address token first
        // We sort it to corresponding to token A and token B
        (amountA, amountB) = tokenA == token0
            ? (amount0, amount1)
            : (amount1, amount0);

        // Here, in this function we have done the transfer first and then we verify its legitimacy.
        // We can revert the transfer if its not legitimate.
        require(
            amountA >= amountAMin,
            "UniswapV2Router: INSUFFICIENT_A_AMOUNT"
        );
        require(
            amountB >= amountBMin,
            "UniswapV2Router: INSUFFICIENT_B_AMOUNT"
        );
    }

    /**
    @dev This function will remove liquidity and pay back the LP
    @param tokenA_tokenB The addresses of token A and B
    @param liquidity The amount of liquidity tokens to burn
    @param amountAMin_amountBMin The minimum amount of each token the LP agrees to accept
    @param to The address where to send the tokens
    @param deadline The deadline of the transaction
    @notice Same as the removeLiquidty(), except we receive the WETH tokens and redeem them for ETH 
    to transfer them to the LP.
     */
    function removeLiquidityETH(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    )
        public
        virtual
        override
        ensure(deadline)
        returns (uint amountToken, uint amountETH)
    {
        (amountToken, amountETH) = removeLiquidity(
            token,
            WETH,
            liquidity,
            amountTokenMin,
            amountETHMin,
            address(this),
            deadline
        );
        TransferHelper.safeTransfer(token, to, amountToken);
        IWETH(WETH).withdraw(amountETH);
        TransferHelper.safeTransferETH(to, amountETH);
    }

    /**
    @dev This function will remove liquidity and pay back the LP
    @param tokenA_tokenB The addresses of token A and B
    @param liquidity The amount of liquidity tokens to burn
    @param amountAMin_amountBMin The minimum amount of each token the LP agrees to accept
    @param to The address where to send the tokens
    @param deadline The deadline of the transaction
    @notice These functions (...WithPermit()) relay meta-transactions to allow users without ether to
    withdraw from the pool, using the permit mechanism

    What is a meta-transaction?
    Meta-transactions allow someone else (often a relayer) to pay the gas fees on behalf of the user. The user signs a transaction off-chain (which doesn't cost any gas) and sends it to a relayer. The relayer then submits the transaction on-chain and pays the gas fee.

    This allows users who don't have Ether to still interact with the blockchain.

    What is the permit mechanism?

    The permit function is part of the ERC-2612 standard, which allows approvals (e.g., giving permission for a contract to spend tokens on your behalf) to be made via a signature, instead of requiring an on-chain transaction (which would normally require gas).
    
    This means a user can authorize a contract to perform actions on their behalf by signing a message off-chain.
     */
    function removeLiquidityWithPermit(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external virtual override returns (uint amountA, uint amountB) {
        address pair = UniswapV2Library.pairFor(factory, tokenA, tokenB);
        uint value = approveMax ? uint(-1) : liquidity;
        IUniswapV2Pair(pair).permit(
            msg.sender,
            address(this),
            value,
            deadline,
            v,
            r,
            s
        );
        (amountA, amountB) = removeLiquidity(
            tokenA,
            tokenB,
            liquidity,
            amountAMin,
            amountBMin,
            to,
            deadline
        );
    }
    function removeLiquidityETHWithPermit(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external virtual override returns (uint amountToken, uint amountETH) {
        address pair = UniswapV2Library.pairFor(factory, token, WETH);
        uint value = approveMax ? uint(-1) : liquidity;
        IUniswapV2Pair(pair).permit(
            msg.sender,
            address(this),
            value,
            deadline,
            v,
            r,
            s
        );
        (amountToken, amountETH) = removeLiquidityETH(
            token,
            liquidity,
            amountTokenMin,
            amountETHMin,
            to,
            deadline
        );
    }

    // **** REMOVE LIQUIDITY (supporting fee-on-transfer tokens) ****

    /**
    @notice This function is used for tokens that have transfer or storage fees.
    In this case, we cannot rely on the removeLiquidity function to tell us how much of the token
    we get back. Hence, we withdraw it first and then get the balance.

     */
    function removeLiquidityETHSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) public virtual override ensure(deadline) returns (uint amountETH) {
        (, amountETH) = removeLiquidity(
            token,
            WETH,
            liquidity,
            amountTokenMin,
            amountETHMin,
            address(this),
            deadline
        );
        TransferHelper.safeTransfer(
            token,
            to,
            IERC20(token).balanceOf(address(this))
        );
        IWETH(WETH).withdraw(amountETH);
        TransferHelper.safeTransferETH(to, amountETH);
    }

    /**
    @notice This function combines storage fees with meta-transactions.
     */
    function removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external virtual override returns (uint amountETH) {
        address pair = UniswapV2Library.pairFor(factory, token, WETH);
        uint value = approveMax ? uint(-1) : liquidity;
        IUniswapV2Pair(pair).permit(
            msg.sender,
            address(this),
            value,
            deadline,
            v,
            r,
            s
        );
        amountETH = removeLiquidityETHSupportingFeeOnTransferTokens(
            token,
            liquidity,
            amountTokenMin,
            amountETHMin,
            to,
            deadline
        );
    }

    // **** SWAP ****
    // requires the initial amount to have already been sent to the first pair
    /**
    @dev This is an internal function that performs processing and required for other functions
    that are exposed to traders.
    There exist concept of Path for exchange. 
    If user wants to exchange A for D, a trader can exchange A for B, B for C and C for D. 
    So no need for direct A-D pair exchange.
    The prices of these markets tend to be synchronised because when they are out of sync it creates
    arbitrage opportunity.

    This function executes a series of token swaps along a specified path.
    @param amounts Array of token amounts at each step in the swap path. 
                `amounts[0]` is the input amount, while `amounts[i+1]` represents the expected output amount after each swap.
    @param path Array of token addresses representing the swap path.
                The first element is the input token address, and the last element is the output token address.
                Intermediate elements are addresses of tokens to swap through.
    @param to The address that will receive the final output tokens after the last swap in the path.
     */
    function _swap(
        uint[] memory amounts,
        address[] memory path,
        address _to
    ) internal virtual {
        // Iterate over each token in the path, except for the last one
        for (uint i; i < path.length - 1; i++) {
            // Get the current pair of tokens to swap: input and output tokens
            (address input, address output) = (path[i], path[i + 1]);

            // Sort the tokens so we can work with the pair contract
            (address token0, ) = UniswapV2Library.sortTokens(input, output);

            // Get the expected amount of the output token from this swap
            uint amountOut = amounts[i + 1];

            // Determine how much of each token will be sent out, according to the pair's expectations
            // ** uint(0) because that would be our input token
            (uint amount0Out, uint amount1Out) = input == token0
                ? (uint(0), amountOut)
                : (amountOut, uint(0));

            // Determine where the output tokens should be sent:
            // If this is the last swap, send to the destination address (_to),
            // Otherwise, send to the next pair in the path
            address to = i < path.length - 2
                ? UniswapV2Library.pairFor(factory, output, path[i + 2])
                : _to;

            // Execute the swap on the pair contract, sending the output tokens to the correct address
            // We don't need any extra data (bytes), so we pass an empty bytes object
            IUniswapV2Pair(UniswapV2Library.pairFor(factory, input, output))
                .swap(amount0Out, amount1Out, to, new bytes(0));
        }
    }

    /**
     * @dev Executes a swap from an exact amount of input tokens to as many output tokens as possible along a specified path.
     *      Ensures the output is at least the minimum amount expected by the trader, or the transaction reverts.
            Here, we specify the exact number of input tokens he is willing to give, ant the minimum amount of tokens
            he is willing to receive in return.
     * @param amountIn The amount of input tokens to send.
     * @param amountOutMin The minimum amount of output tokens the trader is willing to accept.
     * @param path The swap path as an array of token addresses. The first address is the input token, and the last is the output token.
     * @param to The address that will receive the output tokens.
     * @param deadline The latest time the transaction is valid. Must be executed before this time.
     * @return amounts The amounts of tokens received at each step in the path.
     */
    function swapExactTokensForTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    )
        external
        virtual
        override
        ensure(deadline)
        returns (uint[] memory amounts)
    {
        // Calculate the amount of output tokens at each step in the swap path
        amounts = UniswapV2Library.getAmountsOut(factory, amountIn, path);

        // Ensure the final output amount is at least the minimum specified by the trader
        require(
            amounts[amounts.length - 1] >= amountOutMin,
            "UniswapV2Router: INSUFFICIENT_OUTPUT_AMOUNT"
        );

        // Transfer the input tokens from the trader to the first pair contract in the path
        TransferHelper.safeTransferFrom(
            path[0],
            msg.sender,
            UniswapV2Library.pairFor(factory, path[0], path[1]),
            amounts[0]
        );

        // Execute the token swaps along the specified path
        _swap(amounts, path, to);
    }

    /**
     * @dev Swaps tokens where the trader specifies the exact amount of output tokens they want to receive,
     *      and the maximum amount of input tokens they are willing to spend.
     * @param amountOut The exact amount of output tokens the trader wants to receive.
     * @param amountInMax The maximum amount of input tokens the trader is willing to spend.
     * @param path The swap path as an array of token addresses. The first address is the input token, and the last is the output token.
     * @param to The address that will receive the output tokens.
     * @param deadline The latest time the transaction is valid. Must be executed before this time.
     * @return amounts The amounts of tokens required at each step in the path to achieve the desired output.
     */
    function swapTokensForExactTokens(
        uint amountOut,
        uint amountInMax,
        address[] calldata path,
        address to,
        uint deadline
    )
        external
        virtual
        override
        ensure(deadline)
        returns (uint[] memory amounts)
    {
        // Calculate the amount of input tokens required at each step to get the exact output amount
        amounts = UniswapV2Library.getAmountsIn(factory, amountOut, path);

        // Ensure the required input amount does not exceed the maximum amount specified by the trader
        require(
            amounts[0] <= amountInMax,
            "UniswapV2Router: EXCESSIVE_INPUT_AMOUNT"
        );

        // Transfer the input tokens from the trader to the first pair contract in the path
        TransferHelper.safeTransferFrom(
            path[0],
            msg.sender,
            UniswapV2Library.pairFor(factory, path[0], path[1]),
            amounts[0]
        );

        // Execute the token swaps along the specified path
        _swap(amounts, path, to);
    }

    /**
     * @dev Swaps an exact amount of ETH for as many output tokens as possible, following a specified path.
     *      Ensures the output is at least the minimum amount expected by the trader, or the transaction reverts.
     * @param amountOutMin The minimum amount of output tokens the trader is willing to accept.
     * @param path The swap path as an array of token addresses. The first address must be WETH (wrapped ETH), and the last is the output token.
     * @param to The address that will receive the output tokens.
     * @param deadline The latest time the transaction is valid. Must be executed before this time.
     * @return amounts The amounts of tokens received at each step in the path.
     */
    function swapExactETHForTokens(
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    )
        external
        payable
        virtual
        override
        ensure(deadline)
        returns (uint[] memory amounts)
    {
        // Ensure the first token in the path is WETH (wrapped ETH)
        require(path[0] == WETH, "UniswapV2Router: INVALID_PATH");

        // Calculate the amount of output tokens at each step in the swap path
        amounts = UniswapV2Library.getAmountsOut(factory, msg.value, path);

        // Ensure the final output amount is at least the minimum specified by the trader
        require(
            amounts[amounts.length - 1] >= amountOutMin,
            "UniswapV2Router: INSUFFICIENT_OUTPUT_AMOUNT"
        );

        // Wrap the sent ETH into WETH
        IWETH(WETH).deposit{value: amounts[0]}();

        // Transfer the WETH to the first pair contract in the path
        assert(
            IWETH(WETH).transfer(
                UniswapV2Library.pairFor(factory, path[0], path[1]),
                amounts[0]
            )
        );

        // Execute the token swaps along the specified path
        _swap(amounts, path, to);
    }

    /**
     * @dev Swaps tokens for an exact amount of ETH, following a specified path.
     *      Ensures the amount of input tokens does not exceed the maximum specified by the trader, or the transaction reverts.
     * @param amountOut The exact amount of ETH the trader wants to receive.
     * @param amountInMax The maximum amount of input tokens the trader is willing to spend.
     * @param path The swap path as an array of token addresses. The last address must be WETH (wrapped ETH), and the first is the input token.
     * @param to The address that will receive the ETH.
     * @param deadline The latest time the transaction is valid. Must be executed before this time.
     * @return amounts The amounts of tokens required at each step in the path to achieve the desired ETH output.
     */
    function swapTokensForExactETH(
        uint amountOut,
        uint amountInMax,
        address[] calldata path,
        address to,
        uint deadline
    )
        external
        virtual
        override
        ensure(deadline)
        returns (uint[] memory amounts)
    {
        // Ensure the last token in the path is WETH (wrapped ETH)
        require(path[path.length - 1] == WETH, "UniswapV2Router: INVALID_PATH");

        // Calculate the amount of input tokens required to get the exact amount of ETH
        amounts = UniswapV2Library.getAmountsIn(factory, amountOut, path);

        // Ensure the required input amount does not exceed the maximum amount specified by the trader
        require(
            amounts[0] <= amountInMax,
            "UniswapV2Router: EXCESSIVE_INPUT_AMOUNT"
        );

        // Transfer the input tokens from the trader to the first pair contract in the path
        TransferHelper.safeTransferFrom(
            path[0],
            msg.sender,
            UniswapV2Library.pairFor(factory, path[0], path[1]),
            amounts[0]
        );

        // Execute the token swaps along the specified path, with the final ETH being sent to this contract
        _swap(amounts, path, address(this));

        // Withdraw the ETH from WETH
        IWETH(WETH).withdraw(amounts[amounts.length - 1]);

        // Transfer the ETH to the trader
        TransferHelper.safeTransferETH(to, amounts[amounts.length - 1]);
    }

    /**
     * @dev Swaps an exact amount of input tokens for as much ETH as possible, following a specified path.
     *      Ensures the amount of output ETH is at least the minimum amount specified by the trader, or the transaction reverts.
     * @param amountIn The exact amount of input tokens the trader wants to spend.
     * @param amountOutMin The minimum amount of ETH the trader is willing to receive.
     * @param path The swap path as an array of token addresses. The last address must be WETH (wrapped ETH), and the first is the input token.
     * @param to The address that will receive the ETH.
     * @param deadline The latest time the transaction is valid. Must be executed before this time.
     * @return amounts The amounts of tokens and ETH at each step in the path.
     */
    function swapExactTokensForETH(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    )
        external
        virtual
        override
        ensure(deadline)
        returns (uint[] memory amounts)
    {
        // Ensure the last token in the path is WETH (wrapped ETH)
        require(path[path.length - 1] == WETH, "UniswapV2Router: INVALID_PATH");

        // Calculate the amount of ETH that will be received for the given input amount
        amounts = UniswapV2Library.getAmountsOut(factory, amountIn, path);

        // Ensure the received ETH amount is at least the minimum specified by the trader
        require(
            amounts[amounts.length - 1] >= amountOutMin,
            "UniswapV2Router: INSUFFICIENT_OUTPUT_AMOUNT"
        );

        // Transfer the input tokens from the trader to the first pair contract in the path
        TransferHelper.safeTransferFrom(
            path[0],
            msg.sender,
            UniswapV2Library.pairFor(factory, path[0], path[1]),
            amounts[0]
        );

        // Execute the token swaps along the specified path, with the final ETH being sent to this contract
        _swap(amounts, path, address(this));

        // Withdraw the ETH from WETH
        IWETH(WETH).withdraw(amounts[amounts.length - 1]);

        // Transfer the ETH to the trader
        TransferHelper.safeTransferETH(to, amounts[amounts.length - 1]);
    }

    /**
     * @dev Swaps ETH for an exact amount of tokens, following a specified path.
     *      Ensures the amount of ETH sent does not exceed the amount required for the swap, and refunds any excess ETH.
     * @param amountOut The exact amount of tokens the trader wants to receive.
     * @param path The swap path as an array of token addresses. The first address must be WETH (wrapped ETH), and the last is the output token.
     * @param to The address that will receive the tokens.
     * @param deadline The latest time the transaction is valid. Must be executed before this time.
     * @return amounts The amounts of ETH used and tokens received at each step in the path.
     */
    function swapETHForExactTokens(
        uint amountOut,
        address[] calldata path,
        address to,
        uint deadline
    )
        external
        payable
        virtual
        override
        ensure(deadline)
        returns (uint[] memory amounts)
    {
        // Ensure the first token in the path is WETH (wrapped ETH)
        require(path[0] == WETH, "UniswapV2Router: INVALID_PATH");

        // Calculate the amount of ETH required to get the exact amount of tokens
        amounts = UniswapV2Library.getAmountsIn(factory, amountOut, path);

        // Ensure the amount of ETH sent does not exceed the amount required for the swap
        require(
            amounts[0] <= msg.value,
            "UniswapV2Router: EXCESSIVE_INPUT_AMOUNT"
        );

        // Deposit the ETH into WETH (wrapped ETH) contract
        IWETH(WETH).deposit{value: amounts[0]}();

        // Transfer the WETH to the first pair contract in the path
        assert(
            IWETH(WETH).transfer(
                UniswapV2Library.pairFor(factory, path[0], path[1]),
                amounts[0]
            )
        );

        // Execute the token swaps along the specified path, sending the final tokens to the specified address
        _swap(amounts, path, to);

        // Refund any excess ETH sent by the trader
        if (msg.value > amounts[0]) {
            TransferHelper.safeTransferETH(msg.sender, msg.value - amounts[0]);
        }
    }

    // **** SWAP (supporting fee-on-transfer tokens) ****
    // requires the initial amount to have already been sent to the first pair
    /**
     * @dev Internal function to swap tokens that may have transfer or storage fees.
     *      This function handles tokens that deduct fees on transfer by calculating the amounts dynamically
     *      after the initial transfer, rather than relying on pre-computed amounts.
     * @param path The swap path as an array of token addresses. Each pair of addresses represents a swap step.
     * @param _to The address that will receive the final output tokens.
     */
    function _swapSupportingFeeOnTransferTokens(
        address[] memory path,
        address _to
    ) internal virtual {
        // Iterate through the path, handling each pair of tokens
        for (uint i; i < path.length - 1; i++) {
            // Get the addresses for the current pair
            (address input, address output) = (path[i], path[i + 1]);

            // Sort tokens to determine the correct order for the pair
            (address token0, ) = UniswapV2Library.sortTokens(input, output);

            // Get the pair contract for the current token pair
            IUniswapV2Pair pair = IUniswapV2Pair(
                UniswapV2Library.pairFor(factory, input, output)
            );

            uint amountInput;
            uint amountOutput;
            {
                // Scope to avoid stack too deep errors
                // Get the current reserves of the pair
                (uint reserve0, uint reserve1, ) = pair.getReserves();

                // Determine which reserve corresponds to the input and output tokens
                (uint reserveInput, uint reserveOutput) = input == token0
                    ? (reserve0, reserve1)
                    : (reserve1, reserve0);

                // Calculate the amount of input tokens transferred
                amountInput = IERC20(input).balanceOf(address(pair)).sub(
                    reserveInput
                );
                // Calculate the expected output amount for the transferred input tokens
                amountOutput = UniswapV2Library.getAmountOut(
                    amountInput,
                    reserveInput,
                    reserveOutput
                );
            }

            // Determine the amount of tokens to output based on the token order
            (uint amount0Out, uint amount1Out) = input == token0
                ? (uint(0), amountOutput)
                : (amountOutput, uint(0));

            // Determine the address for the next swap or the final recipient
            address to = i < path.length - 2
                ? UniswapV2Library.pairFor(factory, output, path[i + 2])
                : _to;

            // Execute the swap with the calculated amounts
            pair.swap(amount0Out, amount1Out, to, new bytes(0));
        }
    }

    // These are the same variants used for normal tokens, but they call _swapSupportingFeeOnTransferTokens instead.
    // ***** START - VARIATIONS OF _swapSupportingFeeOnTransferTokens *****
    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external virtual override ensure(deadline) {
        TransferHelper.safeTransferFrom(
            path[0],
            msg.sender,
            UniswapV2Library.pairFor(factory, path[0], path[1]),
            amountIn
        );
        uint balanceBefore = IERC20(path[path.length - 1]).balanceOf(to);
        _swapSupportingFeeOnTransferTokens(path, to);
        require(
            IERC20(path[path.length - 1]).balanceOf(to).sub(balanceBefore) >=
                amountOutMin,
            "UniswapV2Router: INSUFFICIENT_OUTPUT_AMOUNT"
        );
    }
    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external payable virtual override ensure(deadline) {
        require(path[0] == WETH, "UniswapV2Router: INVALID_PATH");
        uint amountIn = msg.value;
        IWETH(WETH).deposit{value: amountIn}();
        assert(
            IWETH(WETH).transfer(
                UniswapV2Library.pairFor(factory, path[0], path[1]),
                amountIn
            )
        );
        uint balanceBefore = IERC20(path[path.length - 1]).balanceOf(to);
        _swapSupportingFeeOnTransferTokens(path, to);
        require(
            IERC20(path[path.length - 1]).balanceOf(to).sub(balanceBefore) >=
                amountOutMin,
            "UniswapV2Router: INSUFFICIENT_OUTPUT_AMOUNT"
        );
    }
    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external virtual override ensure(deadline) {
        require(path[path.length - 1] == WETH, "UniswapV2Router: INVALID_PATH");
        TransferHelper.safeTransferFrom(
            path[0],
            msg.sender,
            UniswapV2Library.pairFor(factory, path[0], path[1]),
            amountIn
        );
        _swapSupportingFeeOnTransferTokens(path, address(this));
        uint amountOut = IERC20(WETH).balanceOf(address(this));
        require(
            amountOut >= amountOutMin,
            "UniswapV2Router: INSUFFICIENT_OUTPUT_AMOUNT"
        );
        IWETH(WETH).withdraw(amountOut);
        TransferHelper.safeTransferETH(to, amountOut);
    }
    // ***** END - VARIATIONS OF _swapSupportingFeeOnTransferTokens *****

    // **** LIBRARY FUNCTIONS ****

    // *** These functions are just proxies that call the functions from UniswapV2Library 
    function quote(
        uint amountA,
        uint reserveA,
        uint reserveB
    ) public pure virtual override returns (uint amountB) {
        return UniswapV2Library.quote(amountA, reserveA, reserveB);
    }

    function getAmountOut(
        uint amountIn,
        uint reserveIn,
        uint reserveOut
    ) public pure virtual override returns (uint amountOut) {
        return UniswapV2Library.getAmountOut(amountIn, reserveIn, reserveOut);
    }

    function getAmountIn(
        uint amountOut,
        uint reserveIn,
        uint reserveOut
    ) public pure virtual override returns (uint amountIn) {
        return UniswapV2Library.getAmountIn(amountOut, reserveIn, reserveOut);
    }

    function getAmountsOut(
        uint amountIn,
        address[] memory path
    ) public view virtual override returns (uint[] memory amounts) {
        return UniswapV2Library.getAmountsOut(factory, amountIn, path);
    }

    function getAmountsIn(
        uint amountOut,
        address[] memory path
    ) public view virtual override returns (uint[] memory amounts) {
        return UniswapV2Library.getAmountsIn(factory, amountOut, path);
    }
}