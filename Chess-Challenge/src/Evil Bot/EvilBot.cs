using ChessChallenge.API;
using System;
using System.Linq;

public class EvilBot : IChessBot
{
    Move bestRootMove;

    public Move Think(Board board, Timer timer)
    {
        int searchDepth = 0;

        int Search(int depth, int alpha, int beta, int material)
        {

            // Quiescence & eval
            if (depth <= 0)
                alpha = Math.Max(alpha, material * 200 + board.GetLegalMoves().Length);  //eval = material + mobility
            // no beta cutoff check here, it will be done latter


            foreach (Move move in board.GetLegalMoves(depth <= 0)
                         .OrderByDescending(move => (move == bestRootMove ? 1 : 0, move.CapturePieceType, 0 - move.MovePieceType)))
            {
                if (alpha >= beta)
                    break;

                board.MakeMove(move);

                int score =
                    board.IsDraw() ? 0 :
                    board.IsInCheckmate() ? 30000 :
                    -Search(depth - 1, -beta, -alpha, -material - move.CapturePieceType - move.PromotionPieceType);

                if (score > alpha)
                {
                    alpha = score;
                    if (depth == searchDepth)
                        bestRootMove = move;
                }

                // Check timer now: after updating best root move (so no illegal move), but before UndoMove (which takes some time)
                if (timer.MillisecondsElapsedThisTurn * 30 >= timer.MillisecondsRemaining)
                    depth /= 0;

                board.UndoMove(move);
            }

            return alpha;
        }

        try
        {
            for (; ; )
                Search(++searchDepth, -40000, 40000, 0);
        }
        catch { }

        return bestRootMove;
    }
}