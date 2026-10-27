module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp62Local

open CFSG.KGroups.Sp6 CFSG.Quasithin.G2U

@[expose] def cAlt0 : List ℕ := [1, 6, 2, 8, 38, 50]

@[expose] def cAlt1 : List ℕ := [1, 4, 6, 8, 50, 20]

@[expose] def cAlt2 : List ℕ := [1, 54, 20, 8, 4, 18]

@[expose] def cAlt3 : List ℕ := [1, 48, 16, 8, 20, 38]

@[expose] def gensAlt : List (List ℕ) := [cAlt0, cAlt1, cAlt2, cAlt3]

@[expose] def sqB (x : List ℕ) : Bool := mulC x x == oneC

@[expose] def chkAlt : Bool := tabCheck gensAlt 360 fun _ => true

@[expose] def relAlt : Bool :=
  (List.range 4).all fun i => cubeB (gensAlt.getD i []) &&
    (List.range 4).all fun j =>
      decide (i = j) || sqB (mulC (gensAlt.getD i []) (gensAlt.getD j []))

@[expose] def commAlt : Bool := gensAlt.all (commB cW0)

@[expose] def outW : Bool := !(inTab (tabOf gensWD 51840) cAlt0)

end CFSG.AGLEmbedding.KFactProofs.Sp62Local
