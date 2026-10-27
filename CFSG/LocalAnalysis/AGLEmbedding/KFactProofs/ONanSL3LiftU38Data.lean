module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Gen

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField.Eight

open CFSG.AGLEmbedding.ChevOuter.GF64 CFSG.AGLEmbedding.ChevOuter.U38

@[expose] def z8Gen : GenData where
  gens := #[#[ofNat' 1, ofNat' 1, ofNat' 1, ofNat' 1, ofNat' 8, ofNat' 9, ofNat' 1, ofNat' 9,
      ofNat' 8], #[ofNat' 22, ofNat' 0, ofNat' 0, ofNat' 0, ofNat' 20, ofNat' 0, ofNat' 0,
      ofNat' 0, ofNat' 1]]
  v0 := #[0, 1, 1]
  words := [[0], [2, 0, 0, 2, 0, 3, 1, 1, 3],
    [2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 1, 3, 1, 3, 1, 3, 1, 3, 3],
    [2, 2, 0, 2, 2, 0, 0, 2, 0, 2, 0, 2, 1, 3, 1, 3, 1, 3, 3, 1, 3],
    [2, 2, 2, 2, 0, 0, 2, 2, 0, 2, 0, 3, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3],
    [2, 2, 0, 0, 0, 2, 0, 2, 0, 2, 0, 2, 1, 3, 1, 1, 1, 3, 3, 3, 3, 3]]
  fuel1 := 33000
  fuel2 := 600

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField.Eight
