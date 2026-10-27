module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Covers
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Perm

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

structure Bal3ThreeInputs : Prop where
  single : Bal3ThreeSingleRed
  schreier : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog

structure Bal3ThreeCoverInputs : Prop where
  covers : Bal3ThreeCovers
  center : Bal3ThreeCenter
  small : Bal3SmallCards
  onan : Bal3OnanComm
  sl3 : Bal3ThreeSL3
  schreier : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog

theorem Bal3ThreeCoverInputs.toInputs (h : Bal3ThreeCoverInputs) : Bal3ThreeInputs :=
  ⟨bal3ThreeSingleRed_of_covers h.covers h.center h.small h.onan h.sl3, h.schreier⟩

theorem bal3KFacts_of_inputs (hK : SchurMultiplierRankFact) (h3 : Bal3ThreeInputs)
    (h294 : Input29_4Rank3) : Bal3KFacts :=
  ⟨kFactLemma212_of_inputs_red hK h3.single,
    kFactLemma213_of_inputs h294 (bal3NoPermute_of_schreier h3.schreier)⟩

theorem bal3KFacts_of_cover_inputs (hK : SchurMultiplierRankFact) (h3 : Bal3ThreeCoverInputs)
    (h294 : Input29_4Rank3) : Bal3KFacts :=
  bal3KFacts_of_inputs hK h3.toInputs h294

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
