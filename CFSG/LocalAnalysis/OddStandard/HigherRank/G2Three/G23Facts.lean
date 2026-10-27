module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsL
public import CFSG.LocalAnalysis.OddStandard.HigherRank.Leaves
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open CFSG.OddStandard.HigherRank.G2Three.Sec1

@[expose] def G23Facts : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], HRG23 Q →
    ∀ P : Sylow 2 (MulAut Q), ∃ fr : Frame (MulAut Q),
      fr.Sσ = (P : Subgroup (MulAut Q)) ∧ fr.Facts (innerAut Q)

end CFSG.OddStandard.HigherRank.G2Three
