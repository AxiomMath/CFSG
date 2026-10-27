module

public import CFSG.LocalAnalysis.EvenBN.G2.QFacts
public import CFSG.LocalAnalysis.EvenBN.G2.LocalQFourFacts
public import CFSG.LocalAnalysis.EvenBN.G2.LocalQFourFive
public import CFSG.LocalAnalysis.EvenBN.G2.LocalQFourSix

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section QFactsFour

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem qFacts_four (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hK4 : Nat.card K = 4) (hcat : SeitzReduction.LinearPilot.SLmCatalogueClausesAt 3) :
    h.QFacts d :=
  ⟨h.doublingFacts_four d hK hK4 hcat, Or.inr ⟨hK4,
    fun {_} hPB hP hXP => h.le_centralizer_yamadaU₁_of_le_yamadaB d hK hK4 hcat hPB hP hXP,
    fun {_} hV {_} hEV hEe hEc hEcard =>
      h.exists_complement_of_isSylowOf_yamadaB d hK hK4 hcat hV hEV hEe hEc hEcard⟩⟩

end QFactsFour

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
