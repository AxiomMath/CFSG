module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraphAll
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenClique

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem thompsonGraphAll (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G))
    (hP : PartIHyp p f Ω) {K : Subgroup G} (hK : K ∈ Ω) (hne : dComp Ω K ≠ dstarComp Ω K)
    {W : Subgroup G} (hW : W ∈ WSet Ω) : ¬ DbarConnected Ω W :=
  Thompson.not_connected_of_dComp_ne hP.1 hP.2.1 hP.2.2.1 hP.2.2.2 hW (thompsonKey G Ω hP W hW)
    hK hne

theorem l7_17_proved : L7_17 p f := by
  intro G _ _ Ω hP K hK
  by_cases h : dComp Ω K = dstarComp Ω K
  · exact Or.inl h
  · exact Or.inr fun W hW => l7_10_proved G Ω hP W hW (thompsonGraphAll G Ω hP hK h hW)

end CFSG.ClassicalInvolution.Asc77
