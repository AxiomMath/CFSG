module

public import CFSG.ClassicalInvolution.Balance.PassTwoP1
public import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

theorem stage2_final [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2)
    (hf : 0 < f) (h9 : p ^ f ≠ 9) (h0 : ModelClauseZero)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) {F : Type*} [Field F] {S : Set (Subgroup G)}
    (Fr : WeakToralFrame F Ω E S) (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationAt E a) :
    Stage2 Ω {x | x ∈ E ∧ x ≠ 1 ∧ FrameMeetsAt Ω E S x} :=
  stage2_of_localLieSystems hnab hp2 hf h9 h0 fundamentalWholeA1 hΩ hsingle hIH Fr h16 hGen hlay

end CFSG.ClassicalInvolution.Balance
