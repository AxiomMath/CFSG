module

public import CFSG.ClassicalInvolution.Asc77.AscT7Z6
public import CFSG.ClassicalInvolution.Q3.Q3T7S23A01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair diagConj2)
open scoped commutatorElement MatrixGroups

theorem admissible_psl4_three : StatedLieAdmissible .PSL 4 3 1 :=
  ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩

section Layer


variable {G : Type} [Group G]

theorem finite_U3 :
    Finite (modelUniv .PSL 4 3 1 Fact.out).K :=
  ModelFacts.finite_modelUniv (by norm_num) Fact.out (by trivial) admissible_psl4_three

theorem injOn_fund_psl3 {Φ : Set (Subgroup G)} (P : T7Z.PSLLayer 3 1 Φ) {L : Subgroup G}
    {R : Subgroup (modelUniv .PSL 4 3 1 Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Fact.out).D)
    (hLR : L = R.map P.ψ) (eL : Nonempty (↥L ≃* SL(2, GaloisField 3 1))) :
    ∀ x ∈ R, P.ψ x = 1 → x = 1 := by
  obtain ⟨e₁⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .PSL)
    (n := 4) (by trivial) admissible_psl4_three (by decide) (by decide) hR
  obtain ⟨e₂⟩ := eL
  have := finite_U3
  intro x hx hψ
  refine T7Z.eq_one_of_map_eq_one_of_card_eq P.ψ ?_ hx hψ
  rw [← hLR]
  exact (Nat.card_congr e₂.toEquiv).trans (Nat.card_congr e₁.toEquiv).symm

end Layer


section Data

variable {G : Type} [Group G] [Finite G]

structure D4YData (Ω : Set (Subgroup G)) (K K' : Subgroup G) (u e g : G) (K₁ : Subgroup G)
    (z₁ : G) : Prop where
  mem : K₁ ∈ Ω
  inv : IsUniqueInvolution K₁ z₁
  le : K₁ ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω u
  pair : ∃ W', LinearBlockStandardPair (GaloisField 3 1) W' K₁ (conjSub g K)
  gen : Q3T8.Asc77.ExactLayer.exactLayer Ω u ≤ conjSub g K' ⊔ K₁ ⊔ conjSub g K
  comm : z₁ * e = e * z₁
  chart : ∃ θ : SL(2, GaloisField 3 1) →* G, θ.range = conjSub g K ∧
    ∀ s, z₁ * θ s * z₁⁻¹ = θ (diagConj2 (-1) 1 s)
  chart' : ∃ θ : SL(2, GaloisField 3 1) →* G, θ.range = conjSub g K' ∧
    ∀ s, z₁ * θ s * z₁⁻¹ = θ (diagConj2 (-1) 1 s)
  fix : ∀ a : G, a * u = u * a → (∀ x ∈ conjSub g K, a * x = x * a) →
    (∀ x ∈ conjSub g K', a * x = x * a) → a * z₁ = z₁ * a

end Data


@[expose] def OddCoreLayer23Plus3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23b Ω K K' W z u e g →
      (alphaOf (Subgroup.closure {u, z}) = ⊥ ∧
        Q3T8.Asc77.ExactLayer.exactLayer Ω e ⊔ Q3T8.Asc77.ExactLayer.exactLayer Ω u = ⊤) →
      Q3T8.Asc77.LayerOrthType Ω e 6 (piSign 3 1) →
      Q3T8.Asc77.LayerOrthType Ω u 6 (!piSign 3 1) → ExactMembers Ω →
      CFSG.Open.classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω e) = ⊥ →
        CFSG.Open.classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) = ⊥

end CFSG.ClassicalInvolution.Q3.Q3T7S23
