module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Three

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section OrderNine

theorem exists_hasNF_zero_of_nine
    {K : Type} [Field K] [Finite K]
    {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 9) (hEI : E ⊓ inner ↥(adjointGroup Tag.D4 K) = ⊥) :
    ∃ e ∈ E, e ≠ 1 ∧ ∃ σ : K ≃+* K, σ ^ 3 = 1 ∧ σ ≠ 1 ∧ HasNF e 0 σ := by
  classical
  obtain ⟨x₁, hx₁E, hx₁1⟩ : ∃ x ∈ E, x ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 h
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hx₁3 : x₁ ^ 3 = 1 := hE.2 x₁ hx₁E
  obtain ⟨x₂, hx₂E, hx₂1⟩ : ∃ x ∈ E, x ∉ Subgroup.zpowers x₁ := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (fun x hx => h x hx : E ≤ Subgroup.zpowers x₁)
    rw [hcard, Nat.card_zpowers] at h1
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx₁3)
    omega
  obtain ⟨g₁, a₁, σ₁, ε₁, hε₁, -, h₁⟩ :=
    CFSG.HardMathSupport.Lang.D4Three.exists_cube_normal_form_sigma x₁ hx₁3
  obtain ⟨g₂, a₂, σ₂, ε₂, hε₂, -, h₂⟩ :=
    CFSG.HardMathSupport.Lang.D4Three.exists_cube_normal_form_sigma x₂ (hE.2 x₂ hx₂E)
  have n₁ : HasNF x₁ ε₁ σ₁ := ⟨g₁, a₁, h₁⟩
  have n₂ : HasNF x₂ ε₂ σ₂ := ⟨g₂, a₂, h₂⟩
  obtain ⟨e, heE, he1, σe, nE⟩ : ∃ e ∈ E, e ≠ 1 ∧ ∃ σ, HasNF e 0 σ := by
    by_cases h0 : ε₁ = 0
    · exact ⟨x₁, hx₁E, hx₁1, σ₁, h0 ▸ n₁⟩
    · obtain ⟨w, hw, σ', hw'⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.exists_hasNF_zero_mul
          n₂ n₁ hε₂ hε₁ h0
      refine ⟨x₂ * w, mul_mem hx₂E (Subgroup.zpowers_le.2 hx₁E hw), ?_, σ', hw'⟩
      intro h
      apply hx₂1
      rw [eq_inv_of_mul_eq_one_left h]
      exact Subgroup.inv_mem _ hw
  refine ⟨e, heE, he1, σe, ?_, ?_, nE⟩
  ·
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.sigma_cube_of_hasNF nE
      (hE.2 e heE)
  ·
    intro hσe
    apply he1
    have hin : e ∈ inner ↥(adjointGroup Tag.D4 K) :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.mem_inner_of_hasNF_zero_one
        (hσe ▸ nE) (hE.2 e heE)
    have hbot : e ∈ (⊥ : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))) := by
      rw [← hEI]
      exact ⟨heE, hin⟩
    simpa using hbot

end OrderNine

end CFSG.LieType.SeitzGeneration.ExcWideThree
