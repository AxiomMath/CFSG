module

public import CFSG.GH74.GLS.Stage4.Q9.ThetaProps
public import CFSG.GH74.GLS.Stage4.Q9.ThetaAbstract
public import CFSG.GH74.GLS.Stage4.Q9.Transfer

public section

open scoped BigOperators Classical

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

theorem model_theta_data :
    ModelThetaData := by
  obtain ⟨α, β, hαf, hβf, hα, hβ, hθv, hθθ, hθ1, hθ0, hα81, hβ80, hθf⟩ :=
    theta_data_of_irr mkC mkC_surjective alphaHat_mem betaHat_mem
      (fun a a' h => alphaHat_eq_of_mkC_eq h) (fun a a' h => betaHat_eq_of_mkC_eq h)
      alphaHat_norm betaHat_norm alphaHat_one betaHat_one
  have hθ : ∀ c : ↥Chat, ((1 : Cq → ℂ) - α + β) (mkC c) = thetaHat c := by
    intro c
    have h := congrFun hθf c
    rw [thetaHat_apply_eq]
    exact h
  refine ⟨(1 : Cq → ℂ) - α + β, hθv, ?_, hθθ, hθ1, hθ0, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := mkC_surjective x
    rw [hθ]
    exact thetaHat_support c hx
  · show ((1 : Cq → ℂ) - α + β) (mkC (inl1 minusOne)) = 0
    rw [hθ]
    exact thetaHat_inl1_minusOne
  · have hJc : ∀ (g x : Cq), x ∈ (Finset.univ.filter fun x : Cq => orderOf x = 2 ∧ x ≠ zq) →
        g * x * g⁻¹ ∈ (Finset.univ.filter fun x : Cq => orderOf x = 2 ∧ x ≠ zq) := by
      intro g x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · have h : orderOf (g * x * g⁻¹) = orderOf x := by
          simpa using (MulAut.conj g).orderOf_eq x
        rw [h]
        exact hx.2.1
      · intro h
        apply hx.2.2
        have hc : g⁻¹ * zq * g = zq := by
          have h1 := Subgroup.mem_center_iff.mp zq_mem_center g⁻¹
          calc g⁻¹ * zq * g = zq * g⁻¹ * g := by rw [h1]
            _ = zq := by group
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g⁻¹ * zq * g := by rw [h]
          _ = zq := hc
    have hJv : ∀ x ∈ (Finset.univ.filter fun x : Cq => orderOf x = 2 ∧ x ≠ zq),
        α x = 1 ∧ β x = 0 := by
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨c, rfl⟩ := mkC_surjective x
      refine ⟨?_, ?_⟩
      · have := alphaHat_J c hx.2.1 hx.2.2
        rw [← hαf] at this
        exact this
      · have := betaHat_J c hx.2.1 hx.2.2
        rw [← hβf] at this
        exact this
    have hcard : (Finset.univ.filter fun x : Cq => orderOf x = 2 ∧ x ≠ zq).card = 6642 := by
      rw [← card_J, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact kappa_class_sum_eval hα hβ _ hJc hJv hα81 hβ80 hcard

theorem model_counts
    : ModelCounts := ⟨card_pSet_two, card_pSet_three, card_pSet_five⟩

end CFSG.GH74.GLS.Stage4.Q9
