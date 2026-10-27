module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

section
variable [Finite G] {t : G} {L S T₂ : Subgroup G} {x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G}

theorem fzJt_mul_invol {v w : G} (hv2 : v ^ 2 = 1) (hw2 : w ^ 2 = 1) (hvw : v ≠ w)
    (hc : v * w = w * v) :
    (v * w) ^ 2 = 1 ∧ v * w ≠ 1 := by
  refine ⟨?_, ?_⟩
  · rw [(show Commute v w from hc).mul_pow, hv2, hw2, one_mul]
  · intro h; apply hvw
    have hw : w⁻¹ = w := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hw2]
    calc v = (v * w) * w⁻¹ := by group
      _ = w := by rw [h, one_mul, hw]

theorem fzJt_holds [IsSimpleGroup G] (hGT : FzInvolT) (hF4 : FzJtWitness)
    (hset : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂) {u : G} (hu : u ∈ T₂)
    (hu2 : u ^ 2 = (x₁ * x₂) ^ 2) (hR3 : u ∉ fzR3 t x₁ x₂ a₃₂)
    (h36 : ¬ (u ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ ∧
      ¬ ∃ r ∈ fzR3 t x₁ x₂ a₃₂, ∃ ε ∈ fourGrp x₁ x₂, u = r * ε)) : FzJt t T₂ u := by
  obtain ⟨v, hv, w, hw, hv2, hw2, hv1, hw1, hvw, hc, hvZ, hwZ, hvwZ⟩ :=
    hF4 G t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hset u hu hu2 hR3 h36
  have hp := fzJt_mul_invol hv2 hw2 hvw hc
  have gt := hGT G t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hset
  exact ⟨v, hv, w, hw, hv2, hw2, hvw, hc, gt v hv.1 hv2 hv1 hvZ, gt w hw.1 hw2 hw1 hwZ,
    gt _ (mul_mem hv.1 hw.1) hp.1 hp.2 hvwZ⟩

theorem fzJt_fails [IsSimpleGroup G] (hGZ : FzInvolZ) (hF3 : FzCalZPairR3)
    (hset : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂) {a : G}
    (ha : a ∈ fzR3 t x₁ x₂ a₃₂) (ha2 : a ^ 2 = (x₁ * x₂) ^ 2) : ¬ FzJt t T₂ a := by
  rintro ⟨v, hv, w, hw, hv2, hw2, hvw, hc, htv, htw, htvw⟩
  have gz := hGZ G t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hset
  have hne : ∀ e : G, IsConj t e → e ≠ 1 := fun e he h1 => by
    rw [h1] at he
    have h1t : t = 1 := isConj_one_right.mp he.symm
    have := hset.ctx.hyp.ord_t; rw [h1t, orderOf_one] at this; exact absurd this (by norm_num)
  rcases hF3 G t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hset a ha ha2 v hv w hw hv2 hw2
      (hne v htv) (hne w htw) hvw hc with h | h | h
  · exact gz v h htv
  · exact gz w h htw
  · exact gz _ h htvw

end

end CFSG.OddStandard.SmallF3.FritzII
