module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtHolds
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisTools
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzInputs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

section
variable [Finite G] {t : G} {L S T₂ : Subgroup G} {x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G}

theorem fzR3_trichotomy (hset : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂) {a : G}
    (ha : a ∈ fzR3 t x₁ x₂ a₃₂) : a = 1 ∨ a = (x₁ * x₂) ^ 2 ∨ a ^ 2 = (x₁ * x₂) ^ 2 := by
  have hq3 := hset.shape.quat₃
  have hsq : ((x₁ * x₂)⁻¹ * t) ^ 2 = (x₁ * x₂) ^ 2 := fz_sq_a31 hset.ctx.toCtx0
  have hr : a ∈ (q8Hom hq3).range := by rw [fz_q8_range hq3]; exact ha
  obtain ⟨q, rfl⟩ := hr
  have ha2 : q8Hom hq3 (QuaternionGroup.a 2) = ((x₁ * x₂)⁻¹ * t) ^ 2 := by
    change zmod4Pow ((x₁ * x₂)⁻¹ * t) (2 : ZMod 4) = ((x₁ * x₂)⁻¹ * t) ^ 2
    rw [zmod4Pow, show (2 : ZMod 4).val = 2 from rfl]
  rcases (by decide : ∀ q : QuaternionGroup 2, q = 1 ∨ q = QuaternionGroup.a 2 ∨
      q ^ 2 = QuaternionGroup.a 2) q with h | h | h
  · left; rw [h, map_one]
  · right; left; rw [h, ha2, hsq]
  · right; right; rw [← map_pow, h, ha2, hsq]

theorem fritzFusionInput_of_labels (hGT : FzInvolT) (hGZ : FzInvolZ) (hSyl : FzSylR3)
    (hF2 : FzJFailsR3) (hF3 : FzCalZPairR3) (hF4 : FzJtWitness) : FritzFusionInput := by
  intro G _ _ _ t L S x₁ x₂ lam rho tau T₂ a₁₂ a₂₂ a₃₂ hctx hK hT hS hsh a ha g hg hgT
  have hset : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ := ⟨hctx, hK, hT, hS, hsh⟩
  have hg_z : g * (x₁ * x₂) ^ 2 * g⁻¹ = (x₁ * x₂) ^ 2 := by
    rw [mem_centralizer_singleton_iff.mp hg]; group
  have hz3R3 : (x₁ * x₂) ^ 2 ∈ fzR3 t x₁ x₂ a₃₂ := by
    rw [← fz_sq_a31 hctx.toCtx0]; exact Subgroup.pow_mem _ (subset_closure (by simp)) 2
  rcases fzR3_trichotomy hset ha with rfl | rfl | ha2
  · simpa using ha
  · rw [hg_z]; exact hz3R3
  by_contra hu
  set u := g * a * g⁻¹ with hu_def
  have hu2 : u ^ 2 = (x₁ * x₂) ^ 2 := by
    rw [hu_def, show (g * a * g⁻¹) ^ 2 = g * a ^ 2 * g⁻¹ by rw [pow_two, pow_two]; group, ha2, hg_z]
  have hv := hSyl G t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hset a ha ha2
  obtain ⟨k, hk, hC⟩ := CFSG.ComponentClassification.GHarris.exists_conj_extremal
    hS.1 hv (h := g⁻¹) (u := u) (by rw [inv_inv])
  by_cases h36 : u ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ ∧
      ¬ ∃ r ∈ fzR3 t x₁ x₂ a₃₂, ∃ ε ∈ fourGrp x₁ x₂, u = r * ε
  · exact hF2 G t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hset a ha ha2
      (fzl_J_conj hk hC (fzl_J_holds hset h36.1 hu2 h36.2))
  · exact fzJt_fails hGZ hF3 hset ha ha2
      (fzJt_conj hk hC (fzJt_holds hGT hF4 hset hgT hu2 hu h36))

end

end CFSG.OddStandard.SmallF3.FritzII
