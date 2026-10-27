module

public import CFSG.GH74.GLS.IVK.Lifted.Lem52
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Lem510

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

theorem ivk_SR_abelian_of_II4 (h44 : II4_44) (h2A7 : II4_2A7) :
    CFSG.GH74.GLS.Stage1.Thm3.Sec6.IVK_SR_abelian := by
  intro G _ _ z S K F h a ha b hb
  classical
  have h6 := h.toStd6r1
  have hOK := std6_hatOK h44 h6.toStd6 (std6r1_comp_rigid h6)
  have hCN : Cz z ≤ normalizer (K : Set G) := fun c hc => std6r1_C_normalizes h6 hc
  have hSC : S ≤ Cz z := h6.sylow.le
  have haN : a ∈ normalizer (K : Set G) := hCN (hSC ha)
  have hbN : b ∈ normalizer (K : Set G) := hCN (hSC hb)
  have habN : a * b * a⁻¹ ∈ normalizer (K : Set G) := mul_mem (mul_mem haN hbN) (inv_mem haN)
  have hbiN : b⁻¹ ∈ normalizer (K : Set G) := inv_mem hbN
  have hcS : a * b * a⁻¹ * b⁻¹ ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
  have hcN : a * b * a⁻¹ * b⁻¹ ∈ normalizer (K : Set G) := mul_mem habN hbiN
  have hin : phi K (a * b * a⁻¹ * b⁻¹) hcN ∈ innOf (Hat K) := by
    have h1 := dict_out_abelian h2A7 hOK.sl2 (phi K a haN) (phi K b hbN)
    have h2 : phi K (a * b * a⁻¹ * b⁻¹) hcN =
        phi K a haN * phi K b hbN * (phi K a haN)⁻¹ * (phi K b hbN)⁻¹ := by
      rw [phi_mul K habN hbiN, phi_mul K (mul_mem haN hbN) (inv_mem haN), phi_mul K haN hbN,
        phi_inv_aux K haN (inv_mem haN), phi_inv_aux K hbN hbiN]
    rw [h2]
    exact h1
  have hinn : InducesInner (a * b * a⁻¹ * b⁻¹) K := (phi_mem_inn_iff K hcN).1 hin
  obtain ⟨k₀, hk₀, hk⟩ := lift_inner_gen (std6_S_pgroup h6.toStd6)
    (std6_exists_sylow_P h6.toStd6 (std6r1_comp_rigid h6))
    (sq_eq_one_of_card_center hOK.sl2.2) hcS hcN hinn
  have hR : Rz S z = (S ⊓ K) ⊔ (S ⊓ cSec K) := Std6r1.Rz_eq h6
  rw [hR]
  have hQ : a * b * a⁻¹ * b⁻¹ * k₀⁻¹ ∈ S ⊓ cSec K := hk
  have : a * b * a⁻¹ * b⁻¹ = (a * b * a⁻¹ * b⁻¹ * k₀⁻¹) * k₀ := by group
  rw [this]
  exact mul_mem (mem_sup_right hQ) (mem_sup_left hk₀)

end CFSG.GH74.GLS.IVK.Lifted
