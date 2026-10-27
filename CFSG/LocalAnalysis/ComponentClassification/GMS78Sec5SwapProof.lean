module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5SwapKey

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII

theorem gms5Swap :
    GMS5Swap := by
  intro G _ _ L T R R₂ a y d hM hS hR₂ hq hcomm _ g hg hgV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h34 : NoStronglyClosedAbelian G := fun S _ hAS hAab hA1 hcl =>
    hM.hyp.lemma34 S hAS hAab hA1 hcl
  have ha : 1 ≤ a := hM.one_le
  have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) := by rw [hq]; omega
  have hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) := by
    rintro ⟨-, h⟩
    rw [hq] at h
    omega
  obtain ⟨w, hw⟩ := hS.exists_swapElt h34 hR₂ h4 hne hg hgV
  obtain ⟨v, φ, c, e, Λ, hC⟩ := hS.exists_rCoords h34 hR₂
  have hgV' : rightConjugate (gmsV L T) g ≠ gmsV L T := by
    rw [hgV]; exact (hS.gmsV_ne_isR₂ hR₂).symm
  obtain ⟨rfl, rfl, rfl⟩ := hS.swapShape h34 hR₂ hC h4 hne hg hgV'
  have hS₁G := hw.isSylowOf_top hS h34 hR₂ h4 hne hcomm
  obtain ⟨-, hS₁2, hS₁idx⟩ := isSylowOf_iff.mp hS₁G
  rw [relIndex_top_right] at hS₁idx
  let S : Sylow 2 G := hS₁2.toSylow hS₁idx
  have hSc : (S : Subgroup G) = R ⊔ zpowers w := IsPGroup.toSylow_coe hS₁2 hS₁idx
  have hAS : gmsA L T ≤ R ⊔ zpowers w :=
    (Sec3.SzR.gmsA_le_T.trans hS.T_le).trans le_sup_left
  have hA1 : gmsA L T ≠ ⊥ := by
    intro hb
    obtain ⟨b, hb', hvb⟩ := hC.v_surj 1
    rw [hb, mem_bot] at hb'
    have h0 : v 1 = 0 := by
      have := hC.v_mul 1 (one_mem _) 1 (one_mem _)
      rw [mul_one] at this
      exact left_eq_add.mp this
    rw [hb', h0] at hvb
    exact zero_ne_one hvb
  have hAab : IsMulCommutative (gmsA L T) := by
    obtain ⟨-, hVel, -, -, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
    exact (isElemAbelian_of_le hVel le_sup_left).1
  refine h34 S (gmsA L T) (hSc ▸ hAS) hAab hA1 fun b hb g' hg' => ?_
  by_contra hx
  have hxS : g'⁻¹ * b * g' ∈ R ⊔ zpowers w := hSc ▸ hg'
  have hconj : g' * (g'⁻¹ * b * g') * g'⁻¹ ∈ gmsA L T := by
    rw [show g' * (g'⁻¹ * b * g') * g'⁻¹ = b by group]
    exact hb
  by_cases hxR : g'⁻¹ * b * g' ∈ R
  · exact hw.false_of_conj_mem_R hS h34 hR₂ h4 hne hcomm hC hxR hx hconj
  · exact hw.false_of_conj_mem_not_R hS h34 hR₂ h4 hne hcomm hC hxS hxR hconj

end CFSG.ComponentClassification.GMS78
