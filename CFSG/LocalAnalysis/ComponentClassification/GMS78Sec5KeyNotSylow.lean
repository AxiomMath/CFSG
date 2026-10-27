module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Swap
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Key
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeySpan

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII

theorem gms5NotSylow_of_key :
    GMS5NotSylow := by
  intro G _ _ L T R R₂ a y d hM hS hR₂ hne hRN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRG : IsSylowOf 2 R ⊤ := isSylowOf_top_of_isSylowOf_normalizer' hRN
  have h34 : NoStronglyClosedAbelian G := fun S _ hAS hAab hA1 hcl =>
    hM.hyp.lemma34 S hAS hAab hA1 hcl
  obtain ⟨v, φ, c, e, Λ, hC⟩ := hS.exists_rCoords h34 hR₂
  have ha : 1 ≤ a := hM.one_le
  have : Fintype (BinaryGaloisField (2 * a + 1)) := Fintype.ofFinite _
  have hK : Fintype.card (BinaryGaloisField (2 * a + 1)) = 2 ^ (2 * a + 1) := by
    rw [← Nat.card_eq_fintype_card]
    simpa [BinaryGaloisField] using GaloisField.card 2 (2 * a + 1) (by omega)
  have hΛ4 : 4 ≤ Nat.card Λ := by
    rw [hC.card]
    obtain ⟨E, hE, -, hE4⟩ := hS.sec3.exists_four_le
    exact hE4 ▸ Subgroup.card_le_of_le hE
  have hRu : ¬ (a = 1 ∧ Nat.card Λ = 4) := by rw [hC.card]; exact hne
  obtain ⟨-, hR2, hRidx⟩ := isSylowOf_iff.mp hRG
  rw [relIndex_top_right] at hRidx
  let S : Sylow 2 G := hR2.toSylow hRidx
  have hSc : (S : Subgroup G) = R := IsPGroup.toSylow_coe hR2 hRidx
  have hAR : gmsA L T ≤ R := Sec3.SzR.gmsA_le_T.trans hS.T_le
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
  refine h34 S (gmsA L T) (hSc ▸ hAR) hAab hA1 fun b hb g hg => ?_
  by_contra hx
  have hxR : g⁻¹ * b * g ∈ R := hSc ▸ hg
  have hconj : g * (g⁻¹ * b * g) * g⁻¹ ∈ gmsA L T := by
    rw [show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
    exact hb
  have hQ := hS.sqMap_eq_zero_of_conj_mem hC hxR hconj
  have hr := hS.snd_ne_zero_of_conj_mem h34 hR₂ hC hxR hx hconj
  exact hS.closure_sqMap_ne_top_of_conj_mem h34 hC hRG hxR hx hconj
    (VLike.closure_sqMap_perp_eq_top ha hK hΛ4 hRu hr hQ)

end CFSG.ComponentClassification.GMS78
