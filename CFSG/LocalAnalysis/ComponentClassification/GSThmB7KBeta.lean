module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB71Step1

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

theorem exists_involution_lift {Y : Type*} [Group Y] [Finite Y] {zb : Y ⧸ pPrimeCore 2 Y}
    (hzb : orderOf zb = 2) : ∃ t : Y, orderOf t = 2 ∧ (t : Y ⧸ pPrimeCore 2 Y) = zb := by
  set e := QuotientGroup.quotientMulEquivOfEq (GSLit.oddCore_eq_pPrimeCore_two Y) with he
  obtain ⟨t, ht, htz⟩ := exists_involution_lift_oddCore (zb := e.symm zb)
    (by rw [MulEquiv.orderOf_eq]; exact hzb)
  refine ⟨t, ht, ?_⟩
  have h1 := congrArg e htz
  rw [MulEquiv.apply_symm_apply] at h1
  rw [← h1]
  rfl

end Seven

namespace Hyp52

variable {X : Type} [Group X] [Finite X]

theorem exists_mem_B_inf_K (h : Hyp52 X) (hKa : conjugate h.K h.a ≠ h.K)
    (hZK : Nat.card (center (h.K ⧸ pPrimeCore 2 h.K)) = 2) :
    ∃ β ∈ h.B, β ∈ h.K ∧ β ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (center (↥h.K ⧸ pPrimeCore 2 ↥h.K)) := by rw [hZK]
  obtain ⟨zb, hzb⟩ := exists_prime_orderOf_dvd_card'
    (G := center (↥h.K ⧸ pPrimeCore 2 ↥h.K)) 2 h2
  obtain ⟨t, ht, htz⟩ := Seven.exists_involution_lift (zb := (zb : ↥h.K ⧸ pPrimeCore 2 ↥h.K))
    (by rw [Subgroup.orderOf_coe, hzb])
  have ht' : orderOf (t : X) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have htc : ∀ k ∈ h.K, k⁻¹ * (t : X)⁻¹ * k * t ∈ oddCoreIn h.K := by
    intro k hk
    have h1 : (⟨k, hk⟩ : h.K)⁻¹ * t⁻¹ * ⟨k, hk⟩ * t ∈ pPrimeCore 2 h.K := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, htz, mul_assoc _ _
          (zb : ↥h.K ⧸ pPrimeCore 2 ↥h.K), mem_center_iff.mp zb.2]
      group
    exact ⟨_, h1, rfl⟩
  obtain ⟨hKW, hKpc⟩ := h.isPComponent_K
  have haW : h.a ∈ normalizer (h.B : Set X) := h.a_mem_normalizer
  have hKaW : conjugate h.K h.a ≤ normalizer (h.B : Set X) :=
    UnbalancedCorr.conjugate_le_of_mem hKW haW
  have hKapc : IsPComponent 2 ((conjugate h.K h.a).subgroupOf
      (normalizer (h.B : Set X))) :=
    UnbalancedCorr.isPComponent_conjugate_subgroupOf haW hKpc
  have htV : (t : X) ∈ coreActionKernel (layerIn (normalizer (h.B : Set X))) := by
    rw [← h.layer_eq_K]
    exact mem_coreActionKernel_sup hKW hKaW hKpc hKapc (Ne.symm hKa) t.2 htc
  have htN : (t : X) ∈ normalizer (h.B : Set X) := hKW t.2
  have ht2 : IsPGroup 2 (zpowers (t : X)) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, ht', pow_one])
  obtain ⟨w, hw, hwB⟩ := exists_conjugate_le_of_sylow h.B_sylow_kernel
    (zpowers_le.mpr (mem_inf.mpr ⟨htN, htV⟩)) ht2
  have hβB : w⁻¹ * t * w ∈ h.B := by
    refine hwB ?_
    rw [mem_conjugate_iff, show w * (w⁻¹ * t * w) * w⁻¹ = t by group]
    exact mem_zpowers _
  have hKV : h.K ≤ layerIn (normalizer (h.B : Set X)) := h.layer_eq_K ▸ le_sup_left
  have hVn : normalizer (h.B : Set X) ≤
      normalizer ((layerIn (normalizer (h.B : Set X)) : Subgroup X) : Set X) := fun g hg => by
    have : (pLayer ↥(normalizer (h.B : Set X)) 2).Characteristic :=
      CatalogueBPrimeJoin.pLayer_characteristic
    exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic _ _ (le_normalizer hg)
  have hKw := conjugate_eq_of_mem_coreActionKernel hKV (map_subtype_le _) hVn hKpc
    (mem_inf.mp hw).1 (mem_inf.mp hw).2
  have hβK : w⁻¹ * t * w ∈ h.K := by
    have h1 : w⁻¹ * (t : X) * w ∈ conjugate h.K w := by
      rw [mem_conjugate_iff, show w * (w⁻¹ * t * w) * w⁻¹ = t by group]
      exact t.2
    rwa [hKw] at h1
  refine ⟨w⁻¹ * t * w, hβB, hβK, fun h1 => ?_⟩
  have h3 : (t : X) = 1 := by
    calc (t : X) = w * (w⁻¹ * t * w) * w⁻¹ := by group
      _ = 1 := by rw [h1]; group
  rw [h3, orderOf_one] at ht'
  exact absurd ht' (by norm_num)

end Hyp52

end CFSG.ComponentClassification.GSThmB
