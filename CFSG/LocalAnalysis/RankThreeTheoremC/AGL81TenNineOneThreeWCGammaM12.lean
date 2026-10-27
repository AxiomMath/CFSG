module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCM12
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGammaAdapt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.CGT.PushingUpLit.Transport
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Equiv CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.GH74.KGroups.TwoM12


theorem kFactTenNineWCGammaM12 :
    ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B) [K.Normal],
      Nonempty (K ≃* NativeSporadic.M12) →
      ∀ (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
        (A Y : Subgroup (MulAut.conjNormal (H := K)).range), Nat.card A = 3 →
        GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y →
        ¬ IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y := by
  intro B _ _ K _ ⟨e⟩ S A Y hA3 hY hwc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZK : ∀ k : K, (∀ x : K, k * x = x * k) → k = 1 := by
    intro k hk
    have hc : e k ∈ Subgroup.center NativeSporadic.M12 := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg e (hk (e.symm y))
      simpa using this.symm
    rw [CFSG.ComponentClassification.M12Cover.m12_center, Subgroup.mem_bot] at hc
    exact e.injective (by rw [hc, map_one])
  set R : Subgroup NativeSporadic.M12 := T27.subgroupOf NativeSporadic.M12 with hRdef
  have hR27 : Nat.card R = 27 := by
    rw [hRdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe T27_le).toEquiv, card_T27]
  have hRidx : ¬ 3 ∣ R.index := by
    have h := R.card_mul_index
    rw [hR27, card_M12] at h
    have : R.index = 3520 := by omega
    rw [this]
    norm_num
  refine false_of_fuse_gamma_inn hZK ?_ ?_ S A hA3 Y hY hwc
  ·
    rintro φ ⟨m, hm⟩
    obtain ⟨j, hj⟩ : Odd (3 ^ m) := Odd.pow (by decide)
    have hK : Nat.card K = 95040 := by rw [Nat.card_congr e.toEquiv, card_M12]
    have hA : Nat.card (MulAut K) = 190080 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv,
        CFSG.ComponentClassification.M12Cover.card_mulAut]
    exact inner_of_index_two hZK (by rw [hA, hK]) φ (hj ▸ hm)
  ·
    intro T a haT hoa hcent
    refine gamma_of_fuse_sq haT hoa ?_
    obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow e
      (IsPGroup.of_card (by rw [hR27]; norm_num : Nat.card R = 3 ^ 3)) hRidx T
    rw [hΦ] at haT hcent ⊢
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp haT
    have ha₀T : (a₀ : Perm (Fin 12)) ∈ T27 := Subgroup.mem_subgroupOf.mp ha₀
    have hc₀ : ∀ t ∈ T27, t * a₀ = a₀ * t := by
      intro t ht
      have h := hcent (Φ ⟨t, T27_le ht⟩) (Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.mpr ht))
      simp only [MulEquiv.coe_toMonoidHom] at h
      have h' : (⟨t, T27_le ht⟩ : NativeSporadic.M12) * a₀ = a₀ * ⟨t, T27_le ht⟩ := by
        apply Φ.injective
        rw [map_mul, map_mul]
        exact mul_inv_eq_iff_eq_mul.mp h
      exact congrArg Subtype.val h'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_c27 ha₀T hc₀)
    have hoc : orderOf c27 = 3 := orderOf_eq_prime c27_cube c27_ne_one
    have hot : orderOf t27 = 3 :=
      orderOf_eq_prime t27_cube fun h => t27_noncomm (by rw [h, one_mul, mul_one])
    have hk3 : k % 3 = 1 ∨ k % 3 = 2 := by
      have h := Int.emod_emod_of_dvd k (dvd_refl (3 : ℤ))
      have h0 : k % 3 ≠ 0 := by
        intro h0
        have : (a₀ : Perm (Fin 12)) = 1 := by
          rw [← hk, ← zpow_mod_orderOf, hoc]
          push_cast
          rw [h0, zpow_zero]
        have h1 : a₀ = 1 := Subtype.ext this
        rw [MulEquiv.coe_toMonoidHom, h1, map_one, orderOf_one] at hoa
        omega
      omega
    set gM : NativeSporadic.M12 := ⟨g27, g27_mem⟩
    have hconj : ((gM * a₀ * gM⁻¹ : NativeSporadic.M12) : Perm (Fin 12)) = t27 ^ k := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, gM]
      rw [← hk, ← g27_conj, ← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    have hsq : Φ gM * Φ gM = 1 := by
      rw [← map_mul, show gM * gM = 1 from Subtype.ext (show g27 * g27 = 1 by decide +kernel),
        map_one]
    refine ⟨Φ gM, hsq, ⟨gM * a₀ * gM⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩, ?_⟩
    · rw [hconj]
      exact Subgroup.zpow_mem _ t27_mem k
    · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    · intro hmem
      have hmem₀ : gM * a₀ * gM⁻¹ ∈ Subgroup.zpowers a₀ := by
        obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hmem
        refine Subgroup.mem_zpowers_iff.mpr ⟨l, Φ.injective ?_⟩
        rw [map_zpow, map_mul, map_mul, map_inv]
        simpa using hl
      obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hmem₀
      have hcx : t27 ^ k * x27 = x27 * t27 ^ k := by
        rw [← hconj, ← hl]
        push_cast
        exact ((Commute.zpow_left (hc₀ x27 x27_mem_T27).symm l)).eq
      rw [← zpow_mod_orderOf, hot] at hcx
      push_cast at hcx
      rcases hk3 with h1 | h2
      · rw [h1, zpow_one] at hcx
        exact t27_noncomm hcx
      · rw [h2] at hcx
        exact t27_sq_noncomm (by exact_mod_cast hcx)

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
