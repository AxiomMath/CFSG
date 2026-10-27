module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCAlt9
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGammaAdapt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA.L9

theorem kFactTenNineWCGammaAlt9 :
    ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B) [K.Normal],
      Nonempty (K ≃* alternatingGroup (Fin 9)) →
      ∀ (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
        (A Y : Subgroup (MulAut.conjNormal (H := K)).range), Nat.card A = 3 →
        GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y →
        ¬ IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y := by
  intro B _ _ K _ ⟨e⟩ S A Y hA3 hY hwc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEbar : ∀ x : alternatingGroup (Fin 9), x * ea = ea * x → x * eb = eb * x →
      x * ec = ec * x → x ∈ Ebar := by
    intro x ha hb hc
    rw [Ebar, Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ha.symm
    · exact hb.symm
    · exact hc.symm
  refine false_of_fuse_gamma_inn ?_ ?_ ?_ S A hA3 Y hY hwc
  ·
    intro k hk
    have hc : ∀ y : alternatingGroup (Fin 9), e k * y = y * e k := by
      intro y
      have := congrArg e (hk (e.symm y))
      simpa using this
    obtain ⟨i, hi⟩ := eq_toE_diag (hEbar _ (hc ea) (hc eb) (hc ec)) (hc ew)
    have h0 := toP_comm_pt i (by have := congrArg Subtype.val (hc et); rw [hi] at this; exact this)
    subst h0
    apply e.injective
    rw [hi, map_one]
    exact Subtype.ext toP_zero
  ·
    rintro φ ⟨m, hm⟩
    obtain ⟨j, hj⟩ : Odd (3 ^ m) := Odd.pow (by decide)
    exact inner_of_odd_alt (by norm_num) e φ (hj ▸ hm)
  ·
    intro T a haT hoa hcent
    refine gamma_of_fuse_sq haT hoa ?_
    obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow e
      (IsPGroup.of_card (by rw [card_Pst]; norm_num : Nat.card Pst = 3 ^ 4))
      not_three_dvd_index_Pst T
    rw [hΦ] at haT hcent ⊢
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp haT
    have hc₀ : ∀ p ∈ Pst, p * a₀ = a₀ * p := by
      intro p hp
      have h := hcent (Φ p) (Subgroup.mem_map_of_mem _ hp)
      simp only [MulEquiv.coe_toMonoidHom] at h
      apply Φ.injective
      rw [map_mul, map_mul]
      exact mul_inv_eq_iff_eq_mul.mp h
    have hx := eq_toE_diag (hEbar _ (hc₀ _ gens_mem_Pst.1).symm (hc₀ _ gens_mem_Pst.2.1).symm
      (hc₀ _ gens_mem_Pst.2.2).symm) (hc₀ _ ew_mem_Pst).symm
    obtain ⟨i, rfl⟩ := hx
    have hi0 : i ≠ 0 := by
      rintro rfl
      have : (toE 0 0 0 : alternatingGroup (Fin 9)) = 1 := Subtype.ext toP_zero
      rw [MulEquiv.coe_toMonoidHom, this, map_one, orderOf_one] at hoa
      omega
    have hsq : Φ et * Φ et = 1 := by
      rw [← map_mul, show et * et = 1 from Subtype.ext (by decide), map_one]
    refine ⟨Φ et, hsq, ?_, ?_⟩
    · refine ⟨et * toE i i i * et⁻¹, Ebar_le_Pst ?_, ?_⟩
      · obtain ⟨h1, h2, h3⟩ := pt_toP_comm i
        exact mem_Ebar_iff.mpr ⟨h1, h2, h3⟩
      · simp
    · intro hmem
      have hoa₀ : orderOf (toE i i i) = 3 := by
        rw [← hoa, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
      have hmem₀ : et * toE i i i * et⁻¹ ∈ zpowers (toE i i i) := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, Φ.injective ?_⟩
        rw [map_zpow, map_mul, map_mul, map_inv]
        simpa using hk
      rw [(orderOf_pos_iff.mp (by rw [hoa₀]; norm_num)).mem_zpowers_iff_mem_range_orderOf,
        hoa₀] at hmem₀
      simp only [Finset.mem_image, Finset.mem_range] at hmem₀
      obtain ⟨l, hl3, hl⟩ := hmem₀
      apply pt_toP_not_pow i hi0 ⟨l, hl3⟩
      have := congrArg Subtype.val hl
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow] at this
      exact this.symm

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
