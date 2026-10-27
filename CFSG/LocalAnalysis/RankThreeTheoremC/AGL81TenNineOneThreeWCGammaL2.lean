module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCL2
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGammaAdapt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGammaMove
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

namespace L2

open Matrix CFSG.GorensteinWalter CFSG.Quasithin.Vol2.Ch11.SecD.BK10.L2
open scoped MatrixGroups

theorem kFactTenNineWCGammaL2 :
    ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B) [K.Normal] (F : Type) [Field F] [Finite F]
      [CharP F 3], 9 ≤ Nat.card F → Nonempty (K ≃* PSL2 F) →
      ∀ (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
        (A Y : Subgroup (MulAut.conjNormal (H := K)).range), Nat.card A = 3 →
        GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y →
        ¬ IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y := by
  intro B _ _ K _ F _ _ _ h9 ⟨e⟩ S A Y hA3 hY hwc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 3
  rw [← Nat.card_eq_fintype_card] at hn
  obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow F hn
  have hU : IsPGroup 3 (psl2UpperUnipotentSubgroup F) := hQ ▸ Q.isPGroup'
  have hUi : ¬ 3 ∣ (psl2UpperUnipotentSubgroup F).index := hQ ▸ Q.not_dvd_index
  refine false_of_fuse_gamma_out ?_ ?_ ?_ S A hA3 Y hY hwc
  ·
    intro k hk
    have hc : e k ∈ Subgroup.center (PSL2 F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg e (hk (e.symm y))
      simpa using this.symm
    rw [center_psl2 h9, Subgroup.mem_bot] at hc
    exact e.injective (by rw [hc, map_one])
  ·
    intro T φ _ hfix
    obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow e hU hUi T
    set ψ : MulAut (PSL2 F) := (MulAut.congr Φ.symm) φ
    have hψ : ∀ b : F, ψ (psl2QuotientMap F (sl2UpperUnipotent b)) =
        psl2QuotientMap F (sl2UpperUnipotent b) := by
      intro b
      have hmem : Φ (psl2QuotientMap F (sl2UpperUnipotent b)) ∈ (T : Subgroup K) := by
        rw [hΦ]
        exact Subgroup.mem_map_of_mem _ ((mem_psl2UpperUnipotentSubgroup_iff _).mpr ⟨b, rfl⟩)
      simp [ψ, MulAut.congr_apply, hfix _ hmem]
    obtain ⟨g, hg⟩ := inner_of_fix_unip ψ hψ
    refine ⟨Φ g, fun y => ?_⟩
    have h := hg (Φ.symm y)
    simp only [ψ, MulAut.congr_apply, MulEquiv.symm_symm] at h
    have h2 := congrArg Φ h
    simpa using h2
  ·
    intro T a haT hoa _
    refine gamma_of_fuse_normalizer haT hoa ?_
    obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow e hU hUi T
    rw [hΦ] at haT ⊢
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp haT
    obtain ⟨b, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff x).mp hx
    have hb : b ≠ 0 := by
      rintro rfl
      rw [sl2UpperUnipotent_zero, map_one, MulEquiv.coe_toMonoidHom, map_one, orderOf_one] at hoa
      omega
    obtain ⟨l, hl0, hl4⟩ := exists_l h9
    refine ⟨Φ (psl2QuotientMap F (dmat l hl0)), ?_, ?_⟩
    · refine mem_normalizer_of_conj_mem fun r hr => ?_
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hr
      obtain ⟨c, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff x).mp hx
      refine ⟨psl2QuotientMap F (sl2UpperUnipotent (l ^ 2 * c)),
        (mem_psl2UpperUnipotentSubgroup_iff _).mpr ⟨_, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← dmat_conj l hl0 c, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    · intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      simp only [MulEquiv.coe_toMonoidHom] at hk
      rw [← map_zpow Φ, ← map_inv Φ, ← map_mul Φ, ← map_mul Φ] at hk
      have hk2 := Φ.injective hk
      rw [← map_zpow (psl2QuotientMap F), unip_zpow, ← map_inv (psl2QuotientMap F),
        ← map_mul (psl2QuotientMap F), ← map_mul (psl2QuotientMap F), dmat_conj] at hk2
      have hkb := unip_inj hk2
      have hkl : (k : F) = l ^ 2 := mul_right_cancel₀ hb hkb
      apply hl4
      rcases intCast_trichotomy (F := F) k with h | h | h <;> rw [h] at hkl
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hkl.symm) hl0
      · rw [show l ^ 4 = (l ^ 2) ^ 2 by ring, ← hkl, one_pow]
      · rw [show l ^ 4 = (l ^ 2) ^ 2 by ring, ← hkl]
        ring

end L2

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
