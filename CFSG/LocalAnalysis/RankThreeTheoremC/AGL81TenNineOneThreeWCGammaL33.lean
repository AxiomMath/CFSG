module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCL33
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGammaAdapt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.GH74.KGroups.L33
import CFSG.GH74.SmallRanks.PSL
public import CFSG.GH74.KGroups.L33Inputs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Matrix
theorem wmat_sq_conj (z : ZMod 3) :
    wmat * wmat * uni 0 0 z * (wmat * wmat)⁻¹ = uni 0 0 z * uni 0 0 z := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  show wM * wM * uniM 0 0 z = uniM 0 0 z * uniM 0 0 z * (wM * wM)
  revert z
  decide

theorem kFactTenNineWCGammaL33 :
    ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B) [K.Normal],
      Nonempty (K ≃* SL33) →
      ∀ (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
        (A Y : Subgroup (MulAut.conjNormal (H := K)).range), Nat.card A = 3 →
        GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y →
        ¬ IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y := by
  intro B _ _ K _ ⟨e⟩ S A Y hA3 hY hwc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZK : ∀ k : K, (∀ x : K, k * x = x * k) → k = 1 := by
    intro k hk
    have hc : e k ∈ Subgroup.center SL33 := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg e (hk (e.symm y))
      simpa using this.symm
    rw [CFSG.GH74.KGroups.L33.center_bot, Subgroup.mem_bot] at hc
    exact e.injective (by rw [hc, map_one])
  refine false_of_fuse_gamma_inn hZK ?_ ?_ S A hA3 Y hY hwc
  ·
    rintro φ ⟨m, hm⟩
    obtain ⟨j, hj⟩ : Odd (3 ^ m) := Odd.pow (by decide)
    obtain ⟨e2⟩ := CFSG.GH74.KGroups.L33.equiv_psl_P13
    obtain ⟨e3⟩ := CFSG.GH74.KGroups.L33.equiv_P13_P
    have e' : K ≃* CFSG.GH74.KGroups.L33.QP.originalSubgroup :=
      e.trans (((QuotientGroup.quotientMulEquivOfEq
        CFSG.GH74.KGroups.L33.center_bot).trans QuotientGroup.quotientBot).symm.trans (e2.trans e3))
    have hK : Nat.card K = 5616 := by
      rw [Nat.card_congr e.toEquiv, CFSG.GH74.SmallRanks.card_sl3]
    exact inner_of_index_two hZK (by rw [CFSG.GH74.KGroups.L33.card_mulAut e', hK]) φ (hj ▸ hm)
  ·
    intro T a haT hoa hcent
    refine gamma_of_fuse_sq_conj haT hoa ?_
    obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow e
      (IsPGroup.of_card (by rw [card_unitri]; norm_num : Nat.card unitri = 3 ^ 3))
      not_three_dvd_index_unitri T
    rw [hΦ] at haT hcent ⊢
    obtain ⟨a₀, ⟨x, y, z, rfl⟩, rfl⟩ := Subgroup.mem_map.mp haT
    have hc₀ : ∀ x' y' z' : ZMod 3, uni x' y' z' * uni x y z = uni x y z * uni x' y' z' := by
      intro x' y' z'
      have h := hcent (Φ (uni x' y' z')) (Subgroup.mem_map_of_mem _ ⟨_, _, _, rfl⟩)
      simp only [MulEquiv.coe_toMonoidHom] at h
      apply Φ.injective
      rw [map_mul, map_mul]
      exact mul_inv_eq_iff_eq_mul.mp h
    have hy : y = 0 := y_eq_zero (hc₀ 1 0 0)
    have hx : x = 0 := x_eq_zero (hc₀ 0 1 0)
    subst hx hy
    have hz : z ≠ 0 := by
      rintro rfl
      rw [MulEquiv.coe_toMonoidHom, uni_zero, map_one, orderOf_one] at hoa
      omega
    have hsq : (Φ wmat * Φ wmat) * Φ.toMonoidHom (uni 0 0 z) * (Φ wmat * Φ wmat)⁻¹ ∈
        Subgroup.zpowers (Φ.toMonoidHom (uni 0 0 z)) := by
      refine Subgroup.mem_zpowers_iff.mpr ⟨2, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, wmat_sq_conj, zpow_two, map_mul]
    refine ⟨Φ wmat, hsq, ⟨uni z 0 0, ⟨_, _, _, rfl⟩, ?_⟩, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom]
      rw [← wmat_conj, map_mul, map_mul, map_inv]
    ·
      intro hmem
      have hmem₀ : uni z 0 0 ∈ Subgroup.zpowers (uni 0 0 z) := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, Φ.injective ?_⟩
        rw [map_zpow, ← wmat_conj, map_mul, map_mul, map_inv]
        simpa using hk
      have hcomm : ∀ g ∈ Subgroup.zpowers (uni 0 0 z), uni 0 1 0 * g = g * uni 0 1 0 := by
        intro g hg
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        have hc : Commute (uni 0 1 0) (uni 0 0 z) := comm_center z
        exact (hc.zpow_right k).eq
      exact hz (x_eq_zero (hcomm _ hmem₀))

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
