module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCSp62
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGammaAdapt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFSp8
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62FrameScan
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalAut
public import Certificates.Certificate5169

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.KGroups.Sp6 CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
theorem mulC_cT6_cT6 : mulC cT6 cT6 = oneC := by decide


theorem kFactTenNineWCGammaSp62 :
    ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B) [K.Normal],
      Nonempty (K ≃* H6) →
      ∀ (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
        (A Y : Subgroup (MulAut.conjNormal (H := K)).range), Nat.card A = 3 →
        GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y →
        ¬ IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y := by
  intro B _ _ K _ ⟨e⟩ S A Y hA3 hY hwc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZH : Subgroup.center H6 = ⊥ := by
    haveI := CFSG.RankThree.PartTwo.Sec4.RonanK429F.Sp8.isSimpleGroup_H6
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H6) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := CFSG.RankThree.PartTwo.Sec4.RonanK429F.Sp8.exists_not_comm_H6
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hσT : elt cSg ∈ T0 := elt_mem_Hgen (by simp [gensT])
  have hσE : elt cSg ∈ E0 := elt_mem_Hgen (by simp [gensE])
  have hw2T : elt cW2 ∈ T0 := elt_mem_Hgen (by simp [gensT])
  have hz0T : z0 ∈ T0 := E0_le_T0 z0_mem_E0
  refine false_of_fuse_gamma_inn ?_ ?_ ?_ S A hA3 Y hY hwc
  ·
    intro k hk
    have hc : e k ∈ Subgroup.center H6 := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg e (hk (e.symm y))
      simpa using this.symm
    rw [hZH, Subgroup.mem_bot] at hc
    exact e.injective (by rw [hc, map_one])
  ·
    rintro φ -
    obtain ⟨g, hg⟩ := all_inner_H6 (MulAut.congr e φ)
    refine ⟨e.symm g, fun x => e.injective ?_⟩
    have h1 : (MulAut.congr e φ) (e x) = e (φ x) := by simp [MulAut.congr_apply]
    have h2 : (MulAut.congr e φ) (e x) = g * e x * g⁻¹ := by rw [hg, MulAut.conj_apply]
    rw [← h1, h2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  ·
    intro T a haT hoa hcent
    refine gamma_of_fuse_sq haT hoa ?_
    obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow e isPGroup_T0 not_dvd_index_T0 T
    rw [hΦ] at haT hcent ⊢
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp haT
    have hc₀ : ∀ p ∈ T0, p * a₀ = a₀ * p := by
      intro p hp
      have h := hcent (Φ p) (Subgroup.mem_map_of_mem _ hp)
      simp only [MulEquiv.coe_toMonoidHom] at h
      apply Φ.injective
      rw [map_mul, map_mul]
      exact mul_inv_eq_iff_eq_mul.mp h
    have ha₀B : a₀ ∈ B0 := centralizer_B0_le
      (Subgroup.mem_centralizer_iff.mpr fun p hp => hc₀ p (B0_le_T0 hp))
    obtain ⟨t, ht, hrep⟩ := Hgen_rep tabCheck_B ha₀B
    have hcomm : commB t cSg = true := by
      have h := hc₀ (elt cSg) hσT
      exact beq_iff_eq.2 ((hrep.comm_iff (rep_elt (genB_isoB genB_cSg))).1 h.symm)
    have hZt : inZ t = true := by
      have h := forall_of_allCheck Certificates.certificate5169 t ht
      simpa [hcomm] using h
    have ha₀z := mem_zpowers_z0 hrep hZt
    set y := elt cT6 * z0 * (elt cT6)⁻¹ with hy
    have hyrep : Rep y (mulC cZ cW2) := conjC_cT6_cZ ▸ rep_conj_elt genB_cT6 rep_z0
    have hyT : y ∈ T0 := by
      have h2 : Rep (z0 * elt cW2) (mulC cZ cW2) := rep_z0.mul (rep_elt (genB_isoB genB_cW2))
      rw [hyrep.eq h2]
      exact T0.mul_mem hz0T hw2T
    have hzσ : ∀ s ∈ Subgroup.zpowers z0, s * elt cSg = elt cSg * s := by
      intro s hs
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      exact (Commute.zpow_left (z0_comm_E0 (elt cSg) hσE) k).eq
    have hyσ : ¬ y * elt cSg = elt cSg * y := by
      rw [hyrep.comm_iff (rep_elt (genB_isoB genB_cSg))]
      intro h
      have := not_commB_zw
      simp [commB, h] at this
    have hy2σ : ¬ (y * y) * elt cSg = elt cSg * (y * y) := by
      rw [(hyrep.mul hyrep).comm_iff (rep_elt (genB_isoB genB_cSg))]
      intro h
      have := not_commB_zw2
      simp [commB, h] at this
    have hconj1 : Φ (elt cT6) * Φ z0 * (Φ (elt cT6))⁻¹ = Φ y := by
      rw [hy, map_mul, map_mul, map_inv]
    rcases zpowers_z0_cases ha₀z with h1 | h1 | h1
    · exfalso
      rw [h1, MulEquiv.coe_toMonoidHom, map_one, orderOf_one] at hoa
      omega
    · subst h1
      have hsq : Φ (elt cT6) * Φ (elt cT6) = 1 := by
        rw [← map_mul, show elt cT6 * elt cT6 = 1 from
          ((rep_elt (genB_isoB genB_cT6)).mul (rep_elt (genB_isoB genB_cT6))).eq
            (by rw [mulC_cT6_cT6]; exact Rep.one), map_one]
      refine ⟨Φ (elt cT6), hsq, ⟨y, hyT, ?_⟩, ?_⟩
      · simp only [MulEquiv.coe_toMonoidHom]; exact hconj1.symm
      · intro hmem
        simp only [MulEquiv.coe_toMonoidHom] at hmem
        rw [hconj1] at hmem
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
        rw [← map_zpow] at hk
        exact hyσ (hzσ y (Subgroup.mem_zpowers_iff.mpr ⟨k, Φ.injective hk⟩))
    · subst h1
      have hc2 : Φ (elt cT6) * Φ (z0 * z0) * (Φ (elt cT6))⁻¹ = Φ (y * y) := by
        rw [map_mul Φ y y, ← hconj1, map_mul]
        group
      have hsq : Φ (elt cT6) * Φ (elt cT6) = 1 := by
        rw [← map_mul, show elt cT6 * elt cT6 = 1 from
          ((rep_elt (genB_isoB genB_cT6)).mul (rep_elt (genB_isoB genB_cT6))).eq
            (by rw [mulC_cT6_cT6]; exact Rep.one), map_one]
      refine ⟨Φ (elt cT6), hsq, ⟨y * y, T0.mul_mem hyT hyT, ?_⟩, ?_⟩
      · simp only [MulEquiv.coe_toMonoidHom]
        exact hc2.symm
      · intro hmem
        simp only [MulEquiv.coe_toMonoidHom] at hmem
        rw [hc2] at hmem
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
        rw [← map_zpow] at hk
        have hk' := Φ.injective hk
        apply hy2σ
        refine hzσ (y * y) (Subgroup.mem_zpowers_iff.mpr ⟨2 * k, ?_⟩)
        rw [← hk', ← pow_two, ← zpow_natCast, ← zpow_mul, mul_comm]
        norm_num [mul_comm]

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
