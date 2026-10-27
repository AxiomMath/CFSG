module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.Relations
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.Involutions

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab wA wordOK eA keyF)
open CFSG.ClassicalInvolution.Generic
open scoped Pointwise

set_option linter.unusedSectionVars false


private theorem iv2_exists_lift (x : WP) : ∃ u : HY, (u : WP × WP).1 = x := by
  obtain ⟨y, hy⟩ := pHat_surjective (sigmaO (pHat x))
  exact ⟨⟨(x, y), mem_YP.2 hy.symm⟩, rfl⟩

private theorem iv2_pHat_zPlus : pHat zPlus = 1 := by
  have h : pHat (1 : WP) = pHat zPlus := pHat_eq_iff.2 (Or.inr (one_mul zPlus).symm)
  rw [map_one] at h
  exact h.symm

private theorem iv2_fst_one {w : HY} (hw : (w : WP × WP).1 = 1) : w = 1 ∨ w = cK 1 := by
  have hker : w ∈ qY.ker := by
    rw [MonoidHom.mem_ker, qY_apply, hw, map_one]
  rcases (mem_ker_qY.1 hker).2 with h2 | h2
  · left
    apply Subtype.ext
    apply Prod.ext
    · simpa using hw
    · simpa using h2
  · right
    apply Subtype.ext
    apply Prod.ext
    · simpa [cK] using hw
    · simpa [cK] using h2

private theorem iv2_fst_eq {u v : HY} (h : (u : WP × WP).1 = (v : WP × WP).1) :
    v = u ∨ v = u * cK 1 := by
  have hw : ((u⁻¹ * v : HY) : WP × WP).1 = 1 := by
    rw [Subgroup.coe_mul, Prod.fst_mul, Subgroup.coe_inv, Prod.fst_inv, h, inv_mul_cancel]
  rcases iv2_fst_one hw with h1 | h1
  · exact Or.inl (inv_mul_eq_one.1 h1).symm
  · exact Or.inr (inv_mul_eq_iff_eq_mul.1 h1)

private theorem iv2_no_lift {L s : HY} (h : (L : WP × WP).1 = (s : WP × WP).1) (hs : s * s = 1)
    (hL : L * L ≠ 1 ∧ (L * cK 1) * (L * cK 1) ≠ 1) : False := by
  rcases iv2_fst_eq h with h1 | h1
  · exact hL.1 (by rw [← h1]; exact hs)
  · exact hL.2 (by rw [← h1]; exact hs)

theorem exists_conj_repY (t : HY) (ht : t * t = 1) (hc : t ∉ Subgroup.center HY) :
    ∃ g : HY, g * t * g⁻¹ = t0Y ∨ g * t * g⁻¹ = tcY := by
  have ha2 : (t : WP × WP).1 * (t : WP × WP).1 = 1 := by
    have h := congrArg (fun u : HY => (u : WP × WP).1) ht
    simpa using h
  have h1 : (t : WP × WP).1 ≠ 1 := by
    intro h
    have hk : t ∈ qY.ker := by
      rw [MonoidHom.mem_ker, qY_apply, h, map_one]
    exact hc (ker_qY_le_center hk)
  have hz : (t : WP × WP).1 ≠ zPlus := by
    intro h
    have hk : t ∈ qY.ker := by
      rw [MonoidHom.mem_ker, qY_apply, h, iv2_pHat_zPlus]
    exact hc (ker_qY_le_center hk)
  obtain ⟨g, hg⟩ := Om1.exists_conj_rep ((t : WP × WP).1) ha2 h1 hz
  obtain ⟨g', hg'⟩ := iv2_exists_lift g
  have hs1 : ((g' * t * g'⁻¹ : HY) : WP × WP).1 = g * (t : WP × WP).1 * g⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, hg']
  have hs2 : (g' * t * g'⁻¹) * (g' * t * g'⁻¹) = 1 := by
    calc (g' * t * g'⁻¹) * (g' * t * g'⁻¹) = g' * (t * t) * g'⁻¹ := by group
      _ = 1 := by rw [ht]; group
  rcases hg with hg | hg | hg | hg
  ·
    have hfst : (t0Y : WP × WP).1 = ((g' * t * g'⁻¹ : HY) : WP × WP).1 :=
      fst_t0Y.trans (hg.symm.trans hs1.symm)
    rcases iv2_fst_eq hfst with h | h
    · exact ⟨g', Or.inl h⟩
    ·
      refine ⟨(fuse0 1)⁻¹ * g', Or.inl ?_⟩
      have hc1 : g' * t * g'⁻¹ = fuse0 1 * t0Y * (fuse0 1)⁻¹ := by
        rw [h, fuse0_conj (by norm_num : (1 : ℕ) < 3)]
      calc (fuse0 1)⁻¹ * g' * t * ((fuse0 1)⁻¹ * g')⁻¹
          = (fuse0 1)⁻¹ * (g' * t * g'⁻¹) * fuse0 1 := by group
        _ = (fuse0 1)⁻¹ * (fuse0 1 * t0Y * (fuse0 1)⁻¹) * fuse0 1 := by rw [hc1]
        _ = t0Y := by group
  ·
    have hfst : (liftA : WP × WP).1 = ((g' * t * g'⁻¹ : HY) : WP × WP).1 :=
      fst_liftA.trans (hg.symm.trans hs1.symm)
    exact (iv2_no_lift hfst hs2 liftA_sq_ne).elim
  ·
    have hfst : (liftB : WP × WP).1 = ((g' * t * g'⁻¹ : HY) : WP × WP).1 :=
      fst_liftB.trans (hg.symm.trans hs1.symm)
    exact (iv2_no_lift hfst hs2 liftB_sq_ne).elim
  ·
    have hfst : (tcY : WP × WP).1 = ((g' * t * g'⁻¹ : HY) : WP × WP).1 :=
      fst_tcY.trans (hg.symm.trans hs1.symm)
    rcases iv2_fst_eq hfst with h | h
    · exact ⟨g', Or.inr h⟩
    · refine ⟨fuseC⁻¹ * g', Or.inr ?_⟩
      have hc1 : g' * t * g'⁻¹ = fuseC * tcY * fuseC⁻¹ := by
        rw [h, fuseC_conj]
      calc fuseC⁻¹ * g' * t * (fuseC⁻¹ * g')⁻¹
          = fuseC⁻¹ * (g' * t * g'⁻¹) * fuseC := by group
        _ = fuseC⁻¹ * (fuseC * tcY * fuseC⁻¹) * fuseC := by rw [hc1]
        _ = tcY := by group

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2
