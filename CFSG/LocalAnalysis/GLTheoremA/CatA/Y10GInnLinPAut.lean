module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel
public import CFSG.Assembly.GL83StatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

theorem charP_two_of_two_eq_zero {K : Type} [Field K] (h2 : (2 : K) = 0) : CharP K 2 :=
  (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2)

section Aut

variable {d : ℕ} {K : Type} [Field K] [Finite K]

theorem linAutDecomp3_of_eq (h2 : (2 : K) = 0) (hd : 3 ≤ d) (H : Subgroup (GL (Fin d) K))
    (hH : H = StatedSL d K) (β : MulAut (LargeEvenProj H)) (hβ : β ^ 3 = 1) :
    ∃ u f : MulAut (LargeEvenProj H), β = u * f ∧
      u ∈ LargeEvenMatConjImage (LargeEvenProjMk H) Set.univ ∧
      f ∈ LargeEvenMatFieldImage (LargeEvenProjMk H) ∧ f ^ 3 = 1 := by
  subst hH
  haveI : CharP K 2 := charP_two_of_two_eq_zero h2
  let ψ : LargeEvenProj (StatedSL d K) ≃* projectiveSL d K :=
    CFSG.ComponentClassification.RankTwoClassical.statedProjEquiv d K
  let sL : SpecialLinearGroup (Fin d) K ≃* StatedSL d K :=
    LowTwoRank.specialLinearGroupEquivStatedSL d K
  have hψ : ∀ h : ↥(StatedSL d K),
      ψ (LargeEvenProjMk (StatedSL d K) h) = proj d K (sL.symm h) := by
    intro h
    have := CFSG.ComponentClassification.RankTwoClassical.statedProjEquiv_mk (n := d) (K := K)
      (sL.symm h)
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hR : ∀ h' : ↥(StatedSL d K),
      LargeEvenProjMk (StatedSL d K) h' = ψ.symm (proj d K (sL.symm h')) := by
    intro h'
    rw [← hψ h', MulEquiv.symm_apply_apply]
  have hcoe : ∀ g : SpecialLinearGroup (Fin d) K,
      ((sL g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = (g : Matrix (Fin d) (Fin d) K) :=
    fun g => LowTwoRank.specialLinearGroupEquivStatedSL_coe d K g
  have hcoe' : ∀ h : ↥(StatedSL d K),
      ((sL.symm h : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    intro h
    rw [← hcoe, MulEquiv.apply_symm_apply]
  have hconj : ∀ (A : GL (Fin d) K) (h h' : ↥(StatedSL d K)),
      (h' : GL (Fin d) K) = A * h * A⁻¹ →
      (MulAut.congr ψ).symm (conjAut d K A) (LargeEvenProjMk (StatedSL d K) h) =
        LargeEvenProjMk (StatedSL d K) h' := by
    intro A h h' hh
    show ψ.symm (conjAut d K A (ψ (LargeEvenProjMk (StatedSL d K) h))) = _
    rw [hψ h, conjAut_proj, hR h']
    congr 2
    apply Subtype.ext
    rw [coe_slConjugation, hcoe' h, hcoe' h', hh]
    simp [Units.val_mul]
  have hfield : ∀ (σ : K ≃+* K) (h h' : ↥(StatedSL d K)),
      ((h' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ →
      (MulAut.congr ψ).symm (fieldAut d K σ) (LargeEvenProjMk (StatedSL d K) h) =
        LargeEvenProjMk (StatedSL d K) h' := by
    intro σ h h' hh
    show ψ.symm (fieldAut d K σ (ψ (LargeEvenProjMk (StatedSL d K) h))) = _
    rw [hψ h, fieldAut_proj, hR h']
    congr 2
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, hcoe' h, hcoe' h', hh]
    try rfl
  have hβ' : (MulAut.congr ψ β) ^ 3 = 1 := by
    rw [← map_pow, hβ, map_one]
  obtain ⟨i, hi, c, hc, hic⟩ :=
    CFSG.StandardType.AutPSL.exists_mul_compl (K := K) hd (MulAut.congr ψ β)
  have hnorm : (CFSG.StandardType.AutPSL.inndiag (n := d) (K := K)).Normal :=
    CFSG.StandardType.AutPSL.inndiag_normal (K := K) hd
  have hc3 : c ^ 3 = 1 := by
    have hcube : (i * c) ^ 3 = 1 := by rw [← hic]; exact hβ'
    have hk : c ^ 3 = (i * (c * i * c⁻¹) * (c ^ 2 * i * (c ^ 2)⁻¹))⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      have hcube3 : (i * c) ^ 3 = i * c * i * c * i * c := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      have hid : i * (c * i * c⁻¹) * (c ^ 2 * i * (c ^ 2)⁻¹) * c ^ 3 = i * c * i * c * i * c := by
        group
      rw [hid, ← hcube3]
      exact hcube
    have hmem : c ^ 3 ∈ CFSG.StandardType.AutPSL.inndiag (n := d) (K := K) := by
      rw [hk]
      exact inv_mem (mul_mem (mul_mem hi (hnorm.conj_mem _ hi c))
        (hnorm.conj_mem _ hi (c ^ 2)))
    have hcomp : c ^ 3 ∈ CFSG.StandardType.AutPSL.compl (n := d) (K := K) := pow_mem hc 3
    have hmem2 : c ^ 3 ∈ CFSG.StandardType.AutPSL.inndiag (n := d) (K := K) ⊓
        CFSG.StandardType.AutPSL.compl (n := d) (K := K) :=
      Subgroup.mem_inf.mpr ⟨hmem, hcomp⟩
    rw [CFSG.StandardType.AutPSL.inndiag_inf_compl (K := K) hd] at hmem2
    exact Subgroup.mem_bot.mp hmem2
  obtain ⟨σ, hσ | hσ⟩ := hc
  ·
    subst hσ
    obtain ⟨A, hA⟩ := hi
    subst hA
    refine ⟨(MulAut.congr ψ).symm (conjAut d K A), (MulAut.congr ψ).symm (fieldAut d K σ),
      ?_, ?_, ?_, ?_⟩
    · calc β = (MulAut.congr ψ).symm (MulAut.congr ψ β) :=
            ((MulAut.congr ψ).symm_apply_apply β).symm
        _ = (MulAut.congr ψ).symm (conjAut d K A * fieldAut d K σ) := by rw [hic]
        _ = _ := map_mul _ _ _
    · refine ⟨A, Set.mem_univ _, fun h h' hh => hconj A h h' hh⟩
    · exact ⟨σ, fun h h' hh => hfield σ h h' hh⟩
    · rw [← map_pow, hc3, map_one]
  ·
    exfalso
    subst hσ
    have hcomm : Commute (fieldAut d K σ) (CFSG.StandardType.AutPSL.graphAut (n := d) (K := K)) :=
      CFSG.StandardType.AutPSL.fieldAut_mul_graphAut σ
    have hg3 : (CFSG.StandardType.AutPSL.graphAut (n := d) (K := K)) ^ 3 =
        CFSG.StandardType.AutPSL.graphAut (n := d) (K := K) := by
      rw [pow_succ, pow_two, CFSG.StandardType.AutPSL.graphAut_mul_self, one_mul]
    have hstep : fieldAut d K σ ^ 3 * CFSG.StandardType.AutPSL.graphAut (n := d) (K := K) ^ 3 =
        1 := by
      rw [← hcomm.mul_pow, hc3]
    rw [hg3] at hstep
    have hgs : CFSG.StandardType.AutPSL.graphAut (n := d) (K := K) ∈
        semilinearAutGroup d K := by
      rw [eq_inv_of_mul_eq_one_right hstep]
      exact inv_mem (pow_mem (fieldAut_mem_semilinearAutGroup σ) 3)
    have hdual : dualAut d K = (conjAut d K
        (SpecialLinearGroup.toGL (CFSG.StandardType.AutPSL.revSL (n := d) (K := K))))⁻¹ *
        CFSG.StandardType.AutPSL.graphAut (n := d) (K := K) := by
      rw [CFSG.StandardType.AutPSL.graphAut, ← mul_assoc, inv_mul_cancel, one_mul]
    apply CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.dualAut_not_mem_semilinearAutGroup
      (K := K) hd
    rw [hdual]
    exact mul_mem (inv_mem (linearAutGroup_le_semilinearAutGroup
      (conjAut_mem_linearAutGroup _))) hgs

end Aut

theorem LinAutDecomp3_holds : LinAutDecomp3 := by
  intro d K _ _ h2 hd β hβ
  exact linAutDecomp3_of_eq h2 hd _ (largeEvenSLGroup_eq_statedSL (K := K) d) β hβ

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

end
