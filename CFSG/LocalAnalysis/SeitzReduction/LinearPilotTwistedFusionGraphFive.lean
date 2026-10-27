module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionGraphNonalt
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionField

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (rootElt rootElt_of_ne coe_rootElt_of_ne
  rootElt_add rootElt_zero rootElt_mul_comm)
open CFSG.ComponentClassification.RankTwoHypIIY (commutator_eq_self_of_isSimpleGroup)

variable {K : Type} [Field K] {n : ℕ}

theorem isInvolutionClass_two_proj_rootElt_mul_rootElt [CharP K 2] {p q p' q' : Fin n}
    (hpq : p ≠ q) (hpq' : p' ≠ q') (hqp' : q ≠ p') (hq'p : q' ≠ p) (hpp' : p ≠ p')
    (hqq' : q ≠ q') :
    IsInvolutionClass 2 (proj n K (rootElt p q 1 * rootElt p' q' 1)) := by
  have hcomm : rootElt p q (1 : K) * rootElt p' q' 1 = rootElt p' q' 1 * rootElt p q 1 :=
    rootElt_mul_comm hqp' hq'p 1 1
  refine ⟨rootElt p q 1 * rootElt p' q' 1, rfl, ?_, ?_⟩
  · calc rootElt p q (1 : K) * rootElt p' q' 1 * (rootElt p q 1 * rootElt p' q' 1) =
        rootElt p q 1 * rootElt p q 1 * (rootElt p' q' 1 * rootElt p' q' 1) := by
          rw [mul_assoc, ← mul_assoc (rootElt p' q' 1), ← hcomm]
          group
      _ = 1 := by
          rw [← rootElt_add, ← rootElt_add, CharTwo.add_self_eq_zero, rootElt_zero, rootElt_zero,
            one_mul]
  · have hprod : single p q (1 : K) * single p' q' 1 = 0 := by simp [hqp']
    have hsub : ((rootElt p q (1 : K) * rootElt p' q' 1 : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) - 1 = single p q 1 + single p' q' 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_rootElt_of_ne hpq, coe_rootElt_of_ne hpq',
        transvection, transvection, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
        Matrix.mul_one, hprod]
      abel
    rw [hsub]
    have hcol₁ : (single p q (1 : K) + single p' q' 1).col q = Pi.single p 1 := by
      ext i
      by_cases hi : i = p
      · subst hi
        simp [col_apply, Ne.symm hqq']
      · simp [col_apply, hi, Ne.symm hi, Ne.symm hqq']
    have hcol₂ : (single p q (1 : K) + single p' q' 1).col q' = Pi.single p' 1 := by
      ext i
      by_cases hi : i = p'
      · subst hi
        simp [col_apply, hqq']
      · simp [col_apply, hi, Ne.symm hi, hqq']
    refine rank_eq_two_of_col_mem (linearIndependent_pi_single_pair hpp') (fun j => ?_) hcol₁ hcol₂
    by_cases hj₁ : j = q
    · rw [hj₁, hcol₁]
      exact Submodule.subset_span (Set.mem_insert _ _)
    · by_cases hj₂ : j = q'
      · rw [hj₂, hcol₂]
        exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
      · have h0 : (single p q (1 : K) + single p' q' 1).col j = 0 := by
          ext i
          simp [col_apply, Ne.symm hj₁, Ne.symm hj₂]
        rw [h0]
        exact Submodule.zero_mem _

section Alt

@[expose] def altPermSL : alternatingGroup (Fin 5) →* SpecialLinearGroup (Fin 5) K where
  toFun σ := ⟨Matrix.permMatrixHom (σ : Equiv.Perm (Fin 5)), by
    rw [Matrix.permMatrixHom_apply, Matrix.det_permutation, Equiv.Perm.sign_inv,
      Equiv.Perm.mem_alternatingGroup.mp σ.2]
    simp⟩
  map_one' := by
    apply Subtype.ext
    change Matrix.permMatrixHom ((1 : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = 1
    rw [OneMemClass.coe_one, map_one]
  map_mul' σ τ := by
    apply Subtype.ext
    change Matrix.permMatrixHom ((σ * τ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
      Matrix.permMatrixHom (σ : Equiv.Perm (Fin 5)) * Matrix.permMatrixHom (τ : Equiv.Perm (Fin 5))
    rw [Subgroup.coe_mul, map_mul]

theorem coe_altPermSL (σ : alternatingGroup (Fin 5)) :
    ((altPermSL σ : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ((σ : Equiv.Perm (Fin 5))⁻¹).permMatrix K :=
  rfl

theorem altPermSL_inv_transpose (σ : alternatingGroup (Fin 5)) :
    ((altPermSL σ : SpecialLinearGroup (Fin 5) K)⁻¹).transpose = altPermSL σ := by
  rw [← map_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, coe_altPermSL, coe_altPermSL,
    Matrix.transpose_permMatrix, Subgroup.coe_inv, inv_inv]

theorem isPerfect_alternatingGroup_fin_five : Group.IsPerfect (alternatingGroup (Fin 5)) :=
  ⟨commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)⟩

@[expose] def fusionTau : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    rfl⟩

theorem coe_altPermSL_fusionTau :
    ((altPermSL fusionTau : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1] := by
  rw [coe_altPermSL]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Alt

section Five

variable [CharP K 2]

theorem fusionM5_transpose_mul :
    (!![1, 0, 0, 1, 1; 1, 1, 0, 1, 1; 0, 1, 0, 1, 1; 0, 0, 1, 1, 1; 0, 0, 1, 0, 1] :
        Matrix (Fin 5) (Fin 5) K)ᵀ *
      !![1, 0, 0, 1, 1; 1, 1, 0, 1, 1; 0, 1, 0, 1, 1; 0, 0, 1, 1, 1; 0, 0, 1, 0, 1] =
      !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1] := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_five] <;>
    simp [h2]

theorem det_fusionM5 :
    (!![1, 0, 0, 1, 1; 1, 1, 0, 1, 1; 0, 1, 0, 1, 1; 0, 0, 1, 1, 1; 0, 0, 1, 0, 1] :
      Matrix (Fin 5) (Fin 5) K).det = 1 := by
  have h := congrArg Matrix.det (fusionM5_transpose_mul (K := K))
  rw [det_mul, det_transpose, ← coe_altPermSL_fusionTau, (altPermSL fusionTau).2, ← sq] at h
  set d := (!![1, 0, 0, 1, 1; 1, 1, 0, 1, 1; 0, 1, 0, 1, 1; 0, 0, 1, 1, 1; 0, 0, 1, 0, 1] :
    Matrix (Fin 5) (Fin 5) K).det
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : (d + 1) ^ 2 = 0 := by linear_combination h + (d + 1) * h22
  have h2 : d + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h1
  rwa [CharTwo.add_eq_zero] at h2

@[expose] def fusionM5 : SpecialLinearGroup (Fin 5) K :=
  ⟨!![1, 0, 0, 1, 1; 1, 1, 0, 1, 1; 0, 1, 0, 1, 1; 0, 0, 1, 1, 1; 0, 0, 1, 0, 1], det_fusionM5⟩

theorem fusionM5_inv_transpose_mul :
    ((fusionM5 : SpecialLinearGroup (Fin 5) K)⁻¹).transpose * altPermSL fusionTau = fusionM5 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  set N5 : Matrix (Fin 5) (Fin 5) K :=
    !![0, 1, 1, 0, 0; 1, 1, 0, 0, 0; 1, 1, 1, 1, 0; 0, 0, 0, 1, 1; 1, 1, 1, 1, 1] with hN5
  have hMN : ((fusionM5 : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * N5 = 1 := by
    change !![1, 0, 0, 1, 1; 1, 1, 0, 1, 1; 0, 1, 0, 1, 1; 0, 0, 1, 1, 1; 0, 0, 1, 0, 1] * N5 = 1
    rw [hN5]
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_five] <;>
      simp [h2]
  have hinv : ((fusionM5⁻¹ : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = N5 := by
    calc ((fusionM5⁻¹ : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
        = ((fusionM5⁻¹ : SpecialLinearGroup (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
            ((fusionM5 : SpecialLinearGroup (Fin 5) K) * N5) := by rw [hMN, Matrix.mul_one]
      _ = N5 := by
          rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose, hinv,
    coe_altPermSL_fusionTau, hN5]
  change _ = !![1, 0, 0, 1, 1; 1, 1, 0, 1, 1; 0, 1, 0, 1, 1; 0, 0, 1, 1, 1; 0, 0, 1, 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_five] <;> simp

theorem altPermSL_fusionTau_eq :
    (altPermSL fusionTau : SpecialLinearGroup (Fin 5) K) =
      (rootElt 1 0 1 * rootElt 3 2 1) * (rootElt 0 1 1 * rootElt 2 3 1) *
        (rootElt 1 0 1 * rootElt 3 2 1) := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hg : ((rootElt (1 : Fin 5) 0 (1 : K) * rootElt 3 2 1 : SpecialLinearGroup (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) =
      !![1, 0, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_rootElt_of_ne (by decide),
      coe_rootElt_of_ne (by decide)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_five] <;>
      simp [transvection, one_apply]
  have hX : ((rootElt (0 : Fin 5) 1 (1 : K) * rootElt 2 3 1 : SpecialLinearGroup (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) =
      !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_rootElt_of_ne (by decide),
      coe_rootElt_of_ne (by decide)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_five] <;>
      simp [transvection, one_apply]
  apply Subtype.ext
  rw [coe_altPermSL_fusionTau, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, hg, hX]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_five] <;>
    simp [h2]

end Five

theorem perfectTwistedFusionIn_dualAut_of_five_le [CharP K 2] (hn : 5 ≤ n) :
    PerfectTwistedFusionIn (dualAut n K) (IsInvolutionClass 2) := by
  have := isPerfect_alternatingGroup_fin_five
  set φ : alternatingGroup (Fin 5) →* projectiveSL n K :=
    (proj n K).comp ((cornerSL hn).comp (altPermSL (K := K))) with hφ
  have hfix : ∀ p ∈ φ.range, dualAut n K p = p := by
    rintro _ ⟨σ, rfl⟩
    rw [hφ, MonoidHom.comp_apply, MonoidHom.comp_apply, dualAut_proj_cornerSL,
      altPermSL_inv_transpose]
  have hfus : (dualAut n K (proj n K (cornerSL hn fusionM5)))⁻¹ * proj n K (cornerSL hn fusionM5) =
      φ fusionTau := by
    rw [dualAut_proj_cornerSL, ← map_inv, ← map_mul, ← map_inv, ← map_mul, hφ,
      MonoidHom.comp_apply, MonoidHom.comp_apply]
    congr 2
    rw [inv_mul_eq_iff_eq_mul]
    exact (fusionM5_inv_transpose_mul (K := K)).symm
  set a : Fin n := ⟨0, by omega⟩ with ha
  set b : Fin n := ⟨1, by omega⟩ with hb
  set c : Fin n := ⟨2, by omega⟩ with hc
  set d : Fin n := ⟨3, by omega⟩ with hd
  have hcl : IsInvolutionClass 2 (φ fusionTau) := by
    have hg : cornerSL hn (rootElt (1 : Fin 5) 0 (1 : K) * rootElt 3 2 1) =
        rootElt b a 1 * rootElt d c 1 := by
      rw [map_mul, cornerSL_rootElt hn (by decide), cornerSL_rootElt hn (by decide)]
      rfl
    have hX : cornerSL hn (rootElt (0 : Fin 5) 1 (1 : K) * rootElt 2 3 1) =
        rootElt a b 1 * rootElt c d 1 := by
      rw [map_mul, cornerSL_rootElt hn (by decide), cornerSL_rootElt hn (by decide)]
      rfl
    have hgg : (rootElt b a (1 : K) * rootElt d c 1)⁻¹ = rootElt b a 1 * rootElt d c 1 := by
      have hcomm : rootElt b a (1 : K) * rootElt d c 1 = rootElt d c 1 * rootElt b a 1 :=
        rootElt_mul_comm (by simp [ha, hd, Fin.ext_iff]) (by simp [hb, hc, Fin.ext_iff]) 1 1
      rw [_root_.mul_inv_rev, ← LinearPilot.rootElt_neg_eq_inv, ← LinearPilot.rootElt_neg_eq_inv,
        CharTwo.neg_eq, hcomm]
    have heq : φ fusionTau = LinearFlag.conjAut n K (SpecialLinearGroup.toGL
        (rootElt b a 1 * rootElt d c 1)) (proj n K (rootElt a b 1 * rootElt c d 1)) := by
      rw [conjAut_toGL, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hgg, hφ,
        MonoidHom.comp_apply, MonoidHom.comp_apply, altPermSL_fusionTau_eq,
        map_mul (cornerSL hn), map_mul (cornerSL hn), hg, hX]
    rw [heq]
    exact (isInvolutionClass_two_proj_rootElt_mul_rootElt (by simp [ha, hb, Fin.ext_iff])
      (by simp [hc, hd, Fin.ext_iff]) (by simp [hb, hc, Fin.ext_iff])
      (by simp [hd, ha, Fin.ext_iff]) (by simp [ha, hc, Fin.ext_iff])
      (by simp [hb, hd, Fin.ext_iff])).conjAut _
  refine ⟨proj n K (cornerSL hn fusionM5), φ fusionTau, hcl.ne_one two_ne_zero, hfus, hcl,
    φ.range, commutator_range_eq_range_of_isPerfect φ, ⟨fusionTau, rfl⟩, hfix⟩

end CFSG.SeitzReduction.LinearPilot
