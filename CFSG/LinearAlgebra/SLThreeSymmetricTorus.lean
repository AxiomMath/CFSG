module

public import CFSG.ClassicalInvolution.WeakCT.Torus
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.RankThree.CentralCover.LinearUnitaryFourGroupWitness
public import CFSG.ClassicalGroups.Unitary.SUnThreeLocalDefs

public section

namespace CFSG.LinearAlgebra

open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalInvolution.WeakCT CFSG.RankThree.CentralCover
open scoped MatrixGroups

variable {K : Type} [Field K]

private noncomputable def swap23 : GL (Fin 3) K where
  val := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
  inv := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private noncomputable def symChangeBasis (h2 : (2 : K) ≠ 0) : GL (Fin 3) K where
  val := !![1, 0, 1; 0, 1, 0; 1, 0, -1]
  inv := !![(2 : K)⁻¹, 0, (2 : K)⁻¹; 0, 1, 0; (2 : K)⁻¹, 0, -(2 : K)⁻¹]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h2, mul_inv_cancel₀ h2]
    all_goals field_simp
    all_goals norm_num
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h2, mul_inv_cancel₀ h2]
    all_goals field_simp
    all_goals norm_num

private noncomputable def diagTorusHom : Kˣ →* Matrix.SpecialLinearGroup (Fin 3) K :=
  ((slConjugation 3 K (swap23 (K := K))).toMonoidHom).comp
    ((blockSL K 3 2 0 (by omega)).comp (torusHom K))

private theorem coe_diagTorusHom (lam : Kˣ) :
    ((diagTorusHom (K := K) lam : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![((lam : K)), 0, 0; 0, 1, 0; 0, 0, (((lam⁻¹ : Kˣ) : K))] := by
  rw [diagTorusHom, MonoidHom.comp_apply, MonoidHom.comp_apply]
  change ((slConjugation 3 K (swap23 (K := K)) ((blockSL K 3 2 0 (by omega)) (torusHom K lam)) :
    Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
  rw [slConjugation_matrix, coe_blockSL_three_zero, coe_torusHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap23, Matrix.mul_apply, Fin.sum_univ_three]

noncomputable def symTorusMatHom (h2 : (2 : K) ≠ 0) : Kˣ →* Matrix.SpecialLinearGroup (Fin 3) K :=
  ((slConjugation 3 K (symChangeBasis (K := K) h2)).toMonoidHom).comp
    (diagTorusHom (K := K))

@[expose] noncomputable def symTorusA (lam : Kˣ) : K :=
  (((lam : K) + (((lam⁻¹ : Kˣ) : K))) / 2)

@[expose] noncomputable def symTorusB (lam : Kˣ) : K :=
  (((lam : K) - (((lam⁻¹ : Kˣ) : K))) / 2)

theorem coe_symTorusMatHom (h2 : (2 : K) ≠ 0) (lam : Kˣ) :
    ((symTorusMatHom (K := K) h2 lam : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![symTorusA lam, 0, symTorusB lam; 0, 1, 0; symTorusB lam, 0, symTorusA lam] := by
  rw [symTorusMatHom, MonoidHom.comp_apply]
  change ((slConjugation 3 K (symChangeBasis (K := K) h2) (diagTorusHom (K := K) lam) :
    Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
  rw [slConjugation_matrix, coe_diagTorusHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symChangeBasis, symTorusA, symTorusB, Matrix.mul_apply, Fin.sum_univ_three, h2]
  all_goals field_simp
  all_goals ring

private theorem symTorusA_inv (lam : Kˣ) : symTorusA (K := K) lam⁻¹ = symTorusA lam := by
  simp [symTorusA, add_comm]

private theorem symTorusB_inv (lam : Kˣ) : symTorusB (K := K) lam⁻¹ = -symTorusB lam := by
  simp [symTorusB]
  ring

@[expose] noncomputable def symTorusHom (h2 : (2 : K) ≠ 0) : Kˣ →* projectiveSL 3 K :=
  (proj 3 K).comp (symTorusMatHom (K := K) h2)

theorem symTorusHom_apply (h2 : (2 : K) ≠ 0) (lam : Kˣ) :
    symTorusHom (K := K) h2 lam = proj 3 K (symTorusMatHom (K := K) h2 lam) := rfl

private theorem symTorusMatHom_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (symTorusMatHom (K := K) h2) := by
  intro lam mu h
  have h' := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
  rw [coe_symTorusMatHom h2, coe_symTorusMatHom h2] at h'
  have h00 := congrFun (congrFun h' 0) 0
  have h02 := congrFun (congrFun h' 0) 2
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.zero_apply] at h00 h02
  have hA : symTorusA lam = symTorusA mu := h00
  have hB : symTorusB lam = symTorusB mu := h02
  apply Units.ext
  have hsum : (lam : K) = (mu : K) := by
    have h1 : symTorusA lam + symTorusB lam = (lam : K) := by
      simp [symTorusA, symTorusB]
      field_simp
      ring
    have h2 : symTorusA mu + symTorusB mu = (mu : K) := by
      simp [symTorusA, symTorusB]
      field_simp
      ring
    rw [← h1, ← h2, hA, hB]
  exact hsum

theorem symTorusHom_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (symTorusHom (K := K) h2) := by
  intro lam mu h
  have hmem : (symTorusMatHom (K := K) h2 lam)⁻¹ * symTorusMatHom (K := K) h2 mu ∈ scalars 3 K :=
    proj_eq_proj_iff.mp h
  have hmap : symTorusMatHom (K := K) h2 (lam⁻¹ * mu) =
      (symTorusMatHom (K := K) h2 lam)⁻¹ * symTorusMatHom (K := K) h2 mu := by
    rw [map_mul, map_inv]
  have hmem' : symTorusMatHom (K := K) h2 (lam⁻¹ * mu) ∈ scalars 3 K := by
    rw [hmap]
    exact hmem
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hmem'
  have hmid : (c : K) = 1 := by
    have hc' := hc
    rw [coe_symTorusMatHom h2] at hc'
    have h11 := congrFun (congrFun hc' 1) 1
    simp [Matrix.scalar_apply] at h11
    exact h11.symm
  have hone : symTorusMatHom (K := K) h2 (lam⁻¹ * mu) = 1 := by
    apply Subtype.ext
    rw [hc, hmid]
    simp [Matrix.scalar_apply]
  have hone' : symTorusMatHom (K := K) h2 (lam⁻¹ * mu) = symTorusMatHom (K := K) h2 1 := by
    simpa using hone
  have hprod : lam⁻¹ * mu = 1 := symTorusMatHom_injective h2 hone'
  exact inv_injective (mul_inv_eq_one.mp hprod)


@[expose] noncomputable def oddDiag₃SL : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨oddDiag₃ K, by rw [det_oddDiag₃]⟩

@[expose] noncomputable def oddDiag₂SL : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨oddDiag₂ K, by rw [det_oddDiag₂]⟩

theorem coe_oddDiag₃SL :
    ((oddDiag₃SL (K := K) : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oddDiag₃SL, oddDiag₃]

theorem coe_oddDiag₂SL :
    ((oddDiag₂SL (K := K) : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oddDiag₂SL, oddDiag₂]

private theorem symTorusMatHom_symm (h2 : (2 : K) ≠ 0) (lam : Kˣ) :
    (((symTorusMatHom (K := K) h2 lam : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)ᵀ) =
      ((symTorusMatHom (K := K) h2 lam : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := by
  rw [coe_symTorusMatHom h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem oddDiag₃SL_conj_symTorusMat (h2 : (2 : K) ≠ 0) (lam : Kˣ) :
    oddDiag₃SL (K := K) * symTorusMatHom (K := K) h2 lam * oddDiag₃SL (K := K) =
      symTorusMatHom (K := K) h2 lam⁻¹ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_symTorusMatHom h2 (lam := lam), coe_symTorusMatHom h2 (lam := lam⁻¹),
    coe_oddDiag₃SL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, symTorusA, symTorusB,
      symTorusA_inv, symTorusB_inv]
  all_goals ring

theorem oddDiag₂SL_conj_symTorusMat (h2 : (2 : K) ≠ 0) (lam : Kˣ) :
    oddDiag₂SL (K := K) * symTorusMatHom (K := K) h2 lam * oddDiag₂SL (K := K) =
      symTorusMatHom (K := K) h2 lam := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_symTorusMatHom h2 (lam := lam), coe_oddDiag₂SL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, symTorusA, symTorusB]

@[expose] noncomputable def d0Hom : Kˣ →* Matrix.SpecialLinearGroup (Fin 3) K :=
  (blockSL K 3 2 0 (by omega)).comp (torusHom K)

theorem coe_d0Hom (δ : Kˣ) :
    ((d0Hom (K := K) δ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![((δ : K)), 0, 0; 0, (((δ⁻¹ : Kˣ) : K)), 0; 0, 0, 1] := by
  rw [d0Hom, MonoidHom.comp_apply, coe_blockSL_three_zero, coe_torusHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem slConjugation_symTorusMat_of_diagonal (h2 : (2 : K) ≠ 0) {A : GL (Fin 3) K}
    {a0 a1 a2 : K} (hA : (A : Matrix (Fin 3) (Fin 3) K) = diagonal ![a0, a1, a2])
    (ha0 : a0 ≠ 0) (ha2 : a2 ≠ 0) (lam : Kˣ) :
    let δ : Kˣ := Units.mk0 (a0 / a2) (div_ne_zero ha0 ha2)
    slConjugation 3 K A (symTorusMatHom (K := K) h2 lam) =
      d0Hom (K := K) δ * symTorusMatHom (K := K) h2 lam * (d0Hom (K := K) δ)⁻¹ := by
  intro δ
  have ha1 : a1 ≠ 0 := by
    intro h1
    have hdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
      (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A) |>.ne_zero
    apply hdet
    rw [hA, Matrix.det_diagonal]
    simp [Fin.prod_univ_three, h1]
  let u0 : Kˣ := Units.mk0 a0 ha0
  let u1 : Kˣ := Units.mk0 a1 ha1
  let u2 : Kˣ := Units.mk0 a2 ha2
  have hAD : A = CFSG.ClassicalGroups.SUnThreeLocal.diagGL K 3 ![u0, u1, u2] := by
    apply Units.ext
    rw [hA, CFSG.ClassicalGroups.SUnThreeLocal.coe_diagGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u0, u1, u2]
  have hAinv : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![a0⁻¹, a1⁻¹, a2⁻¹] := by
    rw [hAD, ← map_inv, CFSG.ClassicalGroups.SUnThreeLocal.coe_diagGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u0, u1, u2]
  apply Subtype.ext
  rw [show (d0Hom (K := K) δ)⁻¹ = d0Hom (K := K) δ⁻¹ by rw [map_inv]]
  rw [slConjugation_matrix, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_d0Hom, coe_d0Hom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hA, hAinv, coe_symTorusMatHom h2, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal, δ, symTorusA, symTorusB]
  all_goals field_simp
  all_goals ring

theorem fieldAut_symTorusHom (h2 : (2 : K) ≠ 0) (σ : K ≃+* K) (lam : Kˣ) :
    fieldAut 3 K σ (symTorusHom (K := K) h2 lam) =
      symTorusHom (K := K) h2 (Units.map σ.toMulEquiv lam) := by
  rw [symTorusHom_apply, fieldAut_proj, symTorusHom_apply]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    coe_symTorusMatHom h2, coe_symTorusMatHom h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symTorusA, symTorusB, map_add, map_mul, map_inv₀, map_div₀, map_ofNat]

theorem dualAut_symTorusHom (h2 : (2 : K) ≠ 0) (lam : Kˣ) :
    dualAut 3 K (symTorusHom (K := K) h2 lam) =
      symTorusHom (K := K) h2 lam⁻¹ := by
  rw [symTorusHom_apply, dualAut_proj, symTorusHom_apply]
  congr 1
  rw [show (symTorusMatHom (K := K) h2 lam)⁻¹ = symTorusMatHom (K := K) h2 lam⁻¹ by
    rw [map_inv]]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, symTorusMatHom_symm]

theorem fieldAut_d0Hom (σ : K ≃+* K) (δ : Kˣ) :
    fieldAut 3 K σ (proj 3 K (d0Hom (K := K) δ)) =
      proj 3 K (d0Hom (K := K) (Units.map σ.toMulEquiv δ)) := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    coe_d0Hom, coe_d0Hom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [map_inv₀]

theorem dualAut_d0Hom (δ : Kˣ) :
    dualAut 3 K (proj 3 K (d0Hom (K := K) δ)) =
      proj 3 K (d0Hom (K := K) δ⁻¹) := by
  rw [dualAut_proj]
  congr 1
  rw [show (d0Hom (K := K) δ)⁻¹ = d0Hom (K := K) δ⁻¹ by rw [map_inv]]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, coe_d0Hom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem conjAut_d0Hom_of_diagonal {A : GL (Fin 3) K} {a0 a1 a2 : K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K) = diagonal ![a0, a1, a2]) (δ : Kˣ) :
    conjAut 3 K A (proj 3 K (d0Hom (K := K) δ)) =
      proj 3 K (d0Hom (K := K) δ) := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [slConjugation_matrix, coe_d0Hom]
  have hcomm : (A : Matrix (Fin 3) (Fin 3) K) *
      (!![((δ : K)), 0, 0; 0, (((δ⁻¹ : Kˣ) : K)), 0; 0, 0, 1] :
        Matrix (Fin 3) (Fin 3) K) =
      (!![((δ : K)), 0, 0; 0, (((δ⁻¹ : Kˣ) : K)), 0; 0, 0, 1] :
        Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hA, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal]
    all_goals ring
  calc (A : Matrix (Fin 3) (Fin 3) K) *
        (!![((δ : K)), 0, 0; 0, (((δ⁻¹ : Kˣ) : K)), 0; 0, 0, 1] :
          Matrix (Fin 3) (Fin 3) K) *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = (!![((δ : K)), 0, 0; 0, (((δ⁻¹ : Kˣ) : K)), 0; 0, 0, 1] :
          Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [hcomm]
    _ = (!![((δ : K)), 0, 0; 0, (((δ⁻¹ : Kˣ) : K)), 0; 0, 0, 1] :
          Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.mul_assoc, show (A : Matrix (Fin 3) (Fin 3) K) *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one], Matrix.mul_one]

end CFSG.LinearAlgebra

end
