module

public import CFSG.ClassicalInvolution.Q3.Q3ZACalc

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups
open Matrix

@[expose] noncomputable def tauMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F3 :=
  Matrix.diagonal (sgn F3)

theorem sgn_mul_sgn (a : Fin 2 ⊕ Fin 2) : sgn F3 a * sgn F3 a = 1 := by
  rcases a with i | i <;> simp

theorem tauMat_mul_self : tauMat * tauMat = 1 := by
  rw [tauMat, Matrix.diagonal_mul_diagonal]
  have h : (fun i => sgn F3 i * sgn F3 i) = fun _ => (1 : F3) := funext sgn_mul_sgn
  rw [h, Matrix.diagonal_one]

theorem tauMat_transpose : tauMatᵀ = tauMat := Matrix.diagonal_transpose _

theorem tauMat_mul_mul (Z : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F3) :
    tauMat * (tauMat * Z) = Z := by
  rw [← Matrix.mul_assoc, tauMat_mul_self, Matrix.one_mul]

theorem tauMat_gram : tauMat * gram F3 2 * tauMat = -gram F3 2 := by
  ext a b
  rw [tauMat, Matrix.mul_diagonal, Matrix.diagonal_mul, Models.SymplecticPairs.gram_apply,
    Matrix.neg_apply, Models.SymplecticPairs.gram_apply]
  rcases a with i | i <;> rcases b with j | j <;> by_cases h : j = i <;> simp [par, sgn, h]

theorem tau_conj_symp (x : StatedSp 2 F3) :
    (tauMat * mat 2 F3 x * tauMat)ᵀ * gram F3 2 * (tauMat * mat 2 F3 x * tauMat) = gram F3 2 := by
  have h1 := mat_transpose_mul_gram_mul x
  have h2 := tauMat_gram
  calc (tauMat * mat 2 F3 x * tauMat)ᵀ * gram F3 2 * (tauMat * mat 2 F3 x * tauMat)
      = tauMat * (mat 2 F3 x)ᵀ * (tauMat * gram F3 2 * tauMat) * mat 2 F3 x * tauMat := by
        simp only [Matrix.transpose_mul, tauMat_transpose, Matrix.mul_assoc]
    _ = tauMat * ((mat 2 F3 x)ᵀ * (-gram F3 2) * mat 2 F3 x) * tauMat := by
        rw [h2]
        simp only [Matrix.mul_assoc]
    _ = -(tauMat * ((mat 2 F3 x)ᵀ * gram F3 2 * mat 2 F3 x) * tauMat) := by
        simp only [Matrix.mul_neg, Matrix.neg_mul]
    _ = -(tauMat * gram F3 2 * tauMat) := by rw [h1]
    _ = gram F3 2 := by rw [h2, neg_neg]

@[expose] noncomputable def tauFun (x : StatedSp 2 F3) : StatedSp 2 F3 :=
  ofSymplecticMat (tauMat * mat 2 F3 x * tauMat) (tau_conj_symp x)

theorem mat_tauFun (x : StatedSp 2 F3) : mat 2 F3 (tauFun x) = tauMat * mat 2 F3 x * tauMat :=
  rfl

@[expose] noncomputable def tauHom : StatedSp 2 F3 →* StatedSp 2 F3 where
  toFun := tauFun
  map_one' := mat_injective (by
    rw [mat_tauFun, map_one, Matrix.mul_one, tauMat_mul_self])
  map_mul' x y := mat_injective (by
    rw [mat_tauFun, map_mul, map_mul, mat_tauFun, mat_tauFun]
    simp only [Matrix.mul_assoc, tauMat_mul_mul])

theorem tauHom_apply (x : StatedSp 2 F3) : tauHom x = tauFun x := rfl

theorem tauHom_tauHom (x : StatedSp 2 F3) : tauHom (tauHom x) = x := by
  refine mat_injective ?_
  rw [tauHom_apply, tauHom_apply, mat_tauFun, mat_tauFun]
  simp only [Matrix.mul_assoc, tauMat_mul_mul, tauMat_mul_self, Matrix.mul_one]

theorem tauHom_injective : Function.Injective tauHom := fun x y h => by
  rw [← tauHom_tauHom x, h, tauHom_tauHom]

theorem tauHom_surjective : Function.Surjective tauHom := fun x => ⟨tauHom x, tauHom_tauHom x⟩

theorem tau_mulVec_single (j : Fin 2 ⊕ Fin 2) :
    tauMat *ᵥ (Pi.single j 1 : V4) = sgn F3 j • (Pi.single j 1 : V4) := by
  funext i
  rw [tauMat, Matrix.mulVec_diagonal]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

theorem tau_e0 : tauMat *ᵥ bE0 = bE0 := by
  rw [tau_mulVec_single]
  simp

theorem tau_e1 : tauMat *ᵥ bE1 = bE1 := by
  rw [tau_mulVec_single]
  simp

theorem tau_f0 : tauMat *ᵥ bF0 = -bF0 := by
  rw [tau_mulVec_single]
  simp

theorem tau_f1 : tauMat *ᵥ bF1 = -bF1 := by
  rw [tau_mulVec_single]
  simp

@[expose] noncomputable def tauSL (x : SL(2, F3)) : SL(2, F3) :=
  mkSL !![(x : Matrix (Fin 2) (Fin 2) F3) 0 0, -(x : Matrix (Fin 2) (Fin 2) F3) 0 1;
    -(x : Matrix (Fin 2) (Fin 2) F3) 1 0, (x : Matrix (Fin 2) (Fin 2) F3) 1 1] (by
    rw [Matrix.det_fin_two_of]
    have h := x.2
    rw [Matrix.det_fin_two] at h
    linear_combination h)

theorem tauSL_apply (x : SL(2, F3)) :
    ((tauSL x : SL(2, F3)) : Matrix (Fin 2) (Fin 2) F3) =
      !![(x : Matrix (Fin 2) (Fin 2) F3) 0 0, -(x : Matrix (Fin 2) (Fin 2) F3) 0 1;
        -(x : Matrix (Fin 2) (Fin 2) F3) 1 0, (x : Matrix (Fin 2) (Fin 2) F3) 1 1] :=
  rfl

theorem tauSL_tauSL (x : SL(2, F3)) : tauSL (tauSL x) = x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tauSL_apply]

theorem tauSL_surjective : Function.Surjective tauSL := fun x => ⟨tauSL x, tauSL_tauSL x⟩

theorem tauSL_eq (x : SL(2, F3)) :
    ((tauSL x : SL(2, F3)) : Matrix (Fin 2) (Fin 2) F3) =
      !![1, 0; 0, -1] * (x : Matrix (Fin 2) (Fin 2) F3) * !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tauSL_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem tauHom_lb0 (x : SL(2, F3)) : tauHom (longBlock F3 2 0 x) = longBlock F3 2 0 (tauSL x) := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_
  · simp only [tauHom_apply, mat_tauFun, ← Matrix.mulVec_mulVec, tau_e0, lb_mulVec_inl 0 x,
      lb_mulVec_inl 0 (tauSL x), Matrix.mulVec_add, Matrix.mulVec_smul, tau_f0, tauSL_apply]
    simp
  · simp only [tauHom_apply, mat_tauFun, ← Matrix.mulVec_mulVec, tau_e1,
      lb_mulVec_other 0 x (j := Sum.inl 1) (by simp [coords]),
      lb_mulVec_other 0 (tauSL x) (j := Sum.inl 1) (by simp [coords])]
  · simp only [tauHom_apply, mat_tauFun, ← Matrix.mulVec_mulVec, tau_f0, lb_mulVec_inr 0 x,
      lb_mulVec_inr 0 (tauSL x), Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_neg, tau_e0,
      tauSL_apply]
    simp
    module
  · simp only [tauHom_apply, mat_tauFun, ← Matrix.mulVec_mulVec, tau_f1,
      lb_mulVec_other 0 x (j := Sum.inr 1) (by simp [coords]),
      lb_mulVec_other 0 (tauSL x) (j := Sum.inr 1) (by simp [coords]), Matrix.mulVec_neg]
    simp

theorem tauHom_lb1 (x : SL(2, F3)) : tauHom (longBlock F3 2 1 x) = longBlock F3 2 1 (tauSL x) := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_
  · simp only [tauHom_apply, mat_tauFun, ← Matrix.mulVec_mulVec, tau_e0,
      lb_mulVec_other 1 x (j := Sum.inl 0) (by simp [coords]),
      lb_mulVec_other 1 (tauSL x) (j := Sum.inl 0) (by simp [coords])]
  · simp only [tauHom_apply, mat_tauFun, ← Matrix.mulVec_mulVec, tau_e1, lb_mulVec_inl 1 x,
      lb_mulVec_inl 1 (tauSL x), Matrix.mulVec_add, Matrix.mulVec_smul, tau_f1, tauSL_apply]
    simp
  · simp only [tauHom_apply, mat_tauFun, ← Matrix.mulVec_mulVec, tau_f0,
      lb_mulVec_other 1 x (j := Sum.inr 0) (by simp [coords]),
      lb_mulVec_other 1 (tauSL x) (j := Sum.inr 0) (by simp [coords]), Matrix.mulVec_neg]
    simp
  · simp only [tauHom_apply, mat_tauFun, ← Matrix.mulVec_mulVec, tau_f1, lb_mulVec_inr 1 x,
      lb_mulVec_inr 1 (tauSL x), Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_neg, tau_e1,
      tauSL_apply]
    simp
    module

theorem exists_aut_of_conj (G : GL (Fin 2) F3) :
    ∃ ν : StatedSp 2 F3 →* StatedSp 2 F3, Function.Bijective ν ∧
      (∀ x y : SL(2, F3), (y : Matrix (Fin 2) (Fin 2) F3) =
          (G : Matrix (Fin 2) (Fin 2) F3) * (x : Matrix (Fin 2) (Fin 2) F3) *
            ((G⁻¹ : GL (Fin 2) F3) : Matrix (Fin 2) (Fin 2) F3) →
        ν (longBlock F3 2 0 x) = longBlock F3 2 0 y) ∧
      ∃ f : SL(2, F3) → SL(2, F3), Function.Surjective f ∧
        ∀ x : SL(2, F3), ν (longBlock F3 2 1 x) = longBlock F3 2 1 (f x) := by
  have hunit : IsUnit (G : Matrix (Fin 2) (Fin 2) F3).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 G.isUnit
  have hdet : (G : Matrix (Fin 2) (Fin 2) F3).det = 1 ∨
      (G : Matrix (Fin 2) (Fin 2) F3).det = -1 := by
    rcases eq_zero_or_one_or_neg_one_f3 (G : Matrix (Fin 2) (Fin 2) F3).det with h | h | h
    · exact absurd h hunit.ne_zero
    · exact Or.inl h
    · exact Or.inr h
  rcases hdet with h1 | h1
  ·
    let g : SL(2, F3) := ⟨(G : Matrix (Fin 2) (Fin 2) F3), h1⟩
    refine ⟨(MulAut.conj (longBlock F3 2 0 g)).toMonoidHom, (MulAut.conj _).bijective, ?_, ?_⟩
    · intro x y hy
      have hyg : y = g * x * g⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        refine Subtype.ext ?_
        show (y : Matrix (Fin 2) (Fin 2) F3) * (G : Matrix (Fin 2) (Fin 2) F3) =
          (G : Matrix (Fin 2) (Fin 2) F3) * (x : Matrix (Fin 2) (Fin 2) F3)
        rw [hy, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      show longBlock F3 2 0 g * longBlock F3 2 0 x * (longBlock F3 2 0 g)⁻¹ = longBlock F3 2 0 y
      rw [hyg, map_mul, map_mul, map_inv]
    · refine ⟨id, Function.surjective_id, fun x => ?_⟩
      show longBlock F3 2 0 g * longBlock F3 2 1 x * (longBlock F3 2 0 g)⁻¹ = longBlock F3 2 1 x
      exact mul_inv_eq_iff_eq_mul.2
        (commute_longBlock_longBlock (zero_ne_one : (0 : Fin 2) ≠ 1) g x).eq
  ·
    have hD : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F3).det = -1 := by
      rw [Matrix.det_fin_two_of]
      ring
    let g : SL(2, F3) := ⟨(G : Matrix (Fin 2) (Fin 2) F3) * !![1, 0; 0, -1], by
      rw [Matrix.det_mul, h1, hD]
      ring⟩
    have hDD : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F3) * !![1, 0; 0, -1] = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨(MulAut.conj (longBlock F3 2 0 g)).toMonoidHom.comp tauHom,
      (MulAut.conj _).bijective.comp ⟨tauHom_injective, tauHom_surjective⟩, ?_, ?_⟩
    · intro x y hy
      have hyg : y = g * tauSL x * g⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        refine Subtype.ext ?_
        show (y : Matrix (Fin 2) (Fin 2) F3) *
            ((G : Matrix (Fin 2) (Fin 2) F3) * !![1, 0; 0, -1]) =
          (G : Matrix (Fin 2) (Fin 2) F3) * !![1, 0; 0, -1] *
            ((tauSL x : SL(2, F3)) : Matrix (Fin 2) (Fin 2) F3)
        rw [hy, tauSL_eq]
        calc (G : Matrix (Fin 2) (Fin 2) F3) * (x : Matrix (Fin 2) (Fin 2) F3) *
              ((G⁻¹ : GL (Fin 2) F3) : Matrix (Fin 2) (Fin 2) F3) *
              ((G : Matrix (Fin 2) (Fin 2) F3) * !![1, 0; 0, -1])
            = (G : Matrix (Fin 2) (Fin 2) F3) * (x : Matrix (Fin 2) (Fin 2) F3) *
              (((G⁻¹ : GL (Fin 2) F3) : Matrix (Fin 2) (Fin 2) F3) *
                (G : Matrix (Fin 2) (Fin 2) F3)) * !![1, 0; 0, -1] := by
              simp only [Matrix.mul_assoc]
          _ = (G : Matrix (Fin 2) (Fin 2) F3) * (x : Matrix (Fin 2) (Fin 2) F3) *
              !![1, 0; 0, -1] := by rw [Units.inv_mul, Matrix.mul_one]
          _ = (G : Matrix (Fin 2) (Fin 2) F3) * (!![1, 0; 0, -1] * !![1, 0; 0, -1]) *
              (x : Matrix (Fin 2) (Fin 2) F3) * !![1, 0; 0, -1] := by
              rw [hDD, Matrix.mul_one]
          _ = (G : Matrix (Fin 2) (Fin 2) F3) * !![1, 0; 0, -1] *
              (!![1, 0; 0, -1] * (x : Matrix (Fin 2) (Fin 2) F3) * !![1, 0; 0, -1]) := by
              simp only [Matrix.mul_assoc]
      show longBlock F3 2 0 g * tauHom (longBlock F3 2 0 x) * (longBlock F3 2 0 g)⁻¹ =
        longBlock F3 2 0 y
      rw [tauHom_lb0, hyg, map_mul, map_mul, map_inv]
    · refine ⟨tauSL, tauSL_surjective, fun x => ?_⟩
      show longBlock F3 2 0 g * tauHom (longBlock F3 2 1 x) * (longBlock F3 2 0 g)⁻¹ =
        longBlock F3 2 1 (tauSL x)
      rw [tauHom_lb1]
      exact mul_inv_eq_iff_eq_mul.2
        (commute_longBlock_longBlock (zero_ne_one : (0 : Fin 2) ≠ 1) g (tauSL x)).eq

end CFSG.ClassicalInvolution.Q3.Q3ZA
