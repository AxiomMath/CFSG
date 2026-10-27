module

public import CFSG.GH74.GLS.IVK.Proofs2.Std44
public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.PGL2TorusCentralizer

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank
  CFSG.RankThree.CentralCover Matrix
open scoped commutatorElement

namespace LinGenAux

section Blocks

variable {F : Type} [Field F]

@[expose] def blk₃ (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

@[expose] def blk₂ (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 0 0, 0, A 0 1; 0, 1, 0; A 1 0, 0, A 1 1]

theorem blk₃_mul (A B : Matrix (Fin 2) (Fin 2) F) : blk₃ (A * B) = blk₃ A * blk₃ B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk₃, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blk₂_mul (A B : Matrix (Fin 2) (Fin 2) F) : blk₂ (A * B) = blk₂ A * blk₂ B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk₂, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blk₃_one : blk₃ (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk₃]

theorem blk₂_one : blk₂ (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk₂]

theorem det_blk₃ (A : Matrix (Fin 2) (Fin 2) F) : (blk₃ A).det = A.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [blk₃]

theorem det_blk₂ (A : Matrix (Fin 2) (Fin 2) F) : (blk₂ A).det = A.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [blk₂]

variable (F) in
@[expose] def β₃ : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 3) F where
  toFun A := ⟨blk₃ (A : Matrix (Fin 2) (Fin 2) F), (det_blk₃ _).trans A.2⟩
  map_one' := Subtype.ext blk₃_one
  map_mul' A B := Subtype.ext (blk₃_mul (A : Matrix (Fin 2) (Fin 2) F) B)

variable (F) in
@[expose] def β₂ : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 3) F where
  toFun A := ⟨blk₂ (A : Matrix (Fin 2) (Fin 2) F), (det_blk₂ _).trans A.2⟩
  map_one' := Subtype.ext blk₂_one
  map_mul' A B := Subtype.ext (blk₂_mul (A : Matrix (Fin 2) (Fin 2) F) B)

theorem coe_β₃ (A : SpecialLinearGroup (Fin 2) F) :
    ((β₃ F A : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blk₃ (A : Matrix _ _ F) :=
  rfl

theorem coe_β₂ (A : SpecialLinearGroup (Fin 2) F) :
    ((β₂ F A : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blk₂ (A : Matrix _ _ F) :=
  rfl

theorem β₃_injective : Function.Injective (β₃ F) := by
  intro A B h
  have h' := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_β₃] at h'
  ext i j
  have := congrFun (congrFun h' (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [blk₃] using this

theorem β₂_injective : Function.Injective (β₂ F) := by
  intro A B h
  have h' := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_β₂] at h'
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blk₂] using congrFun (congrFun h' 0) 0
  · simpa [blk₂] using congrFun (congrFun h' 0) 2
  · simpa [blk₂] using congrFun (congrFun h' 2) 0
  · simpa [blk₂] using congrFun (congrFun h' 2) 2

open SpecialLinearGroup in
theorem β₃_transvection_01 (c : F) :
    β₃ F (transvection (show (0 : Fin 2) ≠ 1 by decide) c) =
      transvection (show (0 : Fin 3) ≠ 1 by decide) c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_β₃, blk₃, transvection_coe]

open SpecialLinearGroup in
theorem β₃_transvection_10 (c : F) :
    β₃ F (transvection (show (1 : Fin 2) ≠ 0 by decide) c) =
      transvection (show (1 : Fin 3) ≠ 0 by decide) c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_β₃, blk₃, transvection_coe]

open SpecialLinearGroup in
theorem β₂_transvection_01 (c : F) :
    β₂ F (transvection (show (0 : Fin 2) ≠ 1 by decide) c) =
      transvection (show (0 : Fin 3) ≠ 2 by decide) c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_β₂, blk₂, transvection_coe]

open SpecialLinearGroup in
theorem β₂_transvection_10 (c : F) :
    β₂ F (transvection (show (1 : Fin 2) ≠ 0 by decide) c) =
      transvection (show (2 : Fin 3) ≠ 0 by decide) c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_β₂, blk₂, transvection_coe]

theorem closure_β_eq_top :
    Subgroup.closure (((β₃ F).range : Set (SpecialLinearGroup (Fin 3) F)) ∪
      ((β₂ F).range : Set (SpecialLinearGroup (Fin 3) F))) = ⊤ := by
  set H := Subgroup.closure (((β₃ F).range : Set (SpecialLinearGroup (Fin 3) F)) ∪
      ((β₂ F).range : Set (SpecialLinearGroup (Fin 3) F))) with hH
  have h3 : ∀ A, β₃ F A ∈ H := fun A => Subgroup.subset_closure (Or.inl ⟨A, rfl⟩)
  have h2 : ∀ A, β₂ F A ∈ H := fun A => Subgroup.subset_closure (Or.inr ⟨A, rfl⟩)
  have t01 : ∀ c : F, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈ H :=
    fun c => by rw [← β₃_transvection_01]; exact h3 _
  have t10 : ∀ c : F, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c ∈ H :=
    fun c => by rw [← β₃_transvection_10]; exact h3 _
  have t02 : ∀ c : F, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c ∈ H :=
    fun c => by rw [← β₂_transvection_01]; exact h2 _
  have t20 : ∀ c : F, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c ∈ H :=
    fun c => by rw [← β₂_transvection_10]; exact h2 _
  have comm_mem : ∀ {a b : SpecialLinearGroup (Fin 3) F}, a ∈ H → b ∈ H → ⁅a, b⁆ ∈ H := by
    intro a b ha hb
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have t12 : ∀ c : F, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c ∈ H := by
    intro c
    have := comm_mem (t10 c) (t02 1)
    rwa [SpecialLinearGroup.commutatorElement_transvection, mul_one] at this
  have t21 : ∀ c : F, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c ∈ H := by
    intro c
    have := comm_mem (t20 c) (t01 1)
    rwa [SpecialLinearGroup.commutatorElement_transvection, mul_one] at this
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 3) (K := F), Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  show SpecialLinearGroup.transvection hij c ∈ H
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact t01 c
  · exact t02 c
  · exact t10 c
  · exact absurd rfl hij
  · exact t12 c
  · exact t20 c
  · exact t21 c
  · exact absurd rfl hij

theorem mem_range_β₃_of {h : SpecialLinearGroup (Fin 3) F}
    (h02 : (h : Matrix (Fin 3) (Fin 3) F) 0 2 = 0) (h12 : (h : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (h20 : (h : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h21 : (h : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (h22 : (h : Matrix (Fin 3) (Fin 3) F) 2 2 = 1) : h ∈ (β₃ F).range := by
  have hdet : (!![(h : Matrix (Fin 3) (Fin 3) F) 0 0, (h : Matrix (Fin 3) (Fin 3) F) 0 1;
      (h : Matrix (Fin 3) (Fin 3) F) 1 0, (h : Matrix (Fin 3) (Fin 3) F) 1 1] :
        Matrix (Fin 2) (Fin 2) F).det = 1 := by
    have := h.2
    rw [Matrix.det_fin_three, h02, h12, h20, h21, h22] at this
    rw [Matrix.det_fin_two_of]
    linear_combination this
  refine ⟨⟨!![(h : Matrix (Fin 3) (Fin 3) F) 0 0, (h : Matrix (Fin 3) (Fin 3) F) 0 1;
      (h : Matrix (Fin 3) (Fin 3) F) 1 0, (h : Matrix (Fin 3) (Fin 3) F) 1 1], hdet⟩, ?_⟩
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  change blk₃ _ i j = (h : Matrix (Fin 3) (Fin 3) F) i j
  fin_cases i <;> fin_cases j <;> simp [blk₃, h02, h12, h20, h21, h22]

theorem mem_range_β₂_of {h : SpecialLinearGroup (Fin 3) F}
    (h01 : (h : Matrix (Fin 3) (Fin 3) F) 0 1 = 0) (h10 : (h : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h12 : (h : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) (h21 : (h : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (h11 : (h : Matrix (Fin 3) (Fin 3) F) 1 1 = 1) : h ∈ (β₂ F).range := by
  have hdet : (!![(h : Matrix (Fin 3) (Fin 3) F) 0 0, (h : Matrix (Fin 3) (Fin 3) F) 0 2;
      (h : Matrix (Fin 3) (Fin 3) F) 2 0, (h : Matrix (Fin 3) (Fin 3) F) 2 2] :
        Matrix (Fin 2) (Fin 2) F).det = 1 := by
    have := h.2
    rw [Matrix.det_fin_three, h01, h10, h12, h21, h11] at this
    rw [Matrix.det_fin_two_of]
    linear_combination this
  refine ⟨⟨!![(h : Matrix (Fin 3) (Fin 3) F) 0 0, (h : Matrix (Fin 3) (Fin 3) F) 0 2;
      (h : Matrix (Fin 3) (Fin 3) F) 2 0, (h : Matrix (Fin 3) (Fin 3) F) 2 2], hdet⟩, ?_⟩
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  change blk₂ _ i j = (h : Matrix (Fin 3) (Fin 3) F) i j
  fin_cases i <;> fin_cases j <;> simp [blk₂, h01, h10, h12, h21, h11]

end Blocks

section Involutions

variable (F : Type) [Field F]

@[expose] def t₃ : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.diagonal ![-1, -1, 1], by simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩

@[expose] def t₂ : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.diagonal ![-1, 1, -1], by simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩

variable {F}

theorem coe_t₃ : (t₃ F : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![-1, -1, 1] := rfl

theorem coe_t₂ : (t₂ F : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![-1, 1, -1] := rfl

theorem block₃_of_commute (h2 : (2 : F) ≠ 0) {g : Matrix.SpecialLinearGroup (Fin 3) F}
    (h : g * t₃ F = t₃ F * g) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  have hm : (g : Matrix (Fin 3) (Fin 3) F) * (t₃ F : Matrix (Fin 3) (Fin 3) F) =
      (t₃ F : Matrix (Fin 3) (Fin 3) F) * g := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, h]
  rw [coe_t₃] at hm
  have e := fun i j => congrFun (congrFun hm i) j
  have e02 := e 0 2
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at e02 e12 e20 e21
  simp at e02 e12 e20 e21
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (2 : F) * (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by linear_combination e02
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : (2 : F) * (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by linear_combination e12
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : (2 : F) * (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by linear_combination -e20
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : (2 : F) * (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by linear_combination -e21
    exact (mul_eq_zero.mp this).resolve_left h2

theorem block₂_of_commute (h2 : (2 : F) ≠ 0) {g : Matrix.SpecialLinearGroup (Fin 3) F}
    (h : g * t₂ F = t₂ F * g) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  have hm : (g : Matrix (Fin 3) (Fin 3) F) * (t₂ F : Matrix (Fin 3) (Fin 3) F) =
      (t₂ F : Matrix (Fin 3) (Fin 3) F) * g := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, h]
  rw [coe_t₂] at hm
  have e := fun i j => congrFun (congrFun hm i) j
  have e01 := e 0 1
  have e10 := e 1 0
  have e12 := e 1 2
  have e21 := e 2 1
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at e01 e10 e12 e21
  simp at e01 e10 e12 e21
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (2 : F) * (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : (2 : F) * (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := by linear_combination -e10
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : (2 : F) * (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by linear_combination -e12
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : (2 : F) * (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by linear_combination e21
    exact (mul_eq_zero.mp this).resolve_left h2

theorem conj_β₃_mem {g : Matrix.SpecialLinearGroup (Fin 3) F}
    (g02 : (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0) (g12 : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (g20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (g21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    g * β₃ F A * g⁻¹ ∈ (β₃ F).range := by
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := g.2
  rw [Matrix.det_fin_three, g02, g12, g20, g21] at hdet
  refine mem_range_β₃_of ?_ ?_ ?_ ?_ ?_ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_three, coe_β₃, blk₃, Matrix.mul_apply, Fin.sum_univ_three, g02, g12,
      g20, g21]
  linear_combination hdet

theorem conj_β₂_mem {g : Matrix.SpecialLinearGroup (Fin 3) F}
    (g01 : (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0) (g10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (g12 : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) (g21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    g * β₂ F A * g⁻¹ ∈ (β₂ F).range := by
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := g.2
  rw [Matrix.det_fin_three, g01, g10, g12, g21] at hdet
  refine mem_range_β₂_of ?_ ?_ ?_ ?_ ?_ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_three, coe_β₂, blk₂, Matrix.mul_apply, Fin.sum_univ_three, g01, g10,
      g12, g21]
  linear_combination hdet

theorem β₃_commute (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    β₃ F A * t₃ F = t₃ F * β₃ F A := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_β₃, coe_t₃]
  fin_cases i <;> fin_cases j <;> simp [blk₃, Matrix.mul_apply, Matrix.diagonal_apply]

theorem β₂_commute (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    β₂ F A * t₂ F = t₂ F * β₂ F A := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_β₂, coe_t₂]
  fin_cases i <;> fin_cases j <;> simp [blk₂, Matrix.mul_apply, Matrix.diagonal_apply]

end Involutions

section Proj

variable (F : Type) [Field F]

noncomputable def projSL : SpecialLinearGroup (Fin 3) F →* StatedProj (StatedSL 3 F) :=
  (statedProjMk (StatedSL 3 F)).comp (specialLinearGroupEquivStatedSL 3 F).toMonoidHom

theorem projSL_surjective : Function.Surjective (projSL F) :=
  (statedProjMk_surjective _).comp (specialLinearGroupEquivStatedSL 3 F).surjective

theorem projSL_eq_one_iff (g : SpecialLinearGroup (Fin 3) F) :
    projSL F g = 1 ↔ g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
  rw [projSL, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← map_center_eq_statedScalars 3 F]
  exact Subgroup.mem_map_iff_mem (specialLinearGroupEquivStatedSL 3 F).injective

theorem projSL_t₃ : projSL F (t₃ F) = linU₀ F := by
  unfold projSL linU₀
  refine congrArg (statedProjMk (StatedSL 3 F)) (Subtype.ext (Units.ext ?_))
  change (t₃ F : Matrix (Fin 3) (Fin 3) F) = (oddDiag₃ F : Matrix (Fin 3) (Fin 3) F)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_t₃, oddDiag₃]

theorem projSL_t₂ : projSL F (t₂ F) = linU₀' F := by
  unfold projSL linU₀'
  refine congrArg (statedProjMk (StatedSL 3 F)) (Subtype.ext (Units.ext ?_))
  change (t₂ F : Matrix (Fin 3) (Fin 3) F) = (oddDiag₂ F : Matrix (Fin 3) (Fin 3) F)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_t₂, oddDiag₂]

variable {F}

theorem commute_of_projSL_commute {t g : Matrix.SpecialLinearGroup (Fin 3) F}
    (ht : Matrix.trace (t : Matrix (Fin 3) (Fin 3) F) ≠ 0)
    (h : projSL F g * projSL F t = projSL F t * projSL F g) : g * t = t * g := by
  have hz : projSL F (g⁻¹ * t * g * t⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [mul_assoc (projSL F g)⁻¹ (projSL F t) (projSL F g), ← h, ← mul_assoc, inv_mul_cancel,
      one_mul, mul_inv_cancel]
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 ((projSL_eq_one_iff F _).1 hz)
  have h1 : g⁻¹ * t * g = (g⁻¹ * t * g * t⁻¹) * t := by group
  have h2 : ((g⁻¹ * t * g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.scalar (Fin 3) r * (t : Matrix (Fin 3) (Fin 3) F) := by
    rw [h1, Matrix.SpecialLinearGroup.coe_mul, ← hr]
  have h3 : Matrix.trace ((g⁻¹ * t * g : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = Matrix.trace (t : Matrix (Fin 3) (Fin 3) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  have h4 : Matrix.trace (Matrix.scalar (Fin 3) r * (t : Matrix (Fin 3) (Fin 3) F)) =
      r * Matrix.trace (t : Matrix (Fin 3) (Fin 3) F) := by
    rw [Matrix.trace_fin_three, Matrix.trace_fin_three]
    simp [Matrix.scalar_apply, Matrix.diagonal_mul]
    ring
  have hr1 : r = 1 := by
    rw [h2, h4] at h3
    exact mul_right_cancel₀ ht (by rw [h3, one_mul])
  subst hr1
  have h5 : g⁻¹ * t * g * t⁻¹ = 1 :=
    Matrix.SpecialLinearGroup.ext _ _ fun i j => by simpa using (congrFun (congrFun hr i) j).symm
  have h6 : g⁻¹ * t * g = t := mul_inv_eq_one.1 h5
  calc g * t = g * (g⁻¹ * t * g) := by rw [h6]
    _ = t * g := by group

end Proj

section Abstract

variable {G X : Type} [Group G] [Group X] {F : Type} [Field F]

theorem range_le_Ez [Finite F] (h4 : 4 ≤ Nat.card F) (π : G →* X) (hπ : Function.Surjective π)
    (t : G) (β : Matrix.SpecialLinearGroup (Fin 2) F →* G) (hinj : Function.Injective (π.comp β))
    (hcomm : ∀ A, π (β A) * π t = π t * π (β A))
    (hnorm : ∀ g : G, π g * π t = π t * π g → ∀ A, ∃ A', g * β A * g⁻¹ = β A') :
    (π.comp β).range ≤ Ez (π t) := by
  set C : Subgroup X := Subgroup.centralizer ({π t} : Set X) with hC
  set J : Subgroup X := (π.comp β).range with hJ
  have hJC : J ≤ C := by
    rintro _ ⟨A, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm A
  have hnormal : (J.subgroupOf C).Normal := by
    refine ⟨fun n hn c => ?_⟩
    obtain ⟨A, hA⟩ := hn
    obtain ⟨g, hg⟩ := hπ (c : X)
    have hgc : π g * π t = π t * π g := by
      have := Subgroup.mem_centralizer_singleton_iff.1 c.2
      rw [hg]
      exact this
    obtain ⟨A', hA'⟩ := hnorm g hgc A
    refine ⟨A', ?_⟩
    change π (β A') = ((c * n * c⁻¹ : C) : X)
    rw [← hA', map_mul, map_mul, map_inv, hg]
    change _ = (c : X) * (n : X) * (c : X)⁻¹
    have hA2 : π (β A) = (n : X) := hA
    rw [hA2]
  have hqs : CFSG.IsQuasisimple (J.subgroupOf C) := by
    have e : Matrix.SpecialLinearGroup (Fin 2) F ≃* J.subgroupOf C :=
      (MonoidHom.ofInjective hinj).trans (Subgroup.subgroupOfEquivOfLe hJC).symm
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1
      (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4)
  have hle : J.subgroupOf C ≤ CFSG.layer C := le_sSup ⟨hqs, hnormal.isSubnormal⟩
  calc J = (J.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hJC).symm
    _ ≤ (CFSG.layer C).map C.subtype := Subgroup.map_mono hle
    _ = Ez (π t) := rfl

theorem closure_map_le_O2z (π : G →* X) (t : G) (T : Set G)
    (hT : ∀ x ∈ T, π x * π t = π t * π x ∧ Odd (orderOf (π x))) :
    (Subgroup.closure T).map π ≤ O2z (π t) := by
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hc, ho⟩ := hT x hx
  have hxC : π x ∈ Subgroup.centralizer ({π t} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 hc
  refine ⟨⟨π x, hxC⟩, ?_, rfl⟩
  apply Subgroup.subset_closure
  show Nat.Coprime (orderOf (⟨π x, hxC⟩ : ↥(Subgroup.centralizer ({π t} : Set X)))) 2
  rw [Subgroup.orderOf_mk]
  exact Nat.coprime_two_right.2 ho

theorem closure_union_map_eq_top (π : G →* X) (hπ : Function.Surjective π) (A B : Subgroup G)
    (h : Subgroup.closure ((A : Set G) ∪ (B : Set G)) = ⊤) :
    Subgroup.closure ((A.map π : Set X) ∪ (B.map π : Set X)) = ⊤ := by
  have h1 : (Subgroup.closure ((A : Set G) ∪ (B : Set G))).map π =
      Subgroup.closure ((A.map π : Set X) ∪ (B.map π : Set X)) := by
    rw [MonoidHom.map_closure, Set.image_union, ← Subgroup.coe_map, ← Subgroup.coe_map]
  rw [← h1, h, Subgroup.map_top, MonoidHom.range_eq_top.2 hπ]

end Abstract

section Transvection

variable {F : Type} [Field F]

theorem transvection_pow {ι : Type} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j) (c : F)
    (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection hij c ^ n =
      Matrix.SpecialLinearGroup.transvection hij (n • c) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, succ_nsmul, Matrix.SpecialLinearGroup.transvection_add]

theorem orderOf_transvection_dvd [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) (c : F) :
    orderOf (Matrix.SpecialLinearGroup.transvection hij c) ∣ Nat.card F := by
  apply orderOf_dvd_of_pow_eq_one
  rw [transvection_pow, card_nsmul_eq_zero', Matrix.SpecialLinearGroup.transvection_coeff_zero]

end Transvection

section Main

variable (F : Type) [Field F]

theorem projSL_comp_β₃_injective : Function.Injective ((projSL F).comp (β₃ F)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1
    ((projSL_eq_one_iff F _).1 hA)
  have hr1 : r = 1 := by
    have := congrFun (congrFun hr 2) 2
    simpa [Matrix.scalar_apply, coe_β₃, blk₃] using this
  subst hr1
  apply β₃_injective
  rw [map_one]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simpa using (congrFun (congrFun hr i) j).symm

theorem projSL_comp_β₂_injective : Function.Injective ((projSL F).comp (β₂ F)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1
    ((projSL_eq_one_iff F _).1 hA)
  have hr1 : r = 1 := by
    have := congrFun (congrFun hr 1) 1
    simpa [Matrix.scalar_apply, coe_β₂, blk₂] using this
  subst hr1
  apply β₂_injective
  rw [map_one]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simpa using (congrFun (congrFun hr i) j).symm

theorem trace_t₃_ne_zero : Matrix.trace (t₃ F : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
  rw [Matrix.trace_fin_three, coe_t₃]
  simp

theorem trace_t₂_ne_zero : Matrix.trace (t₂ F : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
  rw [Matrix.trace_fin_three, coe_t₂]
  simp

variable {F}

theorem range₃_le_Ez [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    ((projSL F).comp (β₃ F)).range ≤ Ez (linU₀ F) := by
  rw [← projSL_t₃]
  refine range_le_Ez h4 (projSL F) (projSL_surjective F) (t₃ F) (β₃ F)
    (projSL_comp_β₃_injective F) ?_ ?_
  · intro A
    rw [← map_mul, ← map_mul, β₃_commute]
  · intro g hg A
    obtain ⟨g02, g12, g20, g21⟩ :=
      block₃_of_commute h2 (commute_of_projSL_commute (trace_t₃_ne_zero F) hg)
    obtain ⟨A', hA'⟩ := conj_β₃_mem g02 g12 g20 g21 A
    exact ⟨A', hA'.symm⟩

theorem range₂_le_Ez [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    ((projSL F).comp (β₂ F)).range ≤ Ez (linU₀' F) := by
  rw [← projSL_t₂]
  refine range_le_Ez h4 (projSL F) (projSL_surjective F) (t₂ F) (β₂ F)
    (projSL_comp_β₂_injective F) ?_ ?_
  · intro A
    rw [← map_mul, ← map_mul, β₂_commute]
  · intro g hg A
    obtain ⟨g01, g10, g12, g21⟩ :=
      block₂_of_commute h2 (commute_of_projSL_commute (trace_t₂_ne_zero F) hg)
    obtain ⟨A', hA'⟩ := conj_β₂_mem g01 g10 g12 g21 A
    exact ⟨A', hA'.symm⟩

theorem range_β_eq_closure_transvections
    (β : Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 3) F) :
    β.range = Subgroup.closure (β '' Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 2) F → Matrix.SpecialLinearGroup (Fin 2) F)) := by
  rw [MonoidHom.range_eq_map,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin 2)
      (K := F), MonoidHom.map_closure]

theorem range₃_le_O2z [Finite F] (hodd : Odd (Nat.card F)) :
    ((projSL F).comp (β₃ F)).range ≤ O2z (linU₀ F) := by
  rw [← projSL_t₃, MonoidHom.range_comp, range_β_eq_closure_transvections]
  refine closure_map_le_O2z (projSL F) (t₃ F) _ ?_
  rintro _ ⟨_, ⟨τ, rfl⟩, rfl⟩
  refine ⟨by rw [← map_mul, ← map_mul, β₃_commute], ?_⟩
  exact Odd.of_dvd_nat hodd
    ((orderOf_map_dvd ((projSL F).comp (β₃ F)) τ.toSpecialLinearGroup).trans
      (orderOf_transvection_dvd τ.hij τ.c))

theorem range₂_le_O2z [Finite F] (hodd : Odd (Nat.card F)) :
    ((projSL F).comp (β₂ F)).range ≤ O2z (linU₀' F) := by
  rw [← projSL_t₂, MonoidHom.range_comp, range_β_eq_closure_transvections]
  refine closure_map_le_O2z (projSL F) (t₂ F) _ ?_
  rintro _ ⟨_, ⟨τ, rfl⟩, rfl⟩
  refine ⟨by rw [← map_mul, ← map_mul, β₂_commute], ?_⟩
  exact Odd.of_dvd_nat hodd
    ((orderOf_map_dvd ((projSL F).comp (β₂ F)) τ.toSpecialLinearGroup).trans
      (orderOf_transvection_dvd τ.hij τ.c))

theorem closure_range_comp_eq_top :
    Subgroup.closure ((((projSL F).comp (β₃ F)).range : Set (StatedProj (StatedSL 3 F))) ∪
      (((projSL F).comp (β₂ F)).range : Set (StatedProj (StatedSL 3 F)))) = ⊤ := by
  rw [MonoidHom.range_comp, MonoidHom.range_comp]
  exact closure_union_map_eq_top (projSL F) (projSL_surjective F) _ _ closure_β_eq_top

end Main

end LinGenAux

open LinGenAux in
theorem linGen (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) : LinGen F := by
  have h2 : (2 : F) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card F hodd
  unfold LinGen
  refine ⟨fun h3 => ?_, fun h3 => ?_⟩
  · have h4 : 4 ≤ Nat.card F := h3
    rw [eq_top_iff, ← closure_range_comp_eq_top]
    exact Subgroup.closure_mono
      (Set.union_subset_union (SetLike.coe_subset_coe.2 (range₃_le_Ez h2 h4))
        (SetLike.coe_subset_coe.2 (range₂_le_Ez h2 h4)))
  · rw [eq_top_iff, ← closure_range_comp_eq_top]
    exact Subgroup.closure_mono
      (Set.union_subset_union (SetLike.coe_subset_coe.2 (range₃_le_O2z hodd))
        (SetLike.coe_subset_coe.2 (range₂_le_O2z hodd)))

end CFSG.GH74.GLS.IVK.Proofs2
