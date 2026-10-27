module

public import CFSG.LieType.SpecialLinear.Block222.Basic
public import CFSG.LieType.SpecialLinear.BorelStd

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

noncomputable section

variable (c : ℕ) (F : Type) [Field F]

theorem isUpperGL_inv {n : ℕ} {A : GL (Fin n) F} (hA : IsUpperGL A) : IsUpperGL A⁻¹ := by
  intro i j hji
  rw [Matrix.GeneralLinearGroup.coe_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular (b := id)
    (M := (A : Matrix (Fin n) (Fin n) F)) (fun p q hpq => hA p q hpq) hji

@[expose] def blockMat11 (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) : Matrix (Fin 2) (Fin 2) F :=
  fun i j => A (e222 c (Sum.inl i)) (e222 c (Sum.inl j))

@[expose] def blockMat12 (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) :
    Matrix (Fin 2) (Fin c ⊕ Fin 2) F :=
  fun i j => A (e222 c (Sum.inl i)) (e222 c (Sum.inr j))

@[expose] def blockMat21 (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) :
    Matrix (Fin c ⊕ Fin 2) (Fin 2) F :=
  fun i j => A (e222 c (Sum.inr i)) (e222 c (Sum.inl j))

@[expose] def blockMat22 (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) :
    Matrix (Fin c ⊕ Fin 2) (Fin c ⊕ Fin 2) F :=
  fun i j => A (e222 c (Sum.inr i)) (e222 c (Sum.inr j))

@[expose] def blockMat22a (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) :
    Matrix (Fin c) (Fin c) F :=
  fun i j => A (e222 c (Sum.inr (Sum.inl i))) (e222 c (Sum.inr (Sum.inl j)))

@[expose] def blockMat22b (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) :
    Matrix (Fin c) (Fin 2) F :=
  fun i j => A (e222 c (Sum.inr (Sum.inl i))) (e222 c (Sum.inr (Sum.inr j)))

@[expose] def blockMat32 (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) :
    Matrix (Fin 2) (Fin c) F :=
  fun i j => A (e222 c (Sum.inr (Sum.inr i))) (e222 c (Sum.inr (Sum.inl j)))

@[expose] def blockMat33 (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) : Matrix (Fin 2) (Fin 2) F :=
  fun i j => A (e222 c (Sum.inr (Sum.inr i))) (e222 c (Sum.inr (Sum.inr j)))

theorem blockMat21_eq_zero (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) :
    blockMat21 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) = 0 := by
  ext i j
  rcases i with s | k
  · exact hA _ _ (e222_inl_lt_inr_inl c j s)
  · exact hA _ _ (e222_inl_lt_inr_inr c j k)

theorem blockMat32_eq_zero (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) :
    blockMat32 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) = 0 := by
  ext i j
  exact hA _ _ (e222_inr_inl_lt_inr_inr c j i)

theorem blockMat22_eq_fromBlocks (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) :
    blockMat22 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
      Matrix.fromBlocks (blockMat22a c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F))
        (blockMat22b c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)) 0
        (blockMat33 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)) := by
  ext x y
  rcases x with s | k <;> rcases y with t | l
  · rfl
  · rfl
  · exact congrFun (congrFun (blockMat32_eq_zero c F A hA) k) t
  · rfl

theorem reindexAlgEquiv_eq_fromBlocks (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) :
    (Matrix.reindexAlgEquiv F F (e222 c).symm) A =
      Matrix.fromBlocks (blockMat11 c F A) (blockMat12 c F A) (blockMat21 c F A)
        (blockMat22 c F A) := by
  ext x y
  rcases x with a | (s | k) <;> rcases y with b | (t | l) <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      blockMat11, blockMat12, blockMat21, blockMat22]

theorem reindexAlgEquiv_eq_fromBlocks' (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) :
    (Matrix.reindexAlgEquiv F F (e222 c).symm)
        (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
      Matrix.fromBlocks (blockMat11 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F))
        (blockMat12 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)) 0
        (Matrix.fromBlocks (blockMat22a c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F))
          (blockMat22b c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)) 0
          (blockMat33 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F))) := by
  rw [reindexAlgEquiv_eq_fromBlocks, blockMat21_eq_zero c F A hA,
    blockMat22_eq_fromBlocks c F A hA]

theorem blockMat11_mul_blockMat11_inv (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) :
    blockMat11 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) *
        blockMat11 c F ((A⁻¹ : GL (Fin (c + 4)) F) :
          Matrix (Fin (c + 4)) (Fin (c + 4)) F) = 1 := by
  ext i j
  have hAA : (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) *
      ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  have hsum := congrFun (congrFun hAA (e222 c (Sum.inl i))) (e222 c (Sum.inl j))
  rw [Matrix.mul_apply, Matrix.one_apply] at hsum
  rw [← Equiv.sum_comp (e222 c) (fun x =>
    (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inl i)) x *
      ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F) x
        (e222 c (Sum.inl j)))] at hsum
  rw [Fintype.sum_sum_type] at hsum
  rw [Fintype.sum_sum_type] at hsum
  have hmid : ∀ t : Fin c,
      (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inl i))
          (e222 c (Sum.inr (Sum.inl t))) *
        ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
          (e222 c (Sum.inr (Sum.inl t))) (e222 c (Sum.inl j)) = 0 := by
    intro t
    have h : e222 c (Sum.inl j) < e222 c (Sum.inr (Sum.inl t)) :=
      e222_inl_lt_inr_inl c j t
    rw [isUpperGL_inv (F := F) (A := A) hA _ _ h, mul_zero]
  have hright : ∀ k : Fin 2,
      (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inl i))
          (e222 c (Sum.inr (Sum.inr k))) *
        ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
          (e222 c (Sum.inr (Sum.inr k))) (e222 c (Sum.inl j)) = 0 := by
    intro k
    have h : e222 c (Sum.inl j) < e222 c (Sum.inr (Sum.inr k)) :=
      e222_inl_lt_inr_inr c j k
    rw [isUpperGL_inv (F := F) (A := A) hA _ _ h, mul_zero]
  simp only [hmid, hright, Finset.sum_const_zero, zero_add] at hsum
  rw [Matrix.mul_apply, Matrix.one_apply]
  simpa [blockMat11, (e222 c).injective.eq_iff] using hsum

theorem blockMat22a_mul_blockMat22a_inv (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) :
    blockMat22a c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) *
        blockMat22a c F ((A⁻¹ : GL (Fin (c + 4)) F) :
          Matrix (Fin (c + 4)) (Fin (c + 4)) F) = 1 := by
  ext i j
  have hAA : (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) *
      ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  have hsum := congrFun (congrFun hAA (e222 c (Sum.inr (Sum.inl i))))
    (e222 c (Sum.inr (Sum.inl j)))
  rw [Matrix.mul_apply, Matrix.one_apply] at hsum
  rw [← Equiv.sum_comp (e222 c) (fun x =>
    (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inr (Sum.inl i))) x *
      ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F) x
        (e222 c (Sum.inr (Sum.inl j))))] at hsum
  rw [Fintype.sum_sum_type] at hsum
  rw [Fintype.sum_sum_type] at hsum
  have hleft : ∀ a : Fin 2,
      (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inr (Sum.inl i)))
          (e222 c (Sum.inl a)) *
        ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
          (e222 c (Sum.inl a)) (e222 c (Sum.inr (Sum.inl j))) = 0 := by
    intro a
    have h : e222 c (Sum.inl a) < e222 c (Sum.inr (Sum.inl i)) :=
      e222_inl_lt_inr_inl c a i
    rw [hA _ _ h, zero_mul]
  have hright : ∀ k : Fin 2,
      (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inr (Sum.inl i)))
          (e222 c (Sum.inr (Sum.inr k))) *
        ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
          (e222 c (Sum.inr (Sum.inr k))) (e222 c (Sum.inr (Sum.inl j))) = 0 := by
    intro k
    have h : e222 c (Sum.inr (Sum.inl j)) < e222 c (Sum.inr (Sum.inr k)) :=
      e222_inr_inl_lt_inr_inr c j k
    rw [isUpperGL_inv (F := F) (A := A) hA _ _ h, mul_zero]
  simp only [hleft, hright, Finset.sum_const_zero, zero_add] at hsum
  rw [Matrix.mul_apply, Matrix.one_apply]
  simpa [blockMat22a, (e222 c).injective.eq_iff] using hsum

theorem blockMat33_mul_blockMat33_inv (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) :
    blockMat33 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) *
        blockMat33 c F ((A⁻¹ : GL (Fin (c + 4)) F) :
          Matrix (Fin (c + 4)) (Fin (c + 4)) F) = 1 := by
  ext i j
  have hAA : (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) *
      ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  have hsum := congrFun (congrFun hAA (e222 c (Sum.inr (Sum.inr i))))
    (e222 c (Sum.inr (Sum.inr j)))
  rw [Matrix.mul_apply, Matrix.one_apply] at hsum
  rw [← Equiv.sum_comp (e222 c) (fun x =>
    (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inr (Sum.inr i))) x *
      ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F) x
        (e222 c (Sum.inr (Sum.inr j))))] at hsum
  rw [Fintype.sum_sum_type] at hsum
  rw [Fintype.sum_sum_type] at hsum
  have hleft : ∀ a : Fin 2,
      (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inr (Sum.inr i)))
          (e222 c (Sum.inl a)) *
        ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
          (e222 c (Sum.inl a)) (e222 c (Sum.inr (Sum.inr j))) = 0 := by
    intro a
    have h : e222 c (Sum.inl a) < e222 c (Sum.inr (Sum.inr i)) :=
      e222_inl_lt_inr_inr c a i
    rw [hA _ _ h, zero_mul]
  have hmid : ∀ t : Fin c,
      (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inr (Sum.inr i)))
          (e222 c (Sum.inr (Sum.inl t))) *
        ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
          (e222 c (Sum.inr (Sum.inl t))) (e222 c (Sum.inr (Sum.inr j))) = 0 := by
    intro t
    have h : e222 c (Sum.inr (Sum.inl t)) < e222 c (Sum.inr (Sum.inr i)) :=
      e222_inr_inl_lt_inr_inr c t i
    rw [hA _ _ h, zero_mul]
  simp only [hleft, hmid, Finset.sum_const_zero, zero_add] at hsum
  rw [Matrix.mul_apply, Matrix.one_apply]
  simpa [blockMat33, (e222 c).injective.eq_iff] using hsum

@[expose] def blockGL1 (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) : GL (Fin 2) F :=
  Units.mkOfMulEqOne (blockMat11 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F))
    (blockMat11 c F ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F))
    (blockMat11_mul_blockMat11_inv c F A hA)

@[expose] def blockGL2 (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) : GL (Fin c) F :=
  Units.mkOfMulEqOne (blockMat22a c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F))
    (blockMat22a c F ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F))
    (blockMat22a_mul_blockMat22a_inv c F A hA)

@[expose] def blockGL3 (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) : GL (Fin 2) F :=
  Units.mkOfMulEqOne (blockMat33 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F))
    (blockMat33 c F ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F))
    (blockMat33_mul_blockMat33_inv c F A hA)

@[simp] theorem coe_blockGL1 (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) (i j : Fin 2) :
    ((blockGL1 c F A hA : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
      (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) (e222 c (Sum.inl i)) (e222 c (Sum.inl j)) :=
  rfl

@[simp] theorem coe_blockGL2 (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) (i j : Fin c) :
    ((blockGL2 c F A hA : GL (Fin c) F) : Matrix (Fin c) (Fin c) F) i j =
      (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
        (e222 c (Sum.inr (Sum.inl i))) (e222 c (Sum.inr (Sum.inl j))) :=
  rfl

@[simp] theorem coe_blockGL3 (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) (i j : Fin 2) :
    ((blockGL3 c F A hA : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
      (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
        (e222 c (Sum.inr (Sum.inr i))) (e222 c (Sum.inr (Sum.inr j))) :=
  rfl

end

end CFSG.LieType.SpecialLinear
