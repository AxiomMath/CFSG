module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Block

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix

section Coord

variable {R : Type*} [CommRing R]

@[expose] def uMat (x : Fin 6 → R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, x 0, x 1, x 2; 0, 1, x 3, x 4; 0, 0, 1, x 5; 0, 0, 0, 1]

@[expose] def uMulF (x y : Fin 6 → R) : Fin 6 → R :=
  ![x 0 + y 0, x 1 + y 1 + x 0 * y 3, x 2 + y 2 + x 0 * y 4 + x 1 * y 5, x 3 + y 3,
    x 4 + y 4 + x 3 * y 5, x 5 + y 5]

@[expose] def uInvF (x : Fin 6 → R) : Fin 6 → R :=
  ![-x 0, -x 1 + x 0 * x 3, -x 2 + x 0 * x 4 + x 1 * x 5 - x 0 * x 3 * x 5, -x 3,
    -x 4 + x 3 * x 5, -x 5]

theorem uMat_mul (x y : Fin 6 → R) : uMat x * uMat y = uMat (uMulF x y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, uMulF, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem uMat_zero : uMat (0 : Fin 6 → R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

theorem uMulF_uInvF (x : Fin 6 → R) : uMulF x (uInvF x) = 0 := by
  funext k
  fin_cases k <;> simp [uMulF, uInvF]
  ring

theorem uMat_isUpperTriangular (x : Fin 6 → R) : (uMat x).IsUpperTriangular := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)

theorem det_uMat (x : Fin 6 → R) : (uMat x).det = 1 := by
  rw [det_of_isUpperTriangular (uMat_isUpperTriangular x), Fin.prod_univ_four]
  simp [uMat]

theorem uMat_injective : Function.Injective (uMat (R := R)) := by
  intro x y h
  have h' : ∀ i j, uMat x i j = uMat y i j := fun i j => congrFun (congrFun h i) j
  funext k
  fin_cases k
  · simpa [uMat] using h' 0 1
  · simpa [uMat] using h' 0 2
  · simpa [uMat] using h' 0 3
  · simpa [uMat] using h' 1 2
  · simpa [uMat] using h' 1 3
  · simpa [uMat] using h' 2 3

@[expose] def uElem (x : Fin 6 → R) : SpecialLinearGroup (Fin 4) R :=
  ⟨uMat x, det_uMat x⟩

theorem coe_uElem (x : Fin 6 → R) :
    ((uElem x : SpecialLinearGroup (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) = uMat x :=
  rfl

theorem uElem_mul (x y : Fin 6 → R) : uElem x * uElem y = uElem (uMulF x y) :=
  Subtype.ext (uMat_mul x y)

theorem uElem_zero : uElem (0 : Fin 6 → R) = 1 :=
  Subtype.ext uMat_zero

theorem uElem_inv (x : Fin 6 → R) : (uElem x)⁻¹ = uElem (uInvF x) :=
  inv_eq_of_mul_eq_one_right (by rw [uElem_mul, uMulF_uInvF, uElem_zero])

theorem uElem_injective : Function.Injective (uElem (R := R)) :=
  fun _ _ h => uMat_injective (congrArg Subtype.val h)

theorem uElem_eq_one_iff {x : Fin 6 → R} : uElem x = 1 ↔ x = 0 := by
  rw [← uElem_zero]
  exact uElem_injective.eq_iff

variable (R) in
@[expose] def uGroup : Subgroup (SpecialLinearGroup (Fin 4) R) where
  carrier := Set.range uElem
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨uMulF x y, (uElem_mul x y).symm⟩
  one_mem' := ⟨0, uElem_zero⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨uInvF x, (uElem_inv x).symm⟩

theorem uElem_mem_uGroup (x : Fin 6 → R) : uElem x ∈ uGroup R :=
  ⟨x, rfl⟩

theorem card_uGroup : Nat.card (uGroup R) = Nat.card R ^ 6 := by
  have h : Nat.card (uGroup R) = Nat.card (Fin 6 → R) :=
    Nat.card_range_of_injective uElem_injective
  rw [h, Nat.card_fun, Nat.card_fin]

end Coord

section Root

variable {R : Type*} [CommRing R]

@[expose] def uRow : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

@[expose] def uCol : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

theorem uRow_ne_uCol (k : Fin 6) : uRow k ≠ uCol k := by
  fin_cases k <;> decide

@[expose] def uRoot (k : Fin 6) : SpecialLinearGroup (Fin 4) R :=
  uElem (Pi.single k 1)

theorem uRoot_eq_transvection (k : Fin 6) :
    uRoot (R := R) k = SpecialLinearGroup.transvection (uRow_ne_uCol k) 1 := by
  apply Subtype.ext
  rw [uRoot, coe_uElem, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [uMat, uRow, uCol]

theorem uRoot_mem_uGroup (k : Fin 6) : uRoot (R := R) k ∈ uGroup R :=
  uElem_mem_uGroup _

end Root

section Quot

@[expose] def uQuot : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)) :=
  Subgroup.closure (Set.range fun k : Fin 5 => uRoot (R := ZMod 2) k.castSucc)

theorem uRoot_castSucc_mem_uQuot (k : Fin 5) : uRoot (R := ZMod 2) k.castSucc ∈ uQuot :=
  Subgroup.subset_closure ⟨k, rfl⟩

theorem uQuot_le_uGroup : uQuot ≤ uGroup (ZMod 2) := by
  rw [uQuot, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact uRoot_mem_uGroup _

theorem eq_zero_or_eq_one_zmod_two (s : ZMod 2) : s = 0 ∨ s = 1 := by
  revert s
  decide

theorem uElem_single_mem_uQuot (k : Fin 5) (s : ZMod 2) :
    uElem (Pi.single k.castSucc s) ∈ uQuot := by
  rcases eq_zero_or_eq_one_zmod_two s with rfl | rfl
  · rw [Pi.single_zero, uElem_zero]
    exact one_mem _
  · exact uRoot_castSucc_mem_uQuot k

theorem uElem_mem_uQuot {x : Fin 6 → ZMod 2} (hx : x 5 = 0) : uElem x ∈ uQuot := by
  have hw : x = uMulF (uMulF (uMulF (uMulF (Pi.single 0 (x 0)) (Pi.single 1 (x 1 - x 0 * x 3)))
      (Pi.single 2 (x 2 - x 0 * x 4))) (Pi.single 3 (x 3))) (Pi.single 4 (x 4)) := by
    funext k
    fin_cases k <;> simp [uMulF, hx]
  rw [hw, ← uElem_mul, ← uElem_mul, ← uElem_mul, ← uElem_mul]
  refine mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_
  · exact uElem_single_mem_uQuot 0 _
  · exact uElem_single_mem_uQuot 1 _
  · exact uElem_single_mem_uQuot 2 _
  · exact uElem_single_mem_uQuot 3 _
  · exact uElem_single_mem_uQuot 4 _

theorem card_uQuot : 2 ^ 5 ≤ Nat.card uQuot := by
  let f : (Fin 5 → ZMod 2) → uQuot := fun z =>
    ⟨uElem (Fin.snoc (α := fun _ => ZMod 2) z 0), uElem_mem_uQuot (by
      change Fin.snoc (α := fun _ => ZMod 2) z 0 (Fin.last 5) = 0
      rw [Fin.snoc_last])⟩
  have hf : Function.Injective f := by
    intro z z' h
    have h1 : Fin.snoc (α := fun _ => ZMod 2) z 0 = Fin.snoc (α := fun _ => ZMod 2) z' 0 :=
      uElem_injective (congrArg Subtype.val h)
    funext i
    have h2 := congrFun h1 i.castSucc
    rwa [Fin.snoc_castSucc, Fin.snoc_castSucc] at h2
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_fun, Nat.card_fin, Nat.card_zmod] at h

theorem uGroup_le_sup : uGroup (ZMod 2) ≤ uQuot ⊔ Subgroup.zpowers (uRoot (R := ZMod 2) 5) := by
  rintro _ ⟨x, rfl⟩
  have hw : x = uMulF ![x 0, x 1, x 2 - x 1 * x 5, x 3, x 4 - x 3 * x 5, 0]
      (Pi.single 5 (x 5)) := by
    funext k
    fin_cases k <;> simp [uMulF]
  rw [hw, ← uElem_mul]
  refine mul_mem (Subgroup.mem_sup_left (uElem_mem_uQuot (by simp)))
    (Subgroup.mem_sup_right ?_)
  rcases eq_zero_or_eq_one_zmod_two (x 5) with h | h
  · rw [h, Pi.single_zero, uElem_zero]
    exact one_mem _
  · rw [h]
    exact Subgroup.mem_zpowers _

end Quot

section Involution

@[expose] def uRep : Fin 9 → Fin 6 → ZMod 2 :=
  ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 1, 0], ![0, 0, 1, 1, 0, 0],
    ![1, 0, 0, 0, 0, 1]]

@[expose] def uConj : Fin 9 → Fin 6 → ZMod 2 :=
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 1, 0, 1]]

theorem uInvolution_check : ∀ x0 x1 x2 x3 x4 x5 : ZMod 2,
    uMulF ![x0, x1, x2, x3, x4, x5] ![x0, x1, x2, x3, x4, x5] = 0 →
      ![x0, x1, x2, x3, x4, x5] = 0 ∨
        ∃ i k : Fin 9, uMulF ![x0, x1, x2, x3, x4, x5] (uConj i) =
          uMulF (uConj i) (uRep k) := by
  decide

theorem exists_conj_eq_uRep {x : Fin 6 → ZMod 2} (hx : uMulF x x = 0) (hx0 : x ≠ 0) :
    ∃ i k : Fin 9, uElem x * uElem (uConj i) = uElem (uConj i) * uElem (uRep k) := by
  have hxe : ![x 0, x 1, x 2, x 3, x 4, x 5] = x := by
    funext k
    fin_cases k <;> rfl
  have h := uInvolution_check (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
  rw [hxe] at h
  rcases h hx with h | ⟨i, k, h⟩
  · exact absurd h hx0
  · exact ⟨i, k, by rw [uElem_mul, uElem_mul, h]⟩

theorem uElem_uRep_mul_self (k : Fin 9) : uElem (uRep k) * uElem (uRep k) = 1 := by
  rw [uElem_mul, ← uElem_zero]
  congr 1
  revert k
  decide

theorem uElem_uRep_cases (k : Fin 9) :
    (∃ m : Fin 6, uElem (uRep k) = uRoot m) ∨
      uElem (uRep k) = uRoot 1 * uRoot 4 ∨ uElem (uRep k) = uRoot 2 * uRoot 3 ∨
        uElem (uRep k) = uRoot 0 * uRoot 5 := by
  simp only [uRoot, uElem_mul]
  fin_cases k
  · exact .inl ⟨0, congrArg uElem (by decide)⟩
  · exact .inl ⟨1, congrArg uElem (by decide)⟩
  · exact .inl ⟨2, congrArg uElem (by decide)⟩
  · exact .inl ⟨3, congrArg uElem (by decide)⟩
  · exact .inl ⟨4, congrArg uElem (by decide)⟩
  · exact .inl ⟨5, congrArg uElem (by decide)⟩
  · exact .inr (.inl (congrArg uElem (by decide)))
  · exact .inr (.inr (.inl (congrArg uElem (by decide))))
  · exact .inr (.inr (.inr (congrArg uElem (by decide))))

end Involution

section Weyl

@[expose] def uWeyl {i j : Fin 4} (hij : i ≠ j) : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  SpecialLinearGroup.transvection hij 1 * SpecialLinearGroup.transvection hij.symm 1 *
    SpecialLinearGroup.transvection hij 1

theorem exists_mul_uRoot_zero_eq (k : Fin 6) :
    ∃ l : SpecialLinearGroup (Fin 4) (ZMod 2), l * uRoot 0 = uRoot k * l := by
  fin_cases k
  · exact ⟨1, by rw [one_mul, mul_one]; rfl⟩
  · exact ⟨uWeyl (show (1 : Fin 4) ≠ 2 by decide), by decide⟩
  · exact ⟨uWeyl (show (1 : Fin 4) ≠ 3 by decide), by decide⟩
  · exact ⟨uWeyl (show (0 : Fin 4) ≠ 2 by decide) * uWeyl (show (0 : Fin 4) ≠ 1 by decide),
      by decide⟩
  · exact ⟨uWeyl (show (0 : Fin 4) ≠ 3 by decide) * uWeyl (show (0 : Fin 4) ≠ 1 by decide),
      by decide⟩
  · exact ⟨uWeyl (show (0 : Fin 4) ≠ 2 by decide) * uWeyl (show (1 : Fin 4) ≠ 3 by decide),
      by decide⟩

end Weyl

section Torus

theorem sl2_torus_pow_three :
    (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (1 : ZMod 2)) ^ 3 = 1 := by
  decide

theorem sl2_torus_ne_one :
    SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : ZMod 2) *
      SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (1 : ZMod 2) ≠ 1 := by
  decide

end Torus

end CFSG.SeitzReduction.LinearPilot
