module

public import CFSG.LargeExtraspecial.DW37Input
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LargeExtraspecial.DW

open Matrix

variable {m : ℕ}

@[expose] def affMat (w : Fin m → ZMod 2) (g : Matrix (Fin m) (Fin m) (ZMod 2)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2) :=
  Matrix.of fun i j => Fin.lastCases (motive := fun _ => ZMod 2)
    (Fin.lastCases (motive := fun _ => ZMod 2) 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases (motive := fun _ => ZMod 2) (w i') (fun j' => g i' j') j) i

@[simp] theorem affMat_last_last (w : Fin m → ZMod 2) (g : Matrix (Fin m) (Fin m) (ZMod 2)) :
    affMat w g (Fin.last m) (Fin.last m) = 1 := by
  simp [affMat]

@[simp] theorem affMat_last_castSucc (w : Fin m → ZMod 2) (g : Matrix (Fin m) (Fin m) (ZMod 2))
    (j : Fin m) : affMat w g (Fin.last m) j.castSucc = 0 := by
  simp [affMat]

@[simp] theorem affMat_castSucc_last (w : Fin m → ZMod 2) (g : Matrix (Fin m) (Fin m) (ZMod 2))
    (i : Fin m) : affMat w g i.castSucc (Fin.last m) = w i := by
  simp [affMat]

@[simp] theorem affMat_castSucc_castSucc (w : Fin m → ZMod 2)
    (g : Matrix (Fin m) (Fin m) (ZMod 2)) (i j : Fin m) :
    affMat w g i.castSucc j.castSucc = g i j := by
  simp [affMat]

theorem affMat_mul (w w' : Fin m → ZMod 2) (g g' : Matrix (Fin m) (Fin m) (ZMod 2)) :
    affMat w g * affMat w' g' = affMat (w + g *ᵥ w') (g * g') := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, mulVec, dotProduct, add_comm]

theorem affMat_zero_one : affMat (0 : Fin m → ZMod 2) 1 = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem det_affMat (w : Fin m → ZMod 2) (g : Matrix (Fin m) (Fin m) (ZMod 2)) :
    (affMat w g).det = g.det := by
  rw [Matrix.det_succ_row _ (Fin.last m), Fin.sum_univ_castSucc]
  have hsub : (affMat w g).submatrix (Fin.last m).succAbove (Fin.last m).succAbove = g := by
    ext i j
    simp
  simp only [affMat_last_castSucc, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
    affMat_last_last, mul_one, hsub, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow,
    one_mul]

theorem affMat_injective {w w' : Fin m → ZMod 2} {g g' : Matrix (Fin m) (Fin m) (ZMod 2)}
    (h : affMat w g = affMat w' g') : w = w' ∧ g = g' := by
  refine ⟨funext fun i => ?_, Matrix.ext fun i j => ?_⟩
  · have := congrFun (congrFun h i.castSucc) (Fin.last m)
    simpa using this
  · have := congrFun (congrFun h i.castSucc) j.castSucc
    simpa using this

theorem det_eq_one_of_ne_zero_zmod_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : Matrix ι ι (ZMod 2)} (h : g.det ≠ 0) : g.det = 1 := by
  revert h
  generalize g.det = d
  revert d
  decide

theorem coe_cornerTransvection_eq_affMat (hN : 2 ≤ m + 1) :
    ((cornerTransvection hN : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) = affMat (Pi.single ⟨0, by omega⟩ 1) 1 := by
  rw [coe_cornerTransvection]
  have hm : m ≠ 0 := by omega
  have hi : ∀ i : Fin m, (i : ℕ) ≠ m := fun i => i.isLt.ne
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.one_apply, Matrix.single_apply, Pi.single_apply, Fin.ext_iff, hm, hi,
      (Fin.castSucc_ne_last _).symm, eq_comm]

theorem exists_eq_affMat_of_commute (hN : 2 ≤ m + 1)
    {M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)} (hdet : M.det ≠ 0)
    (hc : M * (cornerTransvection hN : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) =
      (cornerTransvection hN : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) * M) :
    ∃ w g, M = affMat w g := by
  rw [coe_cornerTransvection_eq_affMat] at hc
  set i₀ : Fin m := ⟨0, by omega⟩
  have hrow : ∀ j : Fin m, M (Fin.last m) j.castSucc = 0 := by
    intro j
    have h := congrFun (congrFun hc i₀.castSucc) j.castSucc
    simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, affMat_castSucc_castSucc,
      affMat_castSucc_last, affMat_last_castSucc] at h
    simpa [Matrix.one_apply, Pi.single_apply, i₀] using h
  have hdiag : M (Fin.last m) (Fin.last m) = M i₀.castSucc i₀.castSucc := by
    have h := congrFun (congrFun hc i₀.castSucc) (Fin.last m)
    simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, affMat_castSucc_castSucc,
      affMat_castSucc_last, affMat_last_last] at h
    simp [Matrix.one_apply, Pi.single_apply, i₀] at h ⊢
    linear_combination -h
  have hlast : M (Fin.last m) (Fin.last m) = 1 := by
    by_contra hne
    have h0 : M (Fin.last m) (Fin.last m) = 0 := by
      revert hne
      generalize M (Fin.last m) (Fin.last m) = d
      revert d
      decide
    refine hdet (Matrix.det_eq_zero_of_row_eq_zero (Fin.last m) fun j => ?_)
    induction j using Fin.lastCases with
    | last => exact h0
    | cast j => exact hrow j
  obtain ⟨w, hw⟩ : ∃ w : Fin m → ZMod 2, ∀ i, M i.castSucc (Fin.last m) = w i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Matrix (Fin m) (Fin m) (ZMod 2),
      ∀ i j, M i.castSucc j.castSucc = g i j :=
    ⟨Matrix.of fun i j => M i.castSucc j.castSucc, fun _ _ => rfl⟩
  refine ⟨w, g, Matrix.ext fun i j => ?_⟩
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  · rw [hlast, affMat_last_last]
  · rw [hrow, affMat_last_castSucc]
  · rw [hw, affMat_castSucc_last]
  · rw [hg, affMat_castSucc_castSucc]

end CFSG.LargeExtraspecial.DW
