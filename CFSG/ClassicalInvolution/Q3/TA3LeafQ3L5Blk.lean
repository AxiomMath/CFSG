module

public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearComponent
public import CFSG.GH74.Filter.ClassicalOdd.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q3L5

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] {k m : ℕ}

@[expose] def p₁ (g : Matrix (Fin (k + m)) (Fin (k + m)) K) : Matrix (Fin k) (Fin k) K :=
  (reindex finSumFinEquiv.symm finSumFinEquiv.symm g).toBlocks₁₁

@[expose] def p₂ (g : Matrix (Fin (k + m)) (Fin (k + m)) K) : Matrix (Fin m) (Fin m) K :=
  (reindex finSumFinEquiv.symm finSumFinEquiv.symm g).toBlocks₂₂

@[simp] theorem p₁_diagBlock (A : Matrix (Fin k) (Fin k) K) (B : Matrix (Fin m) (Fin m) K) :
    p₁ (diagBlock A B) = A := by
  simp [p₁, diagBlock, toBlocks₁₁, fromBlocks]
  rfl

@[simp] theorem p₂_diagBlock (A : Matrix (Fin k) (Fin k) K) (B : Matrix (Fin m) (Fin m) K) :
    p₂ (diagBlock A B) = B := by
  simp [p₂, diagBlock, toBlocks₂₂, fromBlocks]
  rfl

theorem eq_diagBlock_p (h2 : (2 : K) ≠ 0) {g : Matrix (Fin (k + m)) (Fin (k + m)) K}
    (hg : g * diagBlock (-1) 1 = diagBlock (-1) 1 * g) : g = diagBlock (p₁ g) (p₂ g) := by
  obtain ⟨A, D, rfl⟩ := CFSG.RankThree.PartTwo.Census.eq_diagBlock_of_comm h2 hg
  rw [p₁_diagBlock, p₂_diagBlock]

theorem diagBlock_comm_neg (A : Matrix (Fin k) (Fin k) K) (B : Matrix (Fin m) (Fin m) K) :
    diagBlock A B * diagBlock (-1) 1 = diagBlock (-1) 1 * diagBlock A B := by
  rw [diagBlock_mul, diagBlock_mul]
  simp

theorem p₁_mul (h2 : (2 : K) ≠ 0) {g h : Matrix (Fin (k + m)) (Fin (k + m)) K}
    (hg : g * diagBlock (-1) 1 = diagBlock (-1) 1 * g)
    (hh : h * diagBlock (-1) 1 = diagBlock (-1) 1 * h) : p₁ (g * h) = p₁ g * p₁ h := by
  rw [eq_diagBlock_p h2 hg, eq_diagBlock_p h2 hh, diagBlock_mul]
  simp

theorem p₂_mul (h2 : (2 : K) ≠ 0) {g h : Matrix (Fin (k + m)) (Fin (k + m)) K}
    (hg : g * diagBlock (-1) 1 = diagBlock (-1) 1 * g)
    (hh : h * diagBlock (-1) 1 = diagBlock (-1) 1 * h) : p₂ (g * h) = p₂ g * p₂ h := by
  rw [eq_diagBlock_p h2 hg, eq_diagBlock_p h2 hh, diagBlock_mul]
  simp

theorem det_eq_p (h2 : (2 : K) ≠ 0) {g : Matrix (Fin (k + m)) (Fin (k + m)) K}
    (hg : g * diagBlock (-1) 1 = diagBlock (-1) 1 * g) : g.det = (p₁ g).det * (p₂ g).det := by
  conv_lhs => rw [eq_diagBlock_p h2 hg]
  exact CFSG.GH74.Filter.ClassicalOdd.det_diagBlock _ _

end CFSG.ClassicalInvolution.Q3.TA3.Q3L5
