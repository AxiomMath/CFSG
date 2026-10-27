module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.GH74.QTGen4.Recog.G23

abbrev M2 : Type := Matrix (Fin 2) (Fin 2) (ZMod 3)

def mx : M2 := !![1, 1; 0, 1]

def my : M2 := !![1, 0; 1, 1]

def mxi : M2 := !![1, 2; 0, 1]

def myi : M2 := !![1, 0; 2, 1]

def msig : M2 := !![1, 0; 0, 2]

def gen4 : Fin 4 → M2 := ![mx, mxi, my, myi]

theorem mx_eq : mx = !![1, 1; 0, 1] := by decide +kernel

theorem my_eq : my = !![1, 0; 1, 1] := by decide +kernel

theorem mxi_eq : mxi = !![1, 2; 0, 1] := by decide +kernel

theorem myi_eq : myi = !![1, 0; 2, 1] := by decide +kernel

theorem msig_eq : msig = !![1, 0; 0, 2] := by decide +kernel

theorem gen4_eq : gen4 = ![mx, mxi, my, myi] := by decide +kernel

@[expose] def evM (w : List (Fin 4)) : M2 := w.foldl (fun A i => A * gen4 i) 1

def allW : ℕ → List (List (Fin 4))
  | 0 => [[]]
  | n + 1 => allW n ++ (allW n).flatMap fun w => (List.finRange 4).map fun i => w ++ [i]

theorem sl_gen_words : ∀ A : M2, A.det = 1 → ∃ w ∈ allW 6, evM w = A := by
  let wordFor : M2 → List (Fin 4) := fun A =>
    match (A 0 0).val, (A 0 1).val, (A 1 0).val, (A 1 1).val with
    | 0, 1, 2, 0 => [0, 3, 0]
    | 0, 1, 2, 1 => [0, 3]
    | 0, 1, 2, 2 => [0, 3, 1]
    | 0, 2, 1, 0 => [1, 2, 1]
    | 0, 2, 1, 1 => [1, 2]
    | 0, 2, 1, 2 => [1, 2, 0]
    | 1, 0, 0, 1 => []
    | 1, 0, 1, 1 => [2]
    | 1, 0, 2, 1 => [3]
    | 1, 1, 0, 1 => [0]
    | 1, 1, 1, 2 => [2, 0]
    | 1, 1, 2, 0 => [3, 0]
    | 1, 2, 0, 1 => [1]
    | 1, 2, 1, 0 => [2, 1]
    | 1, 2, 2, 2 => [3, 1]
    | 2, 0, 0, 2 => [0, 2, 0, 2]
    | 2, 0, 1, 2 => [0, 2, 0]
    | 2, 0, 2, 2 => [1, 3, 1]
    | 2, 1, 0, 2 => [2, 0, 2]
    | 2, 1, 1, 1 => [0, 2]
    | 2, 1, 2, 0 => [1, 3, 0]
    | 2, 2, 0, 2 => [3, 1, 3]
    | 2, 2, 1, 0 => [0, 2, 1]
    | 2, 2, 2, 1 => [1, 3]
    | _, _, _, _ => []
  have checked : ∀ A : M2, A.det = 1 →
      wordFor A ∈ allW 6 ∧ evM (wordFor A) = A := by
    dsimp only [wordFor]
    decide +kernel
  intro A hA
  exact ⟨wordFor A, (checked A hA).1, (checked A hA).2⟩

theorem sl_unique_invol : ∀ A : M2, A.det = 1 → A * A = 1 → A ≠ 1 → A = -1 := by
  decide +kernel

theorem sl_rel_x : mx * mx * mx = 1 ∧ my * my * my = 1 ∧
    myi * mxi * my * mxi * myi * mx = 1 := by
  decide +kernel

theorem sl_xy_sq : (mx * my) * (mx * my) = -1 := by decide +kernel

theorem commutant_scalar : ∀ N : M2, N * mx = mx * N → N * my = my * N →
    ∃ c : ZMod 3, N = c • (1 : M2) := by
  decide +kernel

theorem outer_square_scalar : ∀ g : M2, g.det = -1 → ∀ c : ZMod 3, g * g = c • (1 : M2) →
    c = 1 := by
  decide +kernel

theorem outer_involution_conj : ∀ g : M2, g.det = -1 → g * g = 1 →
    ∃ h : M2, h.det ≠ 0 ∧ h * g = msig * h := by
  decide +kernel

theorem centralizer_Q8 : ∀ A : M2, A.det = 1 →
    (∀ q : M2, q.det = 1 → q ^ 4 = 1 → A * q = q * A) → A = 1 ∨ A = -1 := by
  decide +kernel

end CFSG.GH74.QTGen4.Recog.G23
