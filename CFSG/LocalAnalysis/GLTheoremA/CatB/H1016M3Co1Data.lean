module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeData
public import Certificates.Data.CFSGNative.Co1Schreier.Base
public import CFSG.HardMathSupport.Foote.E27.OrbitF3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.Co1Sylow

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.Sporadic.Co1Schreier.Native (decWord)
open CFSG.Monster.B.Pinned (rowsMat)
open CFSG.HardMathSupport.Foote.E27.OrbitF3 (lmulD lidD rowsMat_lmulD)
open scoped Matrix

@[expose] def r0Rows : List (List ℕ) :=
  [[0, 2, 0, 1, 1, 0], [2, 0, 1, 1, 2, 2], [2, 2, 0, 1, 0, 1], [2, 2, 0, 2, 1, 0],
    [1, 1, 1, 2, 1, 2], [0, 0, 2, 0, 2, 2]]

@[expose] def r1Rows : List (List ℕ) :=
  [[2, 2, 1, 0, 0, 0], [0, 2, 1, 2, 0, 2], [1, 1, 0, 1, 2, 0], [1, 0, 2, 1, 0, 1],
    [1, 2, 2, 0, 2, 1], [1, 0, 2, 0, 0, 2]]

@[expose] def m1Rows : List (List ℕ) :=
  [[1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 2, 2], [0, 0, 2, 1, 2, 2],
    [0, 0, 1, 1, 0, 2], [0, 0, 0, 2, 2, 0]]

@[expose] def m2Rows : List (List ℕ) :=
  [[0, 0, 2, 0, 2, 0], [2, 1, 1, 2, 0, 0], [2, 1, 2, 1, 2, 0], [2, 2, 0, 2, 1, 1],
    [1, 0, 1, 2, 1, 1], [0, 2, 2, 1, 0, 0]]

@[expose] def s0Rows : List (List (List ℕ)) :=
  [[[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0],
      [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]],
    [[1, 2, 0, 2, 2, 2], [0, 1, 0, 0, 0, 0], [0, 2, 0, 2, 1, 0],
      [0, 0, 2, 1, 2, 1], [2, 0, 2, 2, 2, 2], [1, 0, 2, 1, 0, 1]],
    [[1, 1, 0, 1, 1, 1], [0, 1, 0, 0, 0, 0], [2, 2, 0, 1, 0, 1],
      [2, 1, 2, 1, 2, 0], [2, 2, 0, 1, 2, 0], [2, 0, 1, 2, 0, 1]],
    [[0, 0, 2, 0, 2, 0], [2, 1, 1, 2, 0, 0], [2, 1, 2, 1, 2, 0],
      [2, 2, 0, 2, 1, 1], [1, 0, 1, 2, 1, 1], [0, 2, 2, 1, 0, 0]],
    [[1, 1, 1, 2, 0, 1], [2, 1, 1, 2, 0, 0], [0, 0, 0, 1, 0, 0],
      [2, 0, 2, 0, 1, 0], [1, 1, 2, 0, 0, 1], [0, 0, 2, 2, 1, 1]],
    [[2, 2, 0, 1, 1, 2], [2, 1, 1, 2, 0, 0], [0, 0, 2, 1, 2, 1],
      [1, 2, 2, 1, 2, 0], [2, 1, 2, 1, 1, 0], [0, 1, 2, 0, 2, 2]],
    [[0, 2, 0, 0, 0, 2], [2, 0, 1, 1, 2, 2], [1, 2, 2, 1, 2, 0],
      [0, 2, 0, 2, 1, 0], [1, 1, 1, 2, 1, 0], [1, 0, 0, 2, 2, 1]],
    [[2, 2, 1, 2, 0, 2], [2, 0, 1, 1, 2, 2], [2, 2, 0, 2, 1, 1],
      [2, 2, 0, 1, 0, 1], [0, 2, 0, 2, 0, 0], [0, 2, 1, 0, 1, 0]],
    [[1, 2, 2, 1, 0, 2], [2, 0, 1, 1, 2, 2], [2, 0, 2, 0, 1, 0],
      [0, 0, 1, 0, 0, 0], [0, 2, 1, 2, 1, 2], [2, 1, 2, 1, 0, 2]],
    [[1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 2, 2],
      [0, 0, 2, 1, 2, 2], [0, 0, 1, 1, 0, 2], [0, 0, 0, 2, 2, 0]],
    [[1, 1, 0, 2, 2, 2], [0, 1, 0, 0, 0, 0], [0, 2, 2, 0, 1, 0],
      [0, 1, 1, 2, 2, 1], [2, 2, 0, 2, 0, 0], [1, 0, 2, 0, 2, 0]],
    [[1, 0, 0, 1, 1, 1], [0, 1, 0, 0, 0, 0], [2, 0, 2, 0, 1, 2],
      [2, 0, 1, 0, 0, 1], [2, 0, 1, 0, 2, 0], [2, 0, 1, 1, 2, 0]],
    [[1, 2, 1, 1, 2, 0], [2, 1, 1, 2, 0, 0], [0, 0, 2, 1, 2, 2],
      [2, 2, 1, 1, 1, 0], [1, 1, 0, 2, 0, 1], [0, 1, 2, 2, 1, 1]],
    [[2, 0, 0, 0, 0, 1], [2, 1, 1, 2, 0, 0], [0, 1, 1, 2, 2, 1],
      [1, 2, 1, 0, 0, 1], [2, 0, 0, 2, 0, 2], [0, 2, 2, 0, 2, 2]],
    [[0, 1, 2, 2, 1, 2], [2, 1, 1, 2, 0, 0], [2, 0, 1, 0, 0, 1],
      [2, 0, 2, 2, 0, 0], [1, 1, 2, 2, 2, 2], [0, 0, 2, 1, 0, 0]],
    [[1, 2, 2, 2, 1, 0], [2, 0, 1, 1, 2, 2], [2, 2, 1, 1, 1, 0],
      [0, 2, 0, 0, 2, 2], [0, 1, 2, 1, 1, 2], [2, 0, 2, 2, 1, 0]],
    [[0, 2, 0, 1, 1, 0], [2, 0, 1, 1, 2, 2], [1, 2, 1, 0, 0, 1],
      [0, 2, 2, 0, 1, 0], [1, 2, 2, 0, 0, 2], [1, 2, 0, 0, 0, 2]],
    [[2, 2, 1, 0, 1, 0], [2, 0, 1, 1, 2, 2], [2, 0, 2, 2, 0, 0],
      [2, 0, 2, 0, 1, 2], [0, 2, 1, 2, 1, 1], [0, 1, 1, 1, 2, 1]],
    [[1, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 2, 2, 0, 1, 1],
      [0, 1, 1, 1, 1, 1], [0, 2, 2, 2, 2, 1], [0, 0, 0, 1, 1, 2]],
    [[1, 0, 0, 2, 2, 2], [0, 1, 0, 0, 0, 0], [0, 0, 1, 1, 1, 0],
      [0, 0, 0, 0, 2, 1], [2, 0, 1, 2, 1, 1], [1, 0, 2, 2, 1, 2]],
    [[1, 2, 0, 1, 1, 1], [0, 1, 0, 0, 0, 0], [2, 2, 1, 2, 2, 0],
      [2, 0, 0, 2, 1, 2], [2, 0, 2, 2, 2, 0], [2, 0, 1, 0, 1, 2]],
    [[2, 1, 0, 2, 2, 0], [2, 1, 1, 2, 0, 0], [0, 0, 0, 0, 2, 1],
      [1, 0, 0, 2, 1, 2], [2, 1, 1, 0, 2, 1], [0, 0, 2, 0, 2, 2]],
    [[0, 2, 2, 1, 0, 1], [2, 1, 1, 2, 0, 0], [2, 0, 0, 2, 1, 2],
      [2, 2, 1, 2, 2, 2], [1, 1, 0, 2, 0, 0], [0, 1, 2, 1, 0, 0]],
    [[1, 0, 1, 0, 1, 2], [2, 1, 1, 2, 0, 0], [0, 1, 1, 1, 1, 1],
      [2, 2, 0, 2, 1, 0], [1, 0, 1, 1, 0, 1], [0, 2, 2, 2, 1, 1]],
    [[2, 2, 1, 1, 2, 1], [2, 0, 1, 1, 2, 2], [2, 2, 1, 2, 2, 2],
      [2, 2, 1, 2, 2, 0], [0, 1, 2, 2, 2, 2], [0, 0, 1, 2, 0, 2]],
    [[1, 2, 2, 0, 2, 1], [2, 0, 1, 1, 2, 2], [2, 2, 0, 2, 1, 0],
      [0, 2, 2, 0, 1, 1], [0, 2, 0, 0, 1, 2], [2, 2, 2, 0, 2, 1]],
    [[0, 2, 0, 2, 2, 1], [2, 0, 1, 1, 2, 2], [1, 0, 0, 2, 1, 2],
      [0, 0, 1, 1, 1, 0], [1, 2, 0, 1, 2, 1], [1, 1, 0, 1, 1, 0]]]

@[expose] def letRows (j : ℤ) : List (List ℕ) :=
  if j = 7 then r0Rows else if j = 8 then r1Rows else lidD 6

@[expose] def wordRows (w : List ℕ) : List (List ℕ) :=
  (decWord w).foldl (fun acc j => lmulD 6 acc (letRows j)) (lidD 6)

@[expose] def gensRows : List (List (List ℕ)) := [lidD 6, m1Rows, m2Rows]

@[expose] def vA (x y z : ZMod 3) : Fin 6 → ZMod 3 := ![x, 0, 0, y, 0, z]

@[expose] def vB (x y z : ZMod 3) : Fin 6 → ZMod 3 := ![0, x, y, z, 0, 0]

theorem words_check : ∀ w ∈ Co1T.Data.qGenWords,
    (∀ j ∈ decWord w, 1 ≤ j ∧ j ≤ 8) ∧ wordRows w ∈ gensRows := by
  decide +kernel

theorem m_words_check : ∃ w₁ ∈ Co1T.Data.qGenWords, ∃ w₂ ∈ Co1T.Data.qGenWords,
    wordRows w₁ = m1Rows ∧ wordRows w₂ = m2Rows := by
  decide +kernel

theorem gens_check : ∀ G ∈ gensRows, G.length = 6 ∧ lmulD 6 G (lmulD 6 G G) = lidD 6 ∧
    ∀ Y ∈ s0Rows, lmulD 6 G Y ∈ s0Rows := by
  decide +kernel

theorem s0_check : lidD 6 ∈ s0Rows ∧ s0Rows.length = 27 := by
  decide +kernel

theorem m_noncomm :
    rowsMat 3 6 m1Rows * rowsMat 3 6 m2Rows ≠ rowsMat 3 6 m2Rows * rowsMat 3 6 m1Rows := by
  rw [← rowsMat_lmulD (d := 6) (A := m1Rows) rfl, ← rowsMat_lmulD (d := 6) (A := m2Rows) rfl]
  decide +kernel

theorem fix_check : ∀ Y ∈ s0Rows, Y = lidD 6 ∨
    (∀ x y z : ZMod 3, rowsMat 3 6 Y *ᵥ vA x y z = vA x y z → x = 0 ∧ y = 0 ∧ z = 0) ∨
    (∀ x y z : ZMod 3, rowsMat 3 6 Y *ᵥ vB x y z = vB x y z → x = 0 ∧ y = 0 ∧ z = 0) := by
  decide +kernel

theorem vA_sub (x y z x' y' z' : ZMod 3) :
    vA x y z - vA x' y' z' = vA (x - x') (y - y') (z - z') := by
  ext i
  fin_cases i <;> simp [vA]

theorem vB_sub (x y z x' y' z' : ZMod 3) :
    vB x y z - vB x' y' z' = vB (x - x') (y - y') (z - z') := by
  ext i
  fin_cases i <;> simp [vB]

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.Co1Sylow
