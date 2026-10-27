module

public import CFSG.GH74.GLS.Stage4.RestNotation

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair

variable {G : Type} [Group G]

theorem root_p1 (D : Ch6Notation G) : D.root 1 = D.X₁ := by simp [Ch6Notation.root]
theorem root_p2 (D : Ch6Notation G) : D.root 2 = conjBy (D.a ^ 2) D.X₂' := by
  simp [Ch6Notation.root]
theorem root_p3 (D : Ch6Notation G) : D.root 3 = conjBy D.a D.X₁' := by simp [Ch6Notation.root]
theorem root_p4 (D : Ch6Notation G) : D.root 4 = D.X₂ := by simp [Ch6Notation.root]
theorem root_p5 (D : Ch6Notation G) : D.root 5 = conjBy (D.a ^ 2) D.X₁ := by
  simp [Ch6Notation.root]
theorem root_p6 (D : Ch6Notation G) : D.root 6 = conjBy D.a D.X₂' := by simp [Ch6Notation.root]
theorem root_m1 (D : Ch6Notation G) : D.root (-1) = D.X₁' := by simp [Ch6Notation.root]
theorem root_m2 (D : Ch6Notation G) : D.root (-2) = conjBy (D.a ^ 2) D.X₂ := by
  simp [Ch6Notation.root]
theorem root_m3 (D : Ch6Notation G) : D.root (-3) = conjBy D.a D.X₁ := by simp [Ch6Notation.root]
theorem root_m4 (D : Ch6Notation G) : D.root (-4) = D.X₂' := by simp [Ch6Notation.root]
theorem root_m5 (D : Ch6Notation G) : D.root (-5) = conjBy (D.a ^ 2) D.X₁' := by
  simp [Ch6Notation.root]
theorem root_m6 (D : Ch6Notation G) : D.root (-6) = conjBy D.a D.X₂ := by simp [Ch6Notation.root]

end CFSG.GH74.GLS.Stage4.Rest
