module

public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.M22Plane

open Equiv CFSG.Blueprint CFSG.Sporadic.Mathieu

@[expose] def gen : Fin 3 → Perm (Fin 22) := ![m22gA, m22gB, m22gB⁻¹]

@[expose] def wp (w : List (Fin 3)) : Perm (Fin 22) := (w.map gen).prod

def wx : List (Fin 3) := [1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1]
def wy : List (Fin 3) := [1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2]
def w0 : List (Fin 3) := [0]
def w1 : List (Fin 3) := [0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0]
def w2 : List (Fin 3) := [2, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1]
def w3 : List (Fin 3) := [0, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2]

@[expose] def sp : Fin 8 → Perm (Fin 22) :=
  ![wp w0, wp w1, wp w2, wp w3, (wp w0)⁻¹, (wp w1)⁻¹, (wp w2)⁻¹, (wp w3)⁻¹]

def wb : List (Fin 8) := [0, 1, 0, 5, 7, 5, 6, 1, 6, 3]

theorem wp_x3 : wp wx ^ 3 = 1 := by unfold wp wx gen; decide +kernel
theorem wp_y3 : wp wy ^ 3 = 1 := by unfold wp wy gen; decide +kernel
theorem wp_xy : wp wx * wp wy = wp wy * wp wx := by unfold wp wx wy gen; decide +kernel
theorem wp_x_ne_one : wp wx ≠ 1 := by unfold wp wx gen; decide +kernel
theorem wp_y_ne_one : wp wy ≠ 1 := by unfold wp wy gen; decide +kernel
theorem wp_y_ne_x : wp wy ≠ wp wx := by unfold wp wx wy gen; decide +kernel
theorem wp_y_ne_xx : wp wy ≠ wp wx * wp wx := by unfold wp wx wy gen; decide +kernel
theorem wp_s0_comm : wp w0 * wp wx = wp wx * wp w0 := by unfold wp w0 wx gen; decide +kernel
theorem wp_s1_comm : wp w1 * (wp wx * wp wy * wp wy) = (wp wx * wp wy * wp wy) * wp w1 := by
  unfold wp w1 wx wy gen; decide +kernel
theorem wp_s2_comm : wp w2 * wp wx = wp wx * wp w2 := by unfold wp w2 wx gen; decide +kernel
theorem wp_s3_comm : wp w3 * wp wy = wp wy * wp w3 := by unfold wp w3 wy gen; decide +kernel
theorem wp_xyy_ne_one : wp wx * wp wy * wp wy ≠ 1 := by unfold wp wx wy gen; decide +kernel

theorem wp_w0 : wp w0 = m22gA := by unfold wp w0 gen; decide +kernel

theorem m22_b_word : m22gB = (wb.map sp).prod := by
  unfold wb sp wp w0 w1 w2 w3 gen; decide +kernel

end CFSG.HardMathSupport.Solomon.Coordinator.M22Plane
