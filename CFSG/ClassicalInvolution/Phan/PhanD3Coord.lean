module

public import CFSG.ClassicalInvolution.ModelFacts.MF15Basic

public section

namespace CFSG.ClassicalInvolution.PhanD4

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.MF15

section Coord

variable {F : Type} [Field F]

@[expose] def vecXY (x y : Fin 4 → F) : Fin 4 ⊕ Fin 4 → F := Sum.elim x y

omit [Field F] in
@[simp] theorem vecXY_inl (x y : Fin 4 → F) (i : Fin 4) : vecXY x y (.inl i) = x i := rfl

omit [Field F] in
@[simp] theorem vecXY_inr (x y : Fin 4 → F) (i : Fin 4) : vecXY x y (.inr i) = y i := rfl

omit [Field F] in
theorem vecXY_eta (v : Fin 4 ⊕ Fin 4 → F) :
    v = vecXY (fun i => v (.inl i)) (fun i => v (.inr i)) := by
  ext s; cases s <;> rfl

theorem polar_vecXY (x y x' y' : Fin 4 → F) :
    polar (quadPlus 4 F) (vecXY x y) (vecXY x' y') = ∑ i, (x i * y' i + x' i * y i) := by
  rw [polar_quadPlus]
  simp

theorem Q_vecXY (x y : Fin 4 → F) :
    quadPlus 4 F (vecXY x y) = ∑ i, x i * y i := by
  rw [quadPlus_apply]
  simp

@[expose] noncomputable def frame0 : Frame (quadPlus 4 F) :=
  frameOfVectors (vecXY ![1, 0, 0, 0] ![0, 0, 0, 0]) (vecXY ![0, 0, 0, 0] ![1, 0, 0, 0])
    (vecXY ![0, 1, 0, 0] ![0, 0, 0, 0]) (vecXY ![0, 0, 0, 0] ![0, 1, 0, 0])
    (by simp [Q_vecXY, Fin.sum_univ_four]) (by simp [Q_vecXY, Fin.sum_univ_four])
    (by simp [polar_vecXY, Fin.sum_univ_four])
    (by simp [Q_vecXY, Fin.sum_univ_four]) (by simp [Q_vecXY, Fin.sum_univ_four])
    (by simp [polar_vecXY, Fin.sum_univ_four])
    (by simp [polar_vecXY, Fin.sum_univ_four]) (by simp [polar_vecXY, Fin.sum_univ_four])
    (by simp [polar_vecXY, Fin.sum_univ_four]) (by simp [polar_vecXY, Fin.sum_univ_four])

@[expose] noncomputable def frame2 : Frame (quadPlus 4 F) :=
  frameOfVectors (vecXY ![0, 0, 1, 0] ![0, 0, 0, 0]) (vecXY ![0, 0, 0, 0] ![0, 0, 1, 0])
    (vecXY ![0, 0, 0, 1] ![0, 0, 0, 0]) (vecXY ![0, 0, 0, 0] ![0, 0, 0, 1])
    (by simp [Q_vecXY, Fin.sum_univ_four]) (by simp [Q_vecXY, Fin.sum_univ_four])
    (by simp [polar_vecXY, Fin.sum_univ_four])
    (by simp [Q_vecXY, Fin.sum_univ_four]) (by simp [Q_vecXY, Fin.sum_univ_four])
    (by simp [polar_vecXY, Fin.sum_univ_four])
    (by simp [polar_vecXY, Fin.sum_univ_four]) (by simp [polar_vecXY, Fin.sum_univ_four])
    (by simp [polar_vecXY, Fin.sum_univ_four]) (by simp [polar_vecXY, Fin.sum_univ_four])

@[expose] noncomputable def frame1 (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) :
    Frame (quadPlus 4 F) :=
  frameOfVectors (vecXY ![1, 0, 1, 0] ![-1, 0, 1, 0])
    (vecXY ![-1 / 4, 0, 1 / 4, 0] ![1 / 4, 0, 1 / 4, 0])
    (vecXY ![0, 1, 0, 1] ![0, -ε, 0, ε])
    (vecXY ![0, -1 / (4 * ε), 0, 1 / (4 * ε)] ![0, 1 / 4, 0, 1 / 4])
    (by simp [Q_vecXY, Fin.sum_univ_four]) (by simp [Q_vecXY, Fin.sum_univ_four]; ring)
    (by simp [polar_vecXY, Fin.sum_univ_four]; field_simp; ring)
    (by simp [Q_vecXY, Fin.sum_univ_four])
    (by simp [Q_vecXY, Fin.sum_univ_four]; field_simp; ring)
    (by simp [polar_vecXY, Fin.sum_univ_four]; field_simp; ring)
    (by simp [polar_vecXY, Fin.sum_univ_four]) (by simp [polar_vecXY, Fin.sum_univ_four])
    (by simp [polar_vecXY, Fin.sum_univ_four]) (by simp [polar_vecXY, Fin.sum_univ_four])

theorem La_neg_one_frame0 (X Y : Fin 4 → F) :
    (frame0 (F := F)).La (-1) (vecXY X Y) =
      vecXY ![-X 0, -X 1, X 2, X 3] ![-Y 0, -Y 1, Y 2, Y 3] := by
  rw [Frame.La_neg_one_apply]
  ext s
  rcases s with i | i <;> fin_cases i <;>
  simp [Frame.incl_apply, Frame.coords_apply, frame0, frameOfVectors, Frame.e₁, Frame.f₁,
    Frame.e₂, Frame.f₂, polar_vecXY, Fin.sum_univ_four] <;> ring

theorem La_neg_one_frame2 (X Y : Fin 4 → F) :
    (frame2 (F := F)).La (-1) (vecXY X Y) =
      vecXY ![X 0, X 1, -X 2, -X 3] ![Y 0, Y 1, -Y 2, -Y 3] := by
  rw [Frame.La_neg_one_apply]
  ext s
  rcases s with i | i <;> fin_cases i <;>
  simp [Frame.incl_apply, Frame.coords_apply, frame2, frameOfVectors, Frame.e₁, Frame.f₁,
    Frame.e₂, Frame.f₂, polar_vecXY, Fin.sum_univ_four] <;> ring

theorem La_neg_one_frame1 (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) (X Y : Fin 4 → F) :
    (frame1 ε hε h4).La (-1) (vecXY X Y) =
      vecXY ![Y 0, Y 1 / ε, -Y 2, -Y 3 / ε] ![X 0, ε * X 1, -X 2, -ε * X 3] := by
  rw [Frame.La_neg_one_apply]
  ext s
  rcases s with i | i <;> fin_cases i <;>
  simp [Frame.incl_apply, Frame.coords_apply, frame1, frameOfVectors, Frame.e₁, Frame.f₁,
    Frame.e₂, Frame.f₂, polar_vecXY, Fin.sum_univ_four] <;> field_simp <;> ring

theorem frame1_comm_frame0 (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) :
    (frame0 (F := F)).La (-1) * (frame1 ε hε h4).La (-1) =
      (frame1 ε hε h4).La (-1) * (frame0 (F := F)).La (-1) := by
  refine LinearEquiv.ext fun x => ?_
  rw [vecXY_eta x]
  simp only [LinearEquiv.mul_apply, La_neg_one_frame0, La_neg_one_frame1]
  ext s
  rcases s with i | i <;> fin_cases i <;> simp [neg_div]

theorem frame2_comm_frame1 (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) :
    (frame2 (F := F)).La (-1) * (frame1 ε hε h4).La (-1) =
      (frame1 ε hε h4).La (-1) * (frame2 (F := F)).La (-1) := by
  refine LinearEquiv.ext fun x => ?_
  rw [vecXY_eta x]
  simp only [LinearEquiv.mul_apply, La_neg_one_frame2, La_neg_one_frame1]
  ext s
  rcases s with i | i <;> fin_cases i <;> simp [neg_div]

end Coord

end CFSG.ClassicalInvolution.PhanD4
