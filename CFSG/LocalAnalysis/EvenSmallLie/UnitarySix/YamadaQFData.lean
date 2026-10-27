module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQWData

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

@[expose] def frobIdx : Fin 4 → Fin 4 := ![0, 1, 3, 2]

@[expose] def mPhi (l : Fin 4 → ZMod 2) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j =>
    if hj : (j : ℕ) < 4 then (if (i : ℕ) = frobIdx ⟨j, hj⟩ then 1 else 0)
    else (if (i : ℕ) = 4 + frobIdx ⟨j - 4, by omega⟩ then 1 else 0) +
      (mX (frobIdx ⟨j - 4, by omega⟩)).mulVec (lo l) i

set_option maxRecDepth 20000 in
theorem hiSum_mPhi (l : Fin 4 → ZMod 2) (v : Fin 8 → ZMod 2) :
    hiSum ((mPhi l).mulVec v) = hiSum v := by
  revert l v; decide +kernel

set_option maxRecDepth 20000 in
theorem hiSum_comm_mPhi (l : Fin 4 → ZMod 2) (v : Fin 8 → ZMod 2) :
    hiSum (v + (mPhi l).mulVec v) = 0 := by
  revert l v; decide +kernel

set_option maxRecDepth 20000 in
theorem augZ_comm_mPhi (l : Fin 4 → ZMod 2) (v : Fin 8 → ZMod 2) (hv : hiSum v = 0) :
    augZ (v + (mPhi l).mulVec v) := by
  revert l v; decide +kernel

set_option maxRecDepth 20000 in
theorem augZ_mPhi (l : Fin 4 → ZMod 2) (v : Fin 8 → ZMod 2) :
    augZ ((mPhi l).mulVec v) ↔ augZ v := by
  revert l v; decide +kernel

theorem moved_test_phi (l : Fin 4 → ZMod 2) (k : Fin 4) (ε : Bool) :
    (mX k * mTe ε * mPhi l).mulVec vw₁ ≠ vw₁ ∨ (mX k * mTe ε * mPhi l).mulVec vw₂ ≠ vw₂ ∨
      (mX k * mTe ε * mPhi l).mulVec vn ≠ vn := by
  revert l k ε; decide

theorem col_mPhi_lo (l : Fin 4 → ZMod 2) (k : Fin 4) :
    (fun i => mPhi l i ⟨k, by omega⟩) = Pi.single ⟨frobIdx k, by omega⟩ 1 := by
  revert l k; decide

theorem col_mPhi_hi (l : Fin 4 → ZMod 2) (k : Fin 4) :
    (fun i => mPhi l i ⟨k + 4, by omega⟩) =
      Pi.single ⟨frobIdx k + 4, by omega⟩ 1 + (mX (frobIdx k)).mulVec (lo l) := by
  revert l k; decide

end CFSG.EvenSmallLie.UnitarySix.YamadaD
