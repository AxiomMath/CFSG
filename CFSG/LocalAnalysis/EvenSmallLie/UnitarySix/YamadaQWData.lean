module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQCoord

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

@[expose] def hiSum (v : Fin 8 → ZMod 2) : ZMod 2 := v 4 + v 5 + v 6 + v 7

@[expose] def mTe (ε : Bool) : Matrix (Fin 8) (Fin 8) (ZMod 2) := if ε then mT else 1

set_option maxRecDepth 10000 in
theorem hiSum_mX (k : Fin 4) (v : Fin 8 → ZMod 2) : hiSum ((mX k).mulVec v) = hiSum v := by
  revert k v; decide

set_option maxRecDepth 10000 in
theorem hiSum_mT (v : Fin 8 → ZMod 2) : hiSum (mT.mulVec v) = hiSum v := by
  revert v; decide

set_option maxRecDepth 10000 in
theorem hiSum_comm_mX (k : Fin 4) (v : Fin 8 → ZMod 2) : hiSum (v + (mX k).mulVec v) = 0 := by
  revert k v; decide

set_option maxRecDepth 10000 in
theorem hiSum_comm_mT (v : Fin 8 → ZMod 2) : hiSum (v + mT.mulVec v) = 0 := by
  revert v; decide

set_option maxRecDepth 10000 in
theorem augZ_comm_mX (k : Fin 4) (v : Fin 8 → ZMod 2) (hv : hiSum v = 0) :
    augZ (v + (mX k).mulVec v) := by
  revert k v; decide

set_option maxRecDepth 10000 in
theorem augZ_comm_mT (v : Fin 8 → ZMod 2) (hv : hiSum v = 0) : augZ (v + mT.mulVec v) := by
  revert v; decide

theorem hiSum_zero : hiSum 0 = 0 := by decide

theorem hiSum_add (v w : Fin 8 → ZMod 2) (hv : hiSum v = 0) (hw : hiSum w = 0) :
    hiSum (v + w) = 0 := by
  simp only [hiSum, Pi.add_apply] at *
  rw [show v 4 + w 4 + (v 5 + w 5) + (v 6 + w 6) + (v 7 + w 7) =
    (v 4 + v 5 + v 6 + v 7) + (w 4 + w 5 + w 6 + w 7) by ring, hv, hw, add_zero]

@[expose] def vw₁ : Fin 8 → ZMod 2 := ![1, 1, 0, 0, 0, 0, 0, 0]
@[expose] def vw₂ : Fin 8 → ZMod 2 := ![1, 0, 1, 0, 0, 0, 0, 0]
@[expose] def vz : Fin 8 → ZMod 2 := ![1, 1, 1, 1, 0, 0, 0, 0]
@[expose] def vn : Fin 8 → ZMod 2 := ![0, 0, 0, 0, 1, 1, 1, 1]

theorem moved_test (k : Fin 4) (ε : Bool) (hkε : ¬ (k = 0 ∧ ε = false)) :
    (mX k * mTe ε).mulVec vw₁ ≠ vw₁ ∨ (mX k * mTe ε).mulVec vw₂ ≠ vw₂ ∨
      (mX k * mTe ε).mulVec vn ≠ vn := by
  revert k ε; decide

set_option maxRecDepth 10000 in
theorem span_Z₂S (v : Fin 8 → ZMod 2) (hv : augZ v ∧ hiPart v = 0) :
    ∃ a b c : ZMod 2, v = a • vw₁ + b • vw₂ + c • vz := by
  revert v; decide

set_option maxRecDepth 10000 in
theorem span_V₁ (v : Fin 8 → ZMod 2) (hv : mU₁.mulVec v = v ∧ mU₂.mulVec v = v) :
    ∃ a b : ZMod 2, v = a • vz + b • vn := by
  revert v; decide

theorem comm_vw₁ : (fun v => v + mU₁.mulVec v) (Pi.single 4 1 + mT.mulVec (Pi.single 4 1)) =
    vw₁ := by decide

theorem comm_vw₂ : (fun v => v + mU₂.mulVec v) (Pi.single 4 1 + mT.mulVec (Pi.single 4 1)) =
    vw₂ := by decide

theorem comm_vz : (fun v => v + mU₁.mulVec v) (Pi.single 0 1 + mU₂.mulVec (Pi.single 0 1)) =
    vz := by decide

theorem comm_vn : (fun v => v + mU₁.mulVec v) (Pi.single 4 1 + mU₂.mulVec (Pi.single 4 1)) =
    vn := by decide

set_option maxRecDepth 10000 in
theorem fix_mX_eq_comm (k : Fin 4) (hk : k ≠ 0) (v : Fin 8 → ZMod 2)
    (hv : (mX k).mulVec v = v) : ∃ w, v = w + (mX k).mulVec w := by
  revert k v; decide

end CFSG.EvenSmallLie.UnitarySix.YamadaD
