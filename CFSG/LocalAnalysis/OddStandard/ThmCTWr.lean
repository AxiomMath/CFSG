module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import CFSG.LocalAnalysis.OddStandard.ThmCTBasic

public section

namespace CFSG.OddStandard.ThmC.T

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

section D8Action

open DihedralGroup

def D8smul : DihedralGroup 4 → ZMod 4 → ZMod 4
  | r i, x => x - i
  | sr i, x => i - x

theorem D8smul_one : ∀ x : ZMod 4, D8smul 1 x = x := by decide +kernel

theorem D8smul_mul : ∀ (a b : DihedralGroup 4) (x : ZMod 4),
    D8smul (a * b) x = D8smul a (D8smul b x) := by decide +kernel

theorem D8smul_faithful : ∀ a b : DihedralGroup 4, (∀ x : ZMod 4, D8smul a x = D8smul b x) →
    a = b := by decide +kernel

end D8Action

end CFSG.OddStandard.ThmC.T
