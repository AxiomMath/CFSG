module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyDef

public section

namespace CFSG.EvenSporadicStandard.TwoHS

theorem sr_ne_one : ∀ k : ZMod 4, (DihedralGroup.sr k : DihedralGroup 4) ≠ 1 := by decide

theorem sr_ne_r2 : ∀ k : ZMod 4, (DihedralGroup.sr k : DihedralGroup 4) ≠ DihedralGroup.r 2 := by
  decide

theorem sr_sq : ∀ k : ZMod 4, (DihedralGroup.sr k : DihedralGroup 4) * DihedralGroup.sr k = 1 := by
  decide

theorem dihChar_one (b : ℤˣ) : dihChar b 1 = 1 := by
  rw [DihedralGroup.one_def, dihChar_r]; simp

end CFSG.EvenSporadicStandard.TwoHS
