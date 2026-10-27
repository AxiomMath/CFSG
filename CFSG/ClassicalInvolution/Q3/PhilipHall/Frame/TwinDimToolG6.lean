module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Ass11

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_e4X (hx : P23E4Exit n) (hi : P23E4Ident n) (hmem : P23Members n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) :
    (¬ SecNoExit R e ∧ (ECase1 R W e ∨ SecAE R e 6)) ∨
      (SecNoExit R e ∧ SecOrthLift R e 6 (piSign 3 1)) := by
  by_cases hno : SecNoExit R e
  · right
    obtain ⟨D⟩ := secDecomp_of_noExit hcit hP hc.std.perp hc.data.he2 hc.data.he1
      (hmem Y R S t K' W u e g hc).1 hno
    exact ⟨hno, D, hi hcit hP Y R S t K' W u e g hc hno D⟩
  · exact Or.inl ⟨hno, hx hcit hP Y R S t K' W u e g hc hno⟩

end Ass11

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
