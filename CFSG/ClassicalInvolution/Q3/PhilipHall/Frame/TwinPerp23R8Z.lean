module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section E8Z

variable {n : ℕ}

@[expose] def P23E8Phi (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e →
      (u * e ∈ zStarOf (rLayer (Om R) u) ∨ SecAE R u 5) → SecAE R e 6 →
        ∀ a ∈ p23ABar t 1 e, ∀ b ∈ p23ABar t 1 e, a * b = b * a

end E8Z

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
