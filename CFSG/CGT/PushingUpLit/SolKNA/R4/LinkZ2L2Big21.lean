module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big13
public import CFSG.ClassicalInvolution.Asc77.AscT8W11
public import CFSG.ClassicalInvolution.AschTight.S19GTrace
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G3Defs
public import CFSG.ClassicalInvolution.Q3.TL4MF163Mat

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section SDCore

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Q : Subgroup X} {r : ℕ}
  {p f : ℕ}

theorem isPGroup_two_of_equiv_quaternion (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) :
    IsPGroup 2 ↥Q := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  refine IsPGroup.of_card (n := 2 + (r - 2)) ?_
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card,
    show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]

end SDCore

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
