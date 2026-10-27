module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHBal
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHAssembly
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHSp
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHTD4Odd

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]

theorem t5BaseAtC_nt_all (t : StatedLieTag) (k e : ℕ) : T5BaseAtC p f t k e Not := by
  cases t with
  | PSL => exact t5BaseAt_nt_psl.toC
  | PSU => exact t5BaseAt_nt_psu.toC
  | PSp => exact t5BaseAt_nt_psp.toC
  | POmegaOdd => exact t5BaseAtC_nt (by decide) (by decide) (fun h => absurd h (by decide))
  | POmegaPlus => exact t5BaseAtC_nt (by decide) (by decide) (fun h => absurd h (by decide))
  | POmegaMinus => exact t5BaseAtC_nt (by decide) (by decide) (fun h => absurd h (by decide))
  | G2 => exact (t5BaseAt_g2 Not).toC
  | F4 => exact t5BaseAtC_nt (by decide) (by decide) (fun h => absurd h (by decide))
  | E6 => exact t5BaseAtC_nt (by decide) (by decide) (fun h => absurd h (by decide))
  | E7 => exact t5BaseAtC_nt (by decide) (by decide) (fun h => absurd h (by decide))
  | E8 => exact t5BaseAtC_nt (by decide) (by decide) (fun h => absurd h (by decide))
  | twistedE6 => exact t5BaseAtC_nt (by decide) (by decide) (fun h => absurd h (by decide))
  | trialityD4 => exact (t5BaseAt_td4_proved Not).toC
  | twistedB2 => exact (t5BaseAt_of_not_fund (t := .twistedB2) (fun h => h) Not).toC
  | twistedF4 => exact (t5BaseAt_of_not_fund (t := .twistedF4) (fun h => h) Not).toC
  | twistedG2 => exact (t5BaseAt_of_not_fund (t := .twistedG2) (fun h => h) Not).toC
  | Tits => exact (t5BaseAt_of_not_fund (t := .Tits) (fun h => h) Not).toC

theorem ih8Thm5_of_twinSmall (h : TwinSmallInner p) : Ih8Thm5 p f := by
  refine thm5IH_of_base_shapes_C (fun t k e ht => ?_) t5BaseAtC_nt_all
  rcases ht with hsh | rfl | rfl
  · exact (t5BaseAt_twin_of_shape h hsh).toC
  · exact (t5BaseAt_g2 id).toC
  · exact (t5BaseAt_td4_proved id).toC

end CFSG.ClassicalInvolution.Asc77
