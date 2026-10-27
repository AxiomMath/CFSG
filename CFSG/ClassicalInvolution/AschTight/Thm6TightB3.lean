module

public import CFSG.ClassicalInvolution.AschTight.Thm6Tight3
public import CFSG.Goldschmidt75.CorollaryB3

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

theorem goldschmidtB3Tmp_holds : GoldschmidtB3Tmp :=
  fun G _ _ S A => CFSG.Goldschmidt75.goldschmidtB3 G S A

variable {p f : ℕ} [Fact p.Prime] in
theorem false_of_allTypeTwo_of_tightD {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {K : Subgroup G} {z : G} (ht : S19R.TightStd p f K z) (hA : AllTypeTwo K z) : False :=
  false_of_allTypeTwo goldschmidtB3Tmp_holds ht hA

variable (p f : ℕ) [Fact p.Prime]

theorem tightControlledD_of_sec19 (hE2 : C19_E2Tmp p f) (h16 : C19_16STmp p f)
    (hIH : IHAllD p f) : TightControlledD p f :=
  tightControlledD_of_targets3 p f goldschmidtB3Tmp_holds hE2 h16 hIH

end CFSG.ClassicalInvolution.Disconnected.AschTight
