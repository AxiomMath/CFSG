module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoA
public import CFSG.Milestones.CL_LIT_Monster_existence_Griess_Conway
public import CFSG.YGroups.Y443.Tri.AssemblyLit

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Monster.Generated

theorem oPrimeCoreTrivialAt_gmat_of_uninverted
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : UninvertedOPrimeTrivial p Gmat) :
    OPrimeCoreTrivialAt p Gmat :=
  oPrimeCoreTrivialAt_of_uninverted_mulEquiv CFSG.Milestones.cl_lit_monster_existence_griess_conway
    (CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth).symm hp hp2 h

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
