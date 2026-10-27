module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKleinThree
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import CFSG.Milestones.CL_LIT_Monster_existence_Griess_Conway
public import CFSG.YGroups.Y443.Tri.AssemblyLit

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Monster.Generated

theorem uninvertedOPrimeTrivial_gmat_of_twoATwoCommuting
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hB : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.B)
    (hCo : SporadicOPrimeHolds .Co1 p) (h : TwoATwoCommuting p Gmat) :
    UninvertedOPrimeTrivial p Gmat := by
  have hCo' : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.Co1 := by
    obtain ⟨hf, -, hs⟩ := CFSG.Sporadic.Co1.fam_co1_simplicity
    exact @hCo CFSG.Blueprint.NativeSporadic.Co1 Units.instGroup hf hs ⟨MulEquiv.refl _⟩
  let φ := CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  exact (uninvertedOPrimeTrivial_of_twoATwoCommuting
    CFSG.Milestones.cl_lit_monster_existence_griess_conway hp hp2 hB hCo'
    (h.of_mulEquiv φ)).of_mulEquiv φ.symm

theorem uninvertedOPrimeTrivial_gmat_of_twoAPureKlein
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hB : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.B) (h : TwoAPureKlein p Gmat) :
    UninvertedOPrimeTrivial p Gmat := by
  let φ := CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  exact (uninvertedOPrimeTrivial_of_twoAPureKlein
    CFSG.Milestones.cl_lit_monster_existence_griess_conway hp hp2 hB
    (h.of_mulEquiv φ)).of_mulEquiv φ.symm

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
