module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.MRowExistence
public import CFSG.YGroups.Y443.Tri.AssemblyLit
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.CenterAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimEquiv

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Blueprint.NativeSporadic CFSG.Monster.Existence CFSG.Monster.Generated
  CFSG.RankThree.PartOne.SPOR CFSG.YGroups.Y443

theorem m_data_of_simple {Y : Type} [Group Y] [IsSimpleGroup Y] (e : Y ≃* Carrier .M) :
    AllInner Y ∧ CenterInvolutions Y ∧ InvolutionsCommute Y := by
  obtain ⟨ε⟩ := mulEquiv_Gmat_of_simple e
  obtain ⟨⟨hfin, -, -, -⟩, ha₀, -, -, hcls, hA, hB⟩ :=
    monster_existence_clauses_one_two_of_stroth
      CFSG.Milestones.cl_lit_stroth_leon_sims_baby_monster_recognition_models
  have hGA := Gmat_eq_AutO_of_stroth
  let φ : Y ≃* MGriess := ε.trans (griessEquivGmat hGA).symm
  have := hfin
  exact ⟨AllInner.of_mulEquiv ε.symm allInner_Gmat,
    (centerInvolutions_of_clauses hcls hA hB).of_mulEquiv φ.symm,
    (involutionsCommute_of_clauses ha₀ hcls).of_mulEquiv φ.symm⟩

end CFSG.EvenSporadicStandard.Solomon78
