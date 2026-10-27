module

public import CFSG.CGT.PushingUpLit.BHS.Defs
public import CFSG.CGT.PushingUpLit.BHS.Replacement
public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6

instance commGroupCoreMod (n : ℕ) : CommGroup ↥(coreMod n) := Subgroup.toCommGroup (coreMod n)

theorem coreMod_sq (n : ℕ) (v : ↥(coreMod n)) : v ^ 2 = 1 := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  simp [pow_two]
  exact CharTwo.add_self_eq_zero _

end CFSG.CGT.PushingUpLit.BHS
