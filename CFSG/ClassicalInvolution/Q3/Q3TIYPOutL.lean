module

public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutGen
public import CFSG.ClassicalInvolution.Q3.Q3WALoc

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.ModelFacts (modelClauseZero)
open CFSG.ClassicalInvolution.Q3 (CompData)
open scoped MatrixGroups


open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem sqDichotomyC_psl4 (hadm : StatedLieAdmissible .PSL 4 3 1) :
    SqDichotomyC (CompData.model .PSL 4) := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have : Group.IsPerfect (modelUniv .PSL 4 3 1 Nat.prime_three).K :=
    Group.isPerfect_def.2 (modelClauseZero .PSL 4 3 1 Nat.prime_three trivial hadm).1.1
  have hπk : (proj 4 (GaloisField 3 1)).ker = Subgroup.center SL(4, GaloisField 3 1) :=
    (ker_proj (n := 4) (K := GaloisField 3 1)).trans (scalars_eq_center 4 (GaloisField 3 1))
  refine sqDichotomyC_of_autVac (CompData.model .PSL 4) (proj 4 (GaloisField 3 1))
    (proj_surjective 4 (GaloisField 3 1)) hπk ?_
  intro R R' hR hR' hne x x' hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ' hφ4
  exact OuterL4.psl4_autVac h2
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR)
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR')
    hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc φ hφ hφ' hφ4

end CFSG.ClassicalInvolution.Q3.Q3TIY
