module

public import CFSG.CGT.T75E.Degenerate
public import CFSG.CGT.T75E.Nondegenerate
public import CFSG.CGT.Timmesfeld75.AschbacherNoPolarDischarge

public section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75


theorem lemma26Simple : Lemma26Simple := by
  intro K _ _ _ T hyp
  by_cases hnd : Lemma26Nondeg T
  · exact lemma26SimpleConcl_of_nondeg hyp hnd
  · exact lemma26SimpleConcl_of_degenerate aschbacherNoPolarInput_of_repo hyp hnd

theorem lemma26 : Lemma26Input :=
  lemma26_of_simple lemma26Simple

end CFSG.CGT.T75E
