module

public import CFSG.ClassicalInvolution.Balance.PassTwoLie
public import CFSG.ClassicalInvolution.ModelFacts.Models

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

theorem fundamentalWholeA1 : FundamentalWholeA1 := by
  intro t n p f hp _ hadm ⟨ht, hn⟩
  subst ht
  subst hn
  intro R hR
  exact CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups_eq_top_PSL_two p f hp hadm R hR

end CFSG.ClassicalInvolution.Balance
