module

public import CFSG.ClassicalInvolution.Asc77.AscSCH14
public import CFSG.ClassicalInvolution.Asc77.AscSCH10
public import CFSG.ClassicalInvolution.Asc77.AscSCH05

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open CFSG.Assembly.LowTwoRank

theorem split3Sp : Split3Sp := by
  intro K _ _ ℓ f hℓ hℓ2 hq hK E _ _ π hπ hC hCp
  have h4 : 4 ≤ Nat.card K := by rw [hK]; omega
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Group.IsPerfect (StatedSp 2 K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 K
      (Or.inl (CFSG.LinearGroups.exists_finset_card_eq_four h4))
  refine split_of_perfect_ker_eq_bot (r := 3) (fun E' _ _ _ π' hπ' hC' hCp' => ?_) E π hπ hC hCp
  by_cases h3 : ℓ = 3
  · subst h3
    exact statedSp_two_perfect_ker_eq_bot_defining hK h4 hπ' hC' hCp'
  · exact statedSp_two_perfect_ker_eq_bot_cross hℓ2 h3 hK π' hπ' hC' hCp'

end CFSG.ClassicalInvolution.Asc77.SCH
