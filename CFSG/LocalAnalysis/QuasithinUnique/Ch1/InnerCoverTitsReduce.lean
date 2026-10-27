module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverEven
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def TitsNoDoubleCover : Prop :=
  ∀ (X : Type) [Group X] [Finite X], ReeTitsModel X .Tits 2 1 →
    ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* X), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.card π.ker = 2 → False

theorem titsTwoCoverTrivial_of_noDoubleCover (h : TitsNoDoubleCover) : TitsTwoCoverTrivial := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro X _ _ hX E _ _ _ η hη hC h2
  exact ker_eq_bot_of_no_prime_order_cover (r := 2)
    (fun E' _ _ _ π hπ hC' hcard => h X hX E' π hπ hC' hcard) η hη hC h2

end CFSG.QuasithinUnique.Ch1
