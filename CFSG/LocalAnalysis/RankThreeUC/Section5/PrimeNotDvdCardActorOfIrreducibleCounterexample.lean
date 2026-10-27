module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.IndependentPPartExclusion

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem prime_not_dvd_card_actor_of_irreducible_counterexample {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) :
    p ∉ piOf B := by
  exact fun hp => CFSG.LocalAnalysis.RankThreeUC.Section5.IndependentPPartExclusion.p_part_impossible h hp

end Section5
end CFSG.LocalAnalysis.RankThreeUC
