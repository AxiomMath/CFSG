module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.HyperplaneOrbitStructure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.ActorInversion

open CFSG.LocalAnalysis.RankThreeUC.Section5

theorem inverted {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    ∃ x : G, ∀ b ∈ B, x * b * x⁻¹ = b⁻¹ := by
  by_contra hn
  exact hc.not_concl (Or.inr (Or.inr ⟨(cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc).2.1.1, (three_lt_pRank_and_prime_not_dvd_card_actor hc).1, hn⟩))

end CFSG.LocalAnalysis.RankThreeUC.Section5.ActorInversion
