module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeNotDvdCardActorOfIrreducibleCounterexample
public import CFSG.LocalAnalysis.RankThreeUC.Section5.SpecialCenterFromAction
public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryOrdersFromAction

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem special_commutator_center_eq_centralizer_and_exponent_power_two {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) :
    (Section3.CoprimeSpecialGroups.IsSpecialPGroup (Sstar P T B) ∧
      (Subgroup.center ↥(Sstar P T B)).map (Sstar P T B).subtype =
        Sstar P T B ⊓ Subgroup.centralizer (Bstar P B : Set (MulAut ↥P))) ∧
    ∃ k : ℕ, e = 2 ^ k := by
  have hpi := prime_not_dvd_card_actor_of_irreducible_counterexample h
  exact ⟨SpecialCenterFromAction.special_and_center h hpi,
    BinaryOrdersFromAction.exponent_is_two_power h hpi⟩

end Section5
end CFSG.LocalAnalysis.RankThreeUC
