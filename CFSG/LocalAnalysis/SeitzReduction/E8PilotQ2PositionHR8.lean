module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2Position
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotHR8Instances

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {K : Type} [Field K]

theorem neighbour_overgroup_E8_nonsplit_two (hcat : E7CatalogueClauses) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hset : StandardSetting G L) (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup (adjointGroup .E8 K)} (hAJ : A ≤ posJE8 K) (hA : Nat.card A = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupE7 (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 1 := by
  have hA3 : Nat.card A = 3 := by rw [hA, hK]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact neighbour_overgroup_E8_nonsplit_of_not_normal hcat hset (by rw [pow_one]; exact hK) e ht
    hKt hAJ hA (isCyclic_of_prime_card hA3) hX htX hDe
    (not_normal_neighbour_E8_nonsplit_two hset hK e ht hKt hAJ hA hX hDe)

end CFSG.SeitzReduction.E8Pilot
