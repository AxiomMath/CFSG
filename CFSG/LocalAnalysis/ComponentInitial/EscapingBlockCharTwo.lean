module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockQuotient
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem not_isComponent_of_isCharacteristicP_two {H : Type*} [Group H] [Finite H]
    (hchar : CFSG.IsCharacteristicP 2 H) (K : Subgroup H) : ¬ CFSG.IsComponent K := by
  intro hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable (CFSG.pCore 2 H) := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := H)).isNilpotent
    infer_instance
  rcases component_normal_subgroup hK (CFSG.pCore_normal (p := 2) (G := H)) with h1 | h1
  · exact not_le_of_isComponent_of_isSolvable hK hsolv h1
  · exact not_le_of_isComponent_of_isSolvable hK hsolv
      ((commutator_eq_bot_iff_le_centralizer.1 h1).trans hchar)

variable {G : Type*} [Group G] [Finite G]

theorem escaping_block_quotient_non_characteristic_two_centralizer {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ∃ t : L ⧸ center L, orderOf t = 2 ∧
      ¬ CFSG.IsCharacteristicP 2 (centralizer ({t} : Set (L ⧸ center L))) := by
  obtain ⟨-, -, -, -, u, hu, Q, hQ⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  exact ⟨u, hu, fun hchar => not_isComponent_of_isCharacteristicP_two hchar
    (Q.subgroupOf (centralizer ({u} : Set (L ⧸ center L))))
    ((isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ)⟩

end CFSG.LocalAnalysis.ComponentInitial
