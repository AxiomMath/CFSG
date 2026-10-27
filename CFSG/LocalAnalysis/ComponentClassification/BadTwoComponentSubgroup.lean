module

public import CFSG.LocalAnalysis.ComponentClassification.PComponentCentralizers
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

open CFSG CFSG.LocalCores

variable {G : Type*} [Group G] [Finite G]

theorem pComponent_ne_bot {p : ℕ} [Fact p.Prime] {L : Subgroup G} (hL : IsPComponent p L) :
    L ≠ ⊥ := by
  rintro rfl
  apply core_ne_top p ⊥ hL
  have : Subsingleton (⊥ : Subgroup G) := inferInstance
  exact Subsingleton.elim _ _

theorem bad_two_component_characteristic_perfect :
    (badTwoComponentSubgroup G).Characteristic ∧ Group.IsPerfect (badTwoComponentSubgroup G) ∧
    (∀ H : Subgroup G, H.IsSubnormal →
      (badTwoComponentSubgroup H).map H.subtype ≤ badTwoComponentSubgroup G) ∧
    (badTwoComponentSubgroup G = ⊥ ↔ ∀ L : Subgroup G, IsPComponent 2 L → IsQuasisimple L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    refine Subgroup.characteristic_iff_map_le.2 fun ϕ => ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2
      Nat.prime_two ϕ).1 L).1 hL.1, fun hq => hL.2 ?_⟩
    exact isQuasisimple_of_mulEquiv
      (L.equivMapOfInjective ϕ.toMonoidHom ϕ.injective).symm hq
  ·
    refine Subgroup.isPerfect_iff.2 (le_antisymm (Subgroup.commutator_le_self _) ?_)
    refine sSup_le fun L hL => ?_
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 L hL.1
    rw [← Subgroup.commutator_eq_self (H := L)]
    exact Subgroup.commutator_mono (le_sSup hL) (le_sSup hL)
  ·
    intro H hH
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨pComponent_extend_subnormal 2 H hH L hL.1, fun hq => hL.2 ?_⟩
    exact isQuasisimple_of_mulEquiv
      (L.equivMapOfInjective H.subtype H.subtype_injective).symm hq
  · constructor
    · intro hbot L hL
      by_contra hq
      have hle : L ≤ badTwoComponentSubgroup G := le_sSup ⟨hL, hq⟩
      rw [hbot, le_bot_iff] at hle
      exact pComponent_ne_bot hL hle
    · intro hall
      refine le_bot_iff.1 (sSup_le fun L hL => ?_)
      exact absurd (hall L hL.1) hL.2

end CFSG.ComponentClassification.CatalogueBPrimeJoin
