module

public import CFSG.GF2Type.Aschbacher1976HigherCenter.Setup

public section

namespace CFSG.GF2Type.Aschbacher1976HigherCenter

open Subgroup CFSG CFSG.Open

theorem center_facts
    {G : Type} [Group G] [Finite G] {M B Q : Subgroup G} {z : G} {D : Subgroup Q} {k u : ℕ}
    (h : Setup M B Q z D k u) :
    IsCyclic (critCenter D) ∧ IsPGroup 2 (critCenter D) ∧ Nat.card (critCenter D) = 2 ^ k ∧
      (∀ g : G, conjugate (critCenter D) g = critCenter D ∨
        critCenter D ⊓ conjugate (critCenter D) g = ⊥) ∧
      normalizer (critCenter D : Set G) = M ∧ z ∈ critCenter D ∧
      (∀ y ∈ critCenter D, orderOf y = 2 → y = z) ∧ critCenter D ≤ Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcc := (CFSG.LocalAnalysis.GorensteinLyons.gf2_critical_center_and_exponent_four_reduction
    h.charTwoType (by have := h.oddRank; omega) h.maxLocal h.symplectic h.bmax h.bmax_le
    h.core_eq h.central h.involution (r := GLATwoLocalRank 3 G) rfl).2 D h.critical _ rfl _ rfl
  obtain ⟨-, -, hYcyc, -, hzY, huniq, -, hnorm, -, -, -, -, -, hconj, -⟩ := hcc
  have hQ2 : IsPGroup 2 Q := by
    rw [h.core_eq]
    exact IsPGroup.map CFSG.pCore_isPGroup _
  have hYQ : critCenter D ≤ Q := map_subtype_le _
  let e : ((center D).map D.subtype) ≃* critCenter D :=
    Subgroup.equivMapOfInjective _ Q.subtype Q.subtype_injective
  refine ⟨isCyclic_of_surjective e.toMonoidHom e.surjective, hQ2.to_le hYQ, ?_,
    fun g => (hconj g).1, hnorm, hzY, huniq, hYQ⟩
  rw [← h.center_card]
  exact card_map_of_injective Q.subtype_injective

end CFSG.GF2Type.Aschbacher1976HigherCenter
