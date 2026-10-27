module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdDefs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

theorem isSolvable_of_cyclic_sylow {G : Type} [Group G] [Finite G]
    (hS : ∃ S : Sylow 2 G, IsCyclic (S : Subgroup G)) : Group.IsSolvable G := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSc⟩ := hS
  obtain ⟨-, -, -, ⟨hNn, hNodd, hidx, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hSc
  have hNs : Group.IsSolvable ↥(pPrimeCore 2 G) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  have hq : IsPGroup 2 (G ⧸ pPrimeCore 2 G) := by
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    refine IsPGroup.of_card (n := k) ?_
    rw [← Subgroup.index_eq_card, hidx, hk]
  have hqs : Group.IsSolvable (G ⧸ pPrimeCore 2 G) := by
    have := hq.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (pPrimeCore 2 G).subtype
    (QuotientGroup.mk' (pPrimeCore 2 G)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {n : ℕ} {z : G}

theorem StdSetup.isCyclic_sylow_of_le (h : StdSetup G L n z) {H : Subgroup G}
    (hH : H ≤ centralizer (L : Set G)) (S : Sylow 2 ↥H) : IsCyclic ↥(S : Subgroup ↥H) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : (S : Subgroup ↥H).map H.subtype ≤ centralizer (L : Set G) :=
    (Subgroup.map_subtype_le _).trans hH
  have hc := h.cyclic _ hle (S.isPGroup'.map _)
  have e : ↥(S : Subgroup ↥H) ≃* ↥((S : Subgroup ↥H).map H.subtype) :=
    Subgroup.equivMapOfInjective _ _ H.subtype_injective
  have := hc
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem StdSetup.isCyclic_sylow (h : StdSetup G L n z) (S : Sylow 2 ↥(centralizer (L : Set G))) :
    IsCyclic ↥(S : Subgroup ↥(centralizer (L : Set G))) :=
  h.isCyclic_sylow_of_le le_rfl S

theorem StdSetup.isSolvable_centralizer (h : StdSetup G L n z) :
    Group.IsSolvable ↥(centralizer (L : Set G)) := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(centralizer (L : Set G))) := inferInstance
  exact isSolvable_of_cyclic_sylow ⟨S, h.isCyclic_sylow S⟩

end CFSG.OddStandard.Solomon75
