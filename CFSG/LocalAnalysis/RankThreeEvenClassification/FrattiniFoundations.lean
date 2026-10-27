module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeNormalizerStep

public section

open scoped commutatorElement

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem pGroup_coatom_normal {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime G)
    (subgroup : Subgroup G) (hmaximal : IsCoatom subgroup) : subgroup.Normal := by
  have : Fact prime.Prime := ⟨hprime⟩
  have : Group.IsNilpotent G := hpgroup.isNilpotent
  exact Subgroup.NormalizerCondition.normal_of_coatom subgroup
    Group.normalizerCondition_of_isNilpotent hmaximal

theorem pGroup_coatom_index {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime G)
    (subgroup : Subgroup G) (hmaximal : IsCoatom subgroup) : subgroup.index = prime := by
  obtain ⟨member, _, hnot, _, hindex⟩ :=
    pGroup_exists_prime_normalizer_step prime hprime hpgroup subgroup hmaximal.1
  have hstrict : subgroup < subgroup ⊔ Subgroup.zpowers member := by
    apply lt_of_le_of_ne le_sup_left
    intro heq
    apply hnot
    rw [heq]
    exact (le_sup_right : Subgroup.zpowers member ≤ subgroup ⊔ Subgroup.zpowers member)
      (Subgroup.mem_zpowers member)
  have htop := hmaximal.2 _ hstrict
  rw [htop, Subgroup.relIndex_top_right] at hindex
  exact hindex

theorem pGroup_coatom_quotient_commutative {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime G)
    (subgroup : Subgroup G) (hmaximal : IsCoatom subgroup) [subgroup.Normal] :
    IsMulCommutative (G ⧸ subgroup) := by
  have : Fact prime.Prime := ⟨hprime⟩
  have hcard : Nat.card (G ⧸ subgroup) = prime := by
    rw [← Subgroup.index_eq_card]
    exact pGroup_coatom_index prime hprime hpgroup subgroup hmaximal
  have : IsCyclic (G ⧸ subgroup) := isCyclic_of_prime_card hcard
  infer_instance

theorem pGroup_pow_mem_frattini {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime G) (member : G) :
    member ^ prime ∈ frattini G := by
  change member ^ prime ∈ ⨅ (subgroup : Subgroup G) (_ : IsCoatom subgroup), subgroup
  apply Subgroup.mem_iInf.mpr
  intro subgroup
  apply Subgroup.mem_iInf.mpr
  intro hmaximal
  have : subgroup.Normal := pGroup_coatom_normal prime hprime hpgroup subgroup hmaximal
  have hcard : Nat.card (G ⧸ subgroup) = prime := by
    rw [← Subgroup.index_eq_card]
    exact pGroup_coatom_index prime hprime hpgroup subgroup hmaximal
  have hmem : member ^ prime ∈ (QuotientGroup.mk' subgroup).ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_pow, ← hcard]
    exact pow_card_eq_one'
  rwa [QuotientGroup.ker_mk'] at hmem

theorem pGroup_commutator_le_frattini {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime G) :
    ⁅(⊤ : Subgroup G), ⊤⁆ ≤ frattini G := by
  change ⁅(⊤ : Subgroup G), ⊤⁆ ≤ ⨅ (subgroup : Subgroup G) (_ : IsCoatom subgroup), subgroup
  apply le_iInf
  intro subgroup
  apply le_iInf
  intro hmaximal
  have : subgroup.Normal := pGroup_coatom_normal prime hprime hpgroup subgroup hmaximal
  have hcommutative := pGroup_coatom_quotient_commutative prime hprime hpgroup subgroup hmaximal
  apply Subgroup.commutator_le.mpr
  intro first _ second _
  have hmem : ⁅first, second⁆ ∈ (QuotientGroup.mk' subgroup).ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_commutatorElement]
    have hcommute : Commute (QuotientGroup.mk' subgroup first) (QuotientGroup.mk' subgroup second) :=
      isMulCommutative_iff.mp hcommutative _ _
    exact hcommute.commutator_eq
  rwa [QuotientGroup.ker_mk'] at hmem

theorem pGroup_frattini_quotient_commutative {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime G) :
    IsMulCommutative (G ⧸ frattini G) := by
  apply isMulCommutative_iff.mpr
  intro first second
  obtain ⟨first, rfl⟩ := QuotientGroup.mk'_surjective (frattini G) first
  obtain ⟨second, rfl⟩ := QuotientGroup.mk'_surjective (frattini G) second
  have hmem : ⁅first, second⁆ ∈ frattini G :=
    pGroup_commutator_le_frattini prime hprime hpgroup
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top first) (Subgroup.mem_top second))
  have heq : QuotientGroup.mk' (frattini G) ⁅first, second⁆ = 1 := by
    apply MonoidHom.mem_ker.mp
    rwa [QuotientGroup.ker_mk']
  rw [map_commutatorElement] at heq
  exact commutatorElement_eq_one_iff_mul_comm.mp heq

theorem pGroup_frattini_quotient_pow_eq_one {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime G)
    (member : G ⧸ frattini G) : member ^ prime = 1 := by
  obtain ⟨member, rfl⟩ := QuotientGroup.mk'_surjective (frattini G) member
  rw [← map_pow]
  apply MonoidHom.mem_ker.mp
  rw [QuotientGroup.ker_mk']
  exact pGroup_pow_mem_frattini prime hprime hpgroup member

theorem frattini_generators_lift {G : Type u} [Group G] [Finite G]
    (generators : Set G)
    (hgenerate : Subgroup.closure ((QuotientGroup.mk' (frattini G)) '' generators) = ⊤) :
    Subgroup.closure generators = ⊤ := by
  have hmapped : (Subgroup.closure generators).map (QuotientGroup.mk' (frattini G)) = ⊤ := by
    rw [MonoidHom.map_closure]
    exact hgenerate
  have hsup := congrArg (fun subgroup : Subgroup (G ⧸ frattini G) =>
    subgroup.comap (QuotientGroup.mk' (frattini G))) hmapped
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hsup
  exact frattini_nongenerating hsup

end CFSG.RankThreeEvenClassification.Helpers
