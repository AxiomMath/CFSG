module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockQuotient
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

variable {G : Type*} [Group G] [Finite G]

theorem escaping_block_exists_pComponent_two {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) {X : Type*} [Group X]
    (φ : L ⧸ center L →* X) (hφ : Function.Injective φ) {H : Subgroup X} (hH : φ.range = H) :
    ∃ x ∈ H, x ^ 2 = 1 ∧ ∃ B : Subgroup X, B ≤ H ⊓ centralizer {x} ∧
      CFSG.IsPComponent 2 (B.subgroupOf (H ⊓ centralizer {x})) ∧ Nat.card B ∣ Nat.card J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K, hK, hKJ⟩ := hΔ.exists_ne J
  have hKL : K ≤ L := (le_blockGroup hK).trans hML
  have hJL : J ≤ L := (le_blockGroup mem_block_self).trans hML
  have hKeven : Even (Nat.card K) := by
    obtain ⟨g, rfl⟩ := hK.1
    rwa [card_conjSub]
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (even_iff_two_dvd.1 hKeven)
  have ht : orderOf (⟨k, hKL k.2⟩ : L) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hk]
  obtain ⟨hu, hB⟩ := hloc J mem_block_self K hK (Ne.symm hKJ) ⟨k, hKL k.2⟩ k.2 ht
  set u := QuotientGroup.mk' (center L) (⟨k, hKL k.2⟩ : L) with hudef
  have hCmap : (centralizer ({u} : Set (L ⧸ center L))).map φ = H ⊓ centralizer {φ u} := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨hH ▸ ⟨c, rfl⟩, mem_centralizer_iff.2 fun w hw => ?_⟩
      rw [Set.mem_singleton_iff.1 hw, ← map_mul, ← map_mul, mem_centralizer_iff.1 hc u rfl]
    · rintro ⟨hyH, hyC⟩
      rw [← hH] at hyH
      obtain ⟨c, rfl⟩ := hyH
      refine ⟨c, mem_centralizer_iff.2 fun w hw => ?_, rfl⟩
      rw [Set.mem_singleton_iff.1 hw]
      exact hφ (by rw [map_mul, map_mul]; exact mem_centralizer_iff.1 hyC (φ u) rfl)
  have hB' : CFSG.Assembly.IsComponentOf ((centerQuotientImage L J).map φ)
      (H ⊓ centralizer {φ u}) := by
    rw [← hCmap]
    exact (isComponentOf_map_iff hφ).2 hB
  have hHfin : Finite H := by
    rw [← hH]
    exact Finite.of_surjective _ φ.rangeRestrict_surjective
  have : Finite ↥(H ⊓ centralizer {φ u}) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : H ⊓ _ ≤ H))
  have hsolv : Group.IsSolvable (CFSG.pPrimeCore 2 ↥(H ⊓ centralizer {φ u})) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card)
  refine ⟨φ u, hH ▸ ⟨u, rfl⟩, ?_, (centerQuotientImage L J).map φ, hB'.1, ?_, ?_⟩
  · rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]
  · exact (solvable_prime_core_ordinary_components 2 Nat.prime_two hsolv).1 _
      ((isComponentOf_iff_isComponent_subgroupOf hB'.1).1 hB')
  · rw [Subgroup.card_map_of_injective hφ, centerQuotientImage,
      ← Nat.card_congr (subgroupOfEquivOfLe hJL).toEquiv]
    exact (J.subgroupOf L).card_map_dvd (QuotientGroup.mk' (center L))

end CFSG.LocalAnalysis.ComponentInitial
