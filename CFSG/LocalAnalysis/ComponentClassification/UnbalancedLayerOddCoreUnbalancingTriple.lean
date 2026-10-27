module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreFreeComponentWitness
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreActiveTwoComponent

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup

theorem exists_active_two_component {K : Type*} [Group K] [Finite K] {x : K}
    (hx : orderOf x = 2) {D : Subgroup K} (hDC : D ≤ centralizer ({x} : Set K))
    (hDn : (D.subgroupOf (centralizer ({x} : Set K))).Normal) (hDodd : Odd (Nat.card D))
    (hDR : ¬ D ≤ pPrimeCore 2 K) :
    ∃ J : Subgroup K, IsPComponent 2 J ∧ x ∈ normalizer (J : Set K) ∧
      D ≤ normalizer (J : Set K) ∧ ⁅J, D⁆ = J ∧ ⁅J, zpowers x⁆ = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hRodd : Odd (Nat.card (pPrimeCore 2 K)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨hDbC, hDbn⟩ := map_normal_centralizer hRodd hxx hDC hDn
  have hxb := orderOf_mk_eq_two hRodd hx
  have hDbodd : Odd (Nat.card (D.map (QuotientGroup.mk' (pPrimeCore 2 K)))) :=
    hDodd.of_dvd_nat (card_map_dvd D _)
  have hDb1 : D.map (QuotientGroup.mk' (pPrimeCore 2 K)) ≠ ⊥ := by
    intro h
    apply hDR
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  obtain ⟨Kc, hKc, hDbK, hxK, hKD, hKx⟩ := odd_core_free_fixed_centralizer_component_witness
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hxb hDb1 hDbC hDbn hDbodd
  obtain ⟨hJ, hJK⟩ := CatalogueBPrimeJoin.canonicalPrimeLift_isPComponent 2 Kc hKc
  obtain ⟨-, -, hJsub, -, -⟩ := id hJ
  have hxJ : x ∈ normalizer (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kc : Set K) :=
    mem_normalizer_of_map hJ (by rw [hJK]; exact hxK)
  have hDJ : D ≤ normalizer (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kc : Set K) :=
    fun d hd => mem_normalizer_of_map hJ (by rw [hJK]; exact hDbK (mem_map_of_mem _ hd))
  have hxz := zpowers_le.mpr hxJ
  refine ⟨_, hJ, hxJ, hDJ, ?_, ?_⟩
  · exact eq_of_le_of_map_eq hJ (commutator_le_left_of_le_normalizer hDJ)
      (commutator_isSubnormal hJsub hDJ) (by rw [map_commutator, hJK, hKD])
  · exact eq_of_le_of_map_eq hJ (commutator_le_left_of_le_normalizer hxz)
      (commutator_isSubnormal hJsub hxz) (by rw [map_commutator, hJK, MonoidHom.map_zpowers, hKx])

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_map_pPrimeCore {C : Subgroup G} {c y : G} (hc : c ∈ C)
    (hy : y ∈ (pPrimeCore 2 C).map C.subtype) : c * y * c⁻¹ ∈ (pPrimeCore 2 C).map C.subtype := by
  obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
  exact ⟨⟨c, hc⟩ * y' * ⟨c, hc⟩⁻¹, pPrimeCore_normal.conj_mem y' hy' ⟨c, hc⟩, rfl⟩

theorem commuting_involution_odd_core_unbalancing_triple {a x : G} (ha : orderOf a = 2)
    (hx : orderOf x = 2) (hax : a * x = x * a) :
    (pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype ⊓
        centralizer ({a} : Set G) ≤
      (pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype ∨
    ∃ J : Subgroup G, GSUnbalancingTriple a x J := by
  by_cases hD : (pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype ⊓
      centralizer ({a} : Set G) ≤
      (pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype
  · exact Or.inl hD
  right
  have hxa : x ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hax.symm
  have hx' : orderOf (⟨x, hxa⟩ : centralizer ({a} : Set G)) = 2 := by
    rw [Subgroup.orderOf_mk, hx]
  have hDle : (pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype ⊓
      centralizer ({a} : Set G) ≤ centralizer ({a} : Set G) := inf_le_right
  have hmemD : ∀ d : centralizer ({a} : Set G),
      d ∈ ((pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype ⊓
        centralizer ({a} : Set G)).subgroupOf (centralizer ({a} : Set G)) ↔
      (d : G) ∈ (pPrimeCore 2 (centralizer ({x} : Set G))).map
        (centralizer ({x} : Set G)).subtype := by
    intro d
    rw [mem_subgroupOf, mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, d.2⟩⟩
  have hDC : ((pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype ⊓
      centralizer ({a} : Set G)).subgroupOf (centralizer ({a} : Set G)) ≤
      centralizer ({(⟨x, hxa⟩ : centralizer ({a} : Set G))} : Set _) := by
    intro d hd
    obtain ⟨y, -, hy⟩ := mem_map.mp ((hmemD d).mp hd)
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    have h := mem_centralizer_singleton_iff.mp y.2
    change (d : G) * x = x * d
    rw [← hy]
    exact h
  have hDn : ((((pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype ⊓ centralizer ({a} : Set G)).subgroupOf
        (centralizer ({a} : Set G))).subgroupOf
      (centralizer ({(⟨x, hxa⟩ : centralizer ({a} : Set G))} : Set _))).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hDC]
    have key : ∀ c ∈ centralizer ({(⟨x, hxa⟩ : centralizer ({a} : Set G))} : Set _),
        ∀ d ∈ ((pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype ⊓
          centralizer ({a} : Set G)).subgroupOf (centralizer ({a} : Set G)),
        c * d * c⁻¹ ∈ ((pPrimeCore 2 (centralizer ({x} : Set G))).map
          (centralizer ({x} : Set G)).subtype ⊓ centralizer ({a} : Set G)).subgroupOf
            (centralizer ({a} : Set G)) := by
      intro c hc d hd
      rw [hmemD] at hd ⊢
      have hcx : (c : G) ∈ centralizer ({x} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
      exact conj_mem_map_pPrimeCore hcx hd
    intro c hc
    rw [mem_normalizer_iff]
    intro d
    refine ⟨key c hc d, fun hd => ?_⟩
    have h := key c⁻¹ (inv_mem hc) _ hd
    rwa [show c⁻¹ * (c * d * c⁻¹) * c⁻¹⁻¹ = d by group] at h
  have hDodd : Odd (Nat.card (((pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype ⊓ centralizer ({a} : Set G)).subgroupOf
        (centralizer ({a} : Set G)))) := by
    have hO : Odd (Nat.card ((pPrimeCore 2 (centralizer ({x} : Set G))).map
        (centralizer ({x} : Set G)).subtype)) := by
      rw [card_map_of_injective (centralizer _).subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    refine hO.of_dvd_nat ?_
    rw [← card_map_of_injective (centralizer ({a} : Set G)).subtype_injective,
      map_subgroupOf_eq_of_le hDle]
    exact card_dvd_of_le inf_le_left
  have hDR : ¬ ((pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype ⊓ centralizer ({a} : Set G)).subgroupOf
        (centralizer ({a} : Set G)) ≤ pPrimeCore 2 (centralizer ({a} : Set G)) := by
    intro h
    apply hD
    have h' := map_mono (f := (centralizer ({a} : Set G)).subtype) h
    rwa [map_subgroupOf_eq_of_le hDle] at h'
  obtain ⟨J', hJ', -, -, hJD, hJx⟩ := exists_active_two_component hx' hDC hDn hDodd hDR
  refine ⟨J'.map (centralizer ({a} : Set G)).subtype, gsUnbalancingTriple_iff.mpr
    ⟨ha, hx, hax, map_subtype_le J', ?_, ?_, ?_⟩⟩
  · have hsub : (J'.map (centralizer ({a} : Set G)).subtype).subgroupOf
        (centralizer ({a} : Set G)) = J' :=
      comap_map_eq_self_of_injective (centralizer ({a} : Set G)).subtype_injective J'
    rwa [hsub]
  · have hz : zpowers x = (zpowers (⟨x, hxa⟩ : centralizer ({a} : Set G))).map
        (centralizer ({a} : Set G)).subtype := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hz, ← map_commutator, hJx]
  · conv_lhs => rw [← map_subgroupOf_eq_of_le hDle]
    rw [← map_commutator, hJD]

end CFSG.ComponentClassification.UnbalancedLayer
