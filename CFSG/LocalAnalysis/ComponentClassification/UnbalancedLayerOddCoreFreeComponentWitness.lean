module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerActiveCore
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalThompson

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup

variable {H : Type*} [Group H]

theorem center_map_le_fittingSubgroup {N : Subgroup H} (hN : N.Normal) :
    (center N).map N.subtype ≤ fittingSubgroup H := by
  have hZn : ((center N).map N.subtype).Normal := by
    constructor
    intro z hz h
    obtain ⟨hzN, hzc⟩ := (mem_map_center_iff _).mp hz
    refine (mem_map_center_iff _).mpr ⟨hN.conj_mem z hzN h, ?_⟩
    rw [mem_centralizer_iff]
    intro e he
    have he' : h⁻¹ * e * h ∈ N := by simpa using hN.conj_mem e he h⁻¹
    have hez := mem_centralizer_iff.mp hzc _ he'
    calc e * (h * z * h⁻¹) = h * ((h⁻¹ * e * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * e * h)) * h⁻¹ := by rw [hez]
      _ = h * z * h⁻¹ * e := by group
  have hZc : IsMulCommutative ((center N).map N.subtype) := by
    refine isMulCommutative_iff.mpr fun x y => Subtype.ext ?_
    obtain ⟨-, hxc⟩ := (mem_map_center_iff _).mp x.2
    obtain ⟨hyN, -⟩ := (mem_map_center_iff _).mp y.2
    exact (mem_centralizer_iff.mp hxc _ hyN).symm
  exact fitting_characteristic.2.2 _ hZn inferInstance

variable [Finite H]

theorem odd_core_free_fixed_centralizer_component_witness (hO : pPrimeCore 2 H = ⊥) {t : H}
    (ht : orderOf t = 2) {D : Subgroup H} (hD1 : D ≠ ⊥) (hDC : D ≤ centralizer ({t} : Set H))
    (hDn : (D.subgroupOf (centralizer ({t} : Set H))).Normal) (hDodd : Odd (Nat.card D)) :
    ∃ K : Subgroup H, IsComponent K ∧ D ≤ normalizer (K : Set H) ∧
      t ∈ normalizer (K : Set H) ∧ ⁅K, D⁆ = K ∧ ⁅K, zpowers t⁆ = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hDP : ⁅D, pCore 2 H⁆ = ⊥ := by
    have hT : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have hDC' := hDC
    have hDn' := hDn
    rw [← centralizer_zpowers_eq] at hDC' hDn'
    exact SmallLocal.normal_coprime_centralizer_centralizes_prime_core Nat.prime_two hT hDC'
      hDn' (Nat.coprime_two_left.mpr hDodd)
  have hFQ := fittingSubgroup_le_pCore_two hO
  have hDZ : ⁅D, (center (layer H)).map (layer H).subtype⁆ = ⊥ :=
    le_bot_iff.mp (hDP ▸ commutator_mono le_rfl (center_layer_le_fittingSubgroup.trans hFQ))
  have heven : ∀ K : Subgroup H, IsComponent K → Even (Nat.card (K ⧸ center K)) := by
    intro K hK
    have : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
    exact (SimpleEvenOrder.nonabelian_simple_even hK.1.2.2).1
  have hnorm := odd_fixed_centralizer_normalizes_even_layer_components ht hDC hDn hDodd hDZ heven
  obtain ⟨K, hK, hKD⟩ : ∃ K : Subgroup H, IsComponent K ∧ ⁅K, D⁆ ≠ ⊥ := by
    by_contra hall
    push Not at hall
    apply hD1
    have hDE : D ≤ centralizer (layer H : Set H) := by
      rw [le_centralizer_iff]
      exact sSup_le fun K hK => commutator_eq_bot_iff_le_centralizer.mp (hall K hK)
    have hDF : D ≤ centralizer (fittingSubgroup H : Set H) :=
      commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp (hDP ▸ commutator_mono le_rfl hFQ))
    have hDFs : D ≤ centralizer (generalizedFitting H : Set H) := by
      rw [le_centralizer_iff, generalizedFitting]
      exact sup_le (le_centralizer_iff.mp hDF) (le_centralizer_iff.mp hDE)
    have hDin : D ≤ generalizedFitting H := hDFs.trans (centralizer_generalizedFitting_le H)
    have hDZF : D ≤ (center (generalizedFitting H)).map (generalizedFitting H).subtype :=
      fun d hd => (mem_map_center_iff _).mpr ⟨hDin hd, hDFs hd⟩
    have hDQ : D ≤ pCore 2 H := hDZF.trans
      ((center_map_le_fittingSubgroup generalized_fitting_characteristic.2).trans hFQ)
    obtain ⟨k, hk⟩ := (pCore_isPGroup.to_le hDQ : IsPGroup 2 D).exists_card_eq
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact card_eq_one.mp hk
    · exfalso
      rw [hk] at hDodd
      exact (Nat.not_even_iff_odd.mpr hDodd) (Nat.even_pow.mpr ⟨even_two, k.succ_ne_zero⟩)
  obtain ⟨htK, hKD', hKt⟩ := active_component htt hDC hDn hDodd hK (heven K hK) (hnorm K hK)
    (hnorm _ (isComponent_conjugate hK t)) hKD
  exact ⟨K, hK, hnorm K hK, htK, hKD', hKt⟩

end CFSG.ComponentClassification.UnbalancedLayer
