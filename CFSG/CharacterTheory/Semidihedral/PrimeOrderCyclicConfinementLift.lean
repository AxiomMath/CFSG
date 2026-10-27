module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.Semidihedral.PrimeOrderCyclicConfinementLift

universe u

variable {G : Type u} [Group G]

theorem cyclic_subgroup_characteristic [Finite G] [IsCyclic G] (H : Subgroup G) :
    H.Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro φ
  apply IsCyclic.subgroup_eq_iff_card_eq.mpr
  exact Nat.card_congr (H.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv.symm

theorem normalizer_le_of_characteristic_subgroupOf {H K : Subgroup G} (hKH : K ≤ H)
    (hchar : (K.subgroupOf H).Characteristic) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  let φ := H.normalizerMonoidHom ⟨g, hg⟩
  have hfixed := Subgroup.characteristic_iff_map_eq.mp hchar φ
  intro x
  constructor
  · intro hx
    have hxH : x ∈ H := hKH hx
    have hxK : (⟨x, hxH⟩ : H) ∈ K.subgroupOf H := hx
    have himage : φ ⟨x, hxH⟩ ∈ (K.subgroupOf H).map φ.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hxK, rfl⟩
    rw [hfixed] at himage
    change ((φ ⟨x, hxH⟩ : H) : G) ∈ K at himage
    exact himage
  · intro hx
    have hxH : x ∈ H := (hg x).mpr (hKH hx)
    have hxK : φ ⟨x, hxH⟩ ∈ K.subgroupOf H := hx
    rw [← hfixed] at hxK
    obtain ⟨y, hy, heq⟩ := Subgroup.mem_map.mp hxK
    have hyx : y = ⟨x, hxH⟩ := φ.injective heq
    simpa only [hyx, Subgroup.mem_subgroupOf, SetLike.mem_coe] using hy

theorem singleton_centralizer_le_cyclic_normalizer (a : G) :
    Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  rw [Subgroup.zpowers_eq_closure, ← Subgroup.centralizer_closure ({a} : Set G)]
  exact Subgroup.centralizer_le_normalizer _

theorem original_positive_power_prime_order [Finite G] {N : Subgroup G} {a : G}
    (haN : a ∈ N) (ha : a ≠ 1) :
    ∃ k r : ℕ, 0 < k ∧ r.Prime ∧ r ∣ orderOf a ∧
      a ^ k ∈ N ∧ orderOf (a ^ k) = r := by
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd
    (show orderOf a ≠ 1 from fun h => ha (orderOf_eq_one_iff.mp h))
  have hapos := orderOf_pos a
  refine ⟨orderOf a / r, r, ?_, hr, hrdvd, N.pow_mem haN _, ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd hapos hrdvd) hr.pos
  · exact orderOf_pow_orderOf_div hapos.ne' hrdvd

theorem original_power_cyclic_unique_characteristic [Finite G] (a : G) (k r : ℕ)
    (horder : orderOf (a ^ k) = r) :
    Subgroup.zpowers (a ^ k) ≤ Subgroup.zpowers a ∧
      Nat.card ((Subgroup.zpowers (a ^ k)).subgroupOf (Subgroup.zpowers a)) = r ∧
      (∀ K : Subgroup (Subgroup.zpowers a), Nat.card K = r →
        K = (Subgroup.zpowers (a ^ k)).subgroupOf (Subgroup.zpowers a)) ∧
      ((Subgroup.zpowers (a ^ k)).subgroupOf (Subgroup.zpowers a)).Characteristic := by
  have hle : Subgroup.zpowers (a ^ k) ≤ Subgroup.zpowers a :=
    Subgroup.zpowers_le.mpr ((Subgroup.zpowers a).pow_mem (Subgroup.mem_zpowers a) k)
  have hcard : Nat.card ((Subgroup.zpowers (a ^ k)).subgroupOf (Subgroup.zpowers a)) = r :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans
      ((Nat.card_zpowers (a ^ k)).trans horder)
  refine ⟨hle, hcard, ?_, cyclic_subgroup_characteristic _⟩
  intro K hK
  exact IsCyclic.subgroup_eq_iff_card_eq.mpr (hK.trans hcard.symm)

theorem original_prime_order_cyclic_normalizer_confinement_extends_to_every_element [Finite G]
    (N C : Subgroup G)
    (hprime : ∀ a ∈ N, ∀ r : ℕ, r.Prime → orderOf a = r →
      Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ C) :
    ∀ a ∈ N, a ≠ 1 → ∃ (k r : ℕ) (v : G),
      0 < k ∧ v = a ^ k ∧ v ∈ N ∧ r.Prime ∧ orderOf v = r ∧
      Subgroup.zpowers v ≤ Subgroup.zpowers a ∧
      Nat.card ((Subgroup.zpowers v).subgroupOf (Subgroup.zpowers a)) = r ∧
      (∀ K : Subgroup (Subgroup.zpowers a), Nat.card K = r →
        K = (Subgroup.zpowers v).subgroupOf (Subgroup.zpowers a)) ∧
      ((Subgroup.zpowers v).subgroupOf (Subgroup.zpowers a)).Characteristic ∧
      Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers v : Set G) ∧
      Subgroup.normalizer (Subgroup.zpowers v : Set G) ≤ C ∧
      Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ C ∧
      Subgroup.centralizer ({a} : Set G) ≤ C := by
  intro a haN ha
  obtain ⟨k, r, hk, hr, _, hvN, hvorder⟩ := original_positive_power_prime_order haN ha
  obtain ⟨hle, hcard, hunique, hchar⟩ := original_power_cyclic_unique_characteristic a k r hvorder
  have hnormal := normalizer_le_of_characteristic_subgroupOf hle hchar
  have hvconf := hprime (a ^ k) hvN r hr hvorder
  have haconf := hnormal.trans hvconf
  exact ⟨k, r, a ^ k, hk, rfl, hvN, hr, hvorder, hle, hcard, hunique, hchar,
    hnormal, hvconf, haconf, (singleton_centralizer_le_cyclic_normalizer a).trans haconf⟩

theorem original_normalizer_le_of_trivial_intersections (N C : Subgroup G) (hN : N ≠ ⊥)
    (hTI : ∀ g : G, g ∉ C → N ⊓ N.map (MulAut.conj g) = ⊥) :
    Subgroup.normalizer (N : Set G) ≤ C := by
  intro g hg
  by_contra hgC
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hintersection := hTI g hgC
  rw [hmap, inf_idem] at hintersection
  exact hN hintersection

theorem original_trivial_intersections_give_exact_normalizer_of_nontrivial_odd_core
    (N C : Subgroup G) (hN : N ≠ ⊥)
    (hTI : ∀ g : G, g ∉ C → N ⊓ N.map (MulAut.conj g) = ⊥)
    (hCN : C ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup.normalizer (N : Set G) ≤ C ∧
      C ≤ Subgroup.normalizer (N : Set G) ∧ Subgroup.normalizer (N : Set G) = C := by
  have hNC := original_normalizer_le_of_trivial_intersections N C hN hTI
  exact ⟨hNC, hCN, le_antisymm hNC hCN⟩

end CFSG.Semidihedral.PrimeOrderCyclicConfinementLift
