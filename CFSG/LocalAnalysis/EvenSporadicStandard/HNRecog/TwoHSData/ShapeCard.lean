module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeIISpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.SylowCover

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

private lemma natCard_elem2 (n : ℕ) : Nat.card (Elem2 n) = 2 ^ n := by
  rw [Elem2, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem IsShapeTwoTwoTimesA8.card_eq {X : Type*} [Group X] (h : IsShapeTwoTwoTimesA8 X) :
    Nat.card X = 80640 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, natCard_elem2, nat_card_alternatingGroup,
    Nat.card_fin]
  norm_num [Nat.factorial]

theorem IsShapeCentralizerFiveB.card_eq {X : Type*} [Group X] (h : IsShapeCentralizerFiveB X) :
    Nat.card X = 100 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact card_target_B5

theorem IsShapeCentralizerFiveC.card_eq {X : Type*} [Group X] (h : IsShapeCentralizerFiveC X) :
    Nat.card X = 1200 := by
  obtain ⟨Y, _, ⟨Z, hZ, hZc, ⟨e⟩, -⟩, ⟨f⟩⟩ := h
  have hS5 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hY : Nat.card Y = 240 := by
    rw [← Subgroup.card_mul_index Z, hZc, Subgroup.index_eq_card, Nat.card_congr e.toEquiv, hS5]
  rw [Nat.card_congr f.toEquiv, Nat.card_prod, hY, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

theorem exists_subgroup_mulEquiv_of_mulEquiv {X Y T : Type*} [Group X] [Group Y] [Group T]
    (e : X ≃* Y) {D : Subgroup X} (hD : Nonempty (↥D ≃* T)) :
    ∃ S : Subgroup Y, Nonempty (↥S ≃* T) := by
  obtain ⟨f⟩ := hD
  exact ⟨D.map e.toMonoidHom,
    ⟨(Subgroup.equivMapOfInjective D e.toMonoidHom e.injective).symm.trans f⟩⟩

theorem exists_subgroup_mulEquiv_of_le {M Y T : Type*} [Group M] [Group Y] [Group T]
    {K D : Subgroup M} (hDK : D ≤ K) (e : ↥K ≃* Y) (hD : Nonempty (↥D ≃* T)) :
    ∃ S : Subgroup Y, Nonempty (↥S ≃* T) := by
  obtain ⟨f⟩ := hD
  exact exists_subgroup_mulEquiv_of_mulEquiv e (D := D.subgroupOf K)
    ⟨(Subgroup.subgroupOfEquivOfLe hDK).trans f⟩

theorem isConj_of_mem_centralizer_of_orderOf_five {G : Type*} [Group G] [Finite G]
    {b rp s ρ : G} (hrp : orderOf rp = 5) (hrpb : rp * b = b * rp)
    (hcard : (Nat.card ↥(centralizer ({b} : Set G))).factorization 5 = 1)
    (hs : ∀ k : ℕ, 0 < k → k < 5 → IsConj s (rp ^ k)) (hρ : orderOf ρ = 5)
    (hρb : ρ * b = b * ρ) : IsConj s ρ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hrpC : rp ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.2 hrpb
  have hρC : ρ ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.2 hρb
  have hle : zpowers rp ≤ centralizer ({b} : Set G) := zpowers_le.2 hrpC
  have hS : Nat.card ↥(zpowers rp) =
      5 ^ (Nat.card ↥(centralizer ({b} : Set G))).factorization 5 := by
    rw [Nat.card_zpowers, hrp, hcard, pow_one]
  obtain ⟨x, -, hx⟩ := TwoHSData.exists_conj_mem_of_orderOf_eq_prime hle hS hρC hρ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hmod : rp ^ (k % (orderOf rp : ℤ)) = x⁻¹ * ρ * x := by rw [zpow_mod_orderOf, hk]
  rw [hrp] at hmod
  have hk5 : 0 ≤ k % ((5 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have hk5' : k % ((5 : ℕ) : ℤ) < 5 := Int.emod_lt_of_pos _ (by norm_num)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, k % ((5 : ℕ) : ℤ) = j := ⟨(k % ((5 : ℕ) : ℤ)).toNat, by omega⟩
  rw [hj, zpow_natCast] at hmod
  have hj5 : j < 5 := by omega
  have hconj : IsConj ρ (x⁻¹ * ρ * x) := isConj_iff.2 ⟨x⁻¹, by simp⟩
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · exfalso
    rw [pow_zero] at hmod
    have h1 : ρ = 1 := by
      have : ρ = x * (x⁻¹ * ρ * x) * x⁻¹ := by group
      rw [this, ← hmod]
      group
    rw [h1, orderOf_one] at hρ
    exact absurd hρ (by norm_num)
  · exact (hs j hjpos hj5).trans (by rw [hmod]; exact hconj.symm)

theorem exists_involution_of_isConj {G : Type*} [Group G] {r ρ a z u₀ : G} (hr : IsConj r ρ)
    (ha : ∀ g : G, g * a = a * g) (hu2 : u₀ * u₀ = 1) (hu1 : u₀ ≠ 1) (hua : u₀ ≠ a)
    (hur : u₀ * r = r * u₀) (hz : IsConj z u₀) :
    ∃ u : G, u * u = 1 ∧ u ≠ 1 ∧ a ≠ u ∧ u * ρ = ρ * u ∧ IsConj z u := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hr
  refine ⟨c * u₀ * c⁻¹, ?_, ?_, ?_, ?_, hz.trans (isConj_iff.2 ⟨c, rfl⟩)⟩
  · calc c * u₀ * c⁻¹ * (c * u₀ * c⁻¹) = c * (u₀ * u₀) * c⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  · intro h
    apply hu1
    have : u₀ = c⁻¹ * (c * u₀ * c⁻¹) * c := by group
    rw [this, h]
    group
  · intro h
    apply hua
    have : u₀ = c⁻¹ * (c * u₀ * c⁻¹) * c := by group
    rw [this, ← h, ha c⁻¹]
    group
  · calc c * u₀ * c⁻¹ * (c * r * c⁻¹) = c * (u₀ * r) * c⁻¹ := by group
      _ = c * (r * u₀) * c⁻¹ := by rw [hur]
      _ = c * r * c⁻¹ * (c * u₀ * c⁻¹) := by group

end CFSG.EvenSporadicStandard.HNRecog
