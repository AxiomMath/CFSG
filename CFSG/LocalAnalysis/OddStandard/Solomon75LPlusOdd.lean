module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusTwoElt

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

variable {A B : Type} [Group A] [Group B]

theorem exists_odd_lift [Finite A] (φ : A →* B) (hφ : Function.Surjective φ) {x : B}
    (hx : Odd (orderOf x)) : ∃ y : A, Odd (orderOf y) ∧ φ y = x := by
  obtain ⟨y₀, rfl⟩ := hφ x
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y₀).ne'
  have hcop : Nat.Coprime (2 ^ a) (orderOf (φ y₀)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hx)
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(y₀ ^ (2 ^ a)) ^ k, ?_, ?_⟩
  · have h1 : ((y₀ ^ (2 ^ a)) ^ k) ^ m = 1 := by
      have : ((y₀ ^ (2 ^ a)) ^ k) ^ m = (y₀ ^ (2 ^ a * m)) ^ k := by
        rw [← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        ring
      rw [this, ← hord, pow_orderOf_eq_one, one_pow]
    exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  · rw [map_pow, map_pow]
    exact hk

theorem mem_of_odd_orderOf_of_index {C : Type} [Group C] (N : Subgroup C) [N.Normal] {k : ℕ}
    (hk : N.index = 2 ^ k) {c : C} (hc : Odd (orderOf c)) : c ∈ N := by
  have h1 : c ^ N.index ∈ N := Subgroup.pow_index_mem N c
  rw [hk] at h1
  have hcop : Nat.Coprime (2 ^ k) (orderOf c) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hc)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hj]
  exact N.pow_mem h1 j

theorem eq_one_of_twoElt_of_odd_card {C : Type} [Group C] (N : Subgroup C)
    (hN : Odd (Nat.card N)) {x : C} (hx : x ∈ N) (h2 : TwoElt x) : x = 1 := by
  obtain ⟨k, hk⟩ := h2
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2' : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
  have hcop : Nat.Coprime (2 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN)
  have := Nat.dvd_gcd h1 h2'
  rw [Nat.Coprime.gcd_eq_one hcop] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

variable {G : Type} [Group G]

theorem relIndex_ne_zero_of_finite [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  have := Subgroup.isFiniteRelIndex_of_finiteIndex (H := H) (K := K)
  exact Subgroup.relIndex_ne_zero

theorem relIndex_sup_eq [Finite G] {H : Subgroup G} [H.Normal] (B : Subgroup G) :
    B.relIndex (B ⊔ H) = (B ⊓ H).relIndex H := by
  have h1 := Subgroup.relIndex_mul_relIndex (H := B ⊓ H) (K := B) (L := B ⊔ H) inf_le_left
    le_sup_left
  have h2 := Subgroup.relIndex_mul_relIndex (H := B ⊓ H) (K := H) (L := B ⊔ H) inf_le_right
    le_sup_right
  have h3 : H.relIndex (B ⊔ H) = H.relIndex B := Subgroup.relIndex_sup_right (H := B) (K := H)
  have h4 : (B ⊓ H).relIndex B = H.relIndex B := Subgroup.inf_relIndex_left B H
  have hpos : 0 < (B ⊓ H).relIndex B :=
    Nat.pos_of_ne_zero (relIndex_ne_zero_of_finite _ _)
  rw [h3, ← h4] at h2
  rw [← h2] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])

theorem odd_relIndex_of_le [Finite G] {B H M : Subgroup G} [H.Normal] (hHM : H ≤ M)
    (h : Odd ((B ⊓ M).relIndex M)) : Odd ((B ⊓ H).relIndex H) := by
  have hBH : B ⊓ M ⊓ H = B ⊓ H := by
    ext x
    simp only [mem_inf]
    constructor
    · rintro ⟨⟨hb, _⟩, hh⟩
      exact ⟨hb, hh⟩
    · rintro ⟨hb, hh⟩
      exact ⟨⟨hb, hHM hh⟩, hh⟩
  have h1 := relIndex_sup_eq (H := H) (B ⊓ M)
  rw [hBH] at h1
  have h2 := Subgroup.relIndex_mul_relIndex (H := B ⊓ M) (K := (B ⊓ M) ⊔ H) (L := M)
    le_sup_left (sup_le inf_le_right hHM)
  rw [h1] at h2
  rw [← h2] at h
  exact (Nat.odd_mul.mp h).1

theorem exists_two_subgroup_normalizing [Finite G] (K B : Subgroup G) (hB : IsPGroup 2 B)
    (hBK : B ≤ K) (heven : ¬ Odd (B.relIndex K)) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ B < T ∧ T ≤ K ∧ T ≤ normalizer (B : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B' : Subgroup ↥K := B.subgroupOf K with hB'
  have hB'p : IsPGroup 2 B' := hB.comap_subtype
  obtain ⟨Q, hQ⟩ := hB'p.exists_le_sylow
  have hne : ¬ (Q : Subgroup ↥K) ≤ B' := by
    intro hle
    have heq : (Q : Subgroup ↥K) = B' := le_antisymm hle hQ
    apply heven
    have : ¬ 2 ∣ B'.index := by
      rw [← heq]
      exact Sylow.not_dvd_index Q
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp this)
  set Q₀ : Subgroup G := (Q : Subgroup ↥K).map K.subtype with hQ₀
  have hQ₀p : IsPGroup 2 Q₀ := Q.isPGroup'.map K.subtype
  have hQ₀K : Q₀ ≤ K := Subgroup.map_subtype_le _
  have hBQ₀ : B ≤ Q₀ := by
    have : B'.map K.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBK
    rw [← this]
    exact Subgroup.map_mono hQ
  have hQ₀B : ¬ Q₀ ≤ B := by
    intro hle
    apply hne
    intro x hx
    have : (x : G) ∈ B := hle ⟨x, hx, rfl⟩
    exact this
  have hnil : Group.IsNilpotent ↥Q₀ := hQ₀p.isNilpotent
  have hlt : B.subgroupOf Q₀ < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hQ₀B ?_
    intro x hx
    have : (⟨x, hx⟩ : ↥Q₀) ∈ B.subgroupOf Q₀ := by rw [htop]; exact Subgroup.mem_top _
    exact this
  obtain ⟨q, hqn, hqB⟩ := IsConcreteLE.exists_of_lt
    ((Group.normalizerCondition_of_isNilpotent (G := ↥Q₀)) _ hlt)
  refine ⟨Q₀ ⊓ normalizer (B : Set G), hQ₀p.to_inf_left, ?_, inf_le_left.trans hQ₀K, inf_le_right⟩
  refine lt_of_le_of_ne (le_inf hBQ₀ Subgroup.le_normalizer) fun heq => hqB ?_
  have hqnorm : (q : G) ∈ normalizer (B : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxq : (⟨x, hBQ₀ hx⟩ : ↥Q₀) ∈ B.subgroupOf Q₀ := hx
      have := (mem_normalizer_iff.mp hqn _).mp hxq
      exact this
    · intro hx
      have hxQ : x ∈ Q₀ := by
        have h1 : (q : G)⁻¹ * ((q : G) * x * (q : G)⁻¹) * (q : G) ∈ Q₀ :=
          Q₀.mul_mem (Q₀.mul_mem (Q₀.inv_mem q.2) (hBQ₀ hx)) q.2
        simpa [mul_assoc] using h1
      have hxq : (q * ⟨x, hxQ⟩ * q⁻¹ : ↥Q₀) ∈ B.subgroupOf Q₀ := hx
      have := (mem_normalizer_iff.mp hqn ⟨x, hxQ⟩).mpr hxq
      exact this
  have hqT : (q : G) ∈ Q₀ ⊓ normalizer (B : Set G) := ⟨q.2, hqnorm⟩
  rw [← heq] at hqT
  exact hqT

end CFSG.OddStandard.Solomon75
