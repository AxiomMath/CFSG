module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.A

open Subgroup

variable {G : Type*} [Group G]

theorem mem_sup_of_le_normalizer {A B : Subgroup G} (hnorm : A ≤ Subgroup.normalizer (B : Set G))
    {y : G} (hy : y ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B hnorm
  have hy' : y ∈ (↑(A ⊔ B) : Set G) := hy
  rw [hset] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hy'
  exact ⟨a, ha, b, hb, rfl⟩

theorem le_normalizer_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ normalizer (A : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h : b * x * b⁻¹ = x := by rw [← hc x hx b hb]; group
    rwa [h]
  · intro hx
    have hcomm := hc _ hx b hb
    have : x = b * x * b⁻¹ := by
      calc x = b⁻¹ * ((b * x * b⁻¹) * b) := by group
        _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [hcomm]
        _ = b * x * b⁻¹ := by group
    rwa [this]

theorem mem_sup_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {y : G}
    (hy : y ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, y = a * b :=
  mem_sup_of_le_normalizer (le_normalizer_of_commute (fun b hb a ha => (hc a ha b hb).symm)) hy

theorem card_sup_mul_card_inf {A B : Subgroup G} (h : B ≤ normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  set M := B ⊔ A with hM
  have hBM : B ≤ M := le_sup_left
  have hAM : A ≤ M := le_sup_right
  have : (A.subgroupOf M).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have hsup : B.subgroupOf M ⊔ A.subgroupOf M = ⊤ :=
    codisjoint_iff.1 (Subgroup.codisjoint_subgroupOf_sup B A)
  have h1 := Subgroup.relIndex_sup_right (H := B.subgroupOf M) (K := A.subgroupOf M)
  rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hBM] at h1
  have h2 := Subgroup.card_mul_index (A.subgroupOf M)
  have h3 : Nat.card ↥(A.subgroupOf M) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv
  rw [h1, h3] at h2
  have h4 := Subgroup.relIndex_mul_card A B
  rw [sup_comm] at hM
  rw [← hM, ← h2, mul_assoc, h4]

theorem card_sup_mul_card_inf_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B :=
  card_sup_mul_card_inf (le_normalizer_of_commute hc)

theorem dedekind_le {A B C : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAC : A ≤ C)
    (hBC : B ⊓ C ≤ A) : (A ⊔ B) ⊓ C ≤ A := by
  rintro x ⟨hx, hxC⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc hx
  have hbC : b ∈ C := by
    have h1 : a⁻¹ * (a * b) ∈ C := C.mul_mem (C.inv_mem (hAC ha)) hxC
    simpa using h1
  have : b ∈ A := hBC ⟨hb, hbC⟩
  exact A.mul_mem ha this

theorem mem_sup_zpowers_two {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hc : a * b = b * a)
    {x : G} (hx : x ∈ zpowers a ⊔ zpowers b) : x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hcomm : ∀ x ∈ zpowers a, ∀ y ∈ zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
    exact ((show Commute a b from hc).zpow_zpow i j).eq
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hcomm hx
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha₁
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 ha₂
  have zp : ∀ {w : G}, w * w = 1 → ∀ k : ℤ, w ^ k = 1 ∨ w ^ k = w := by
    intro w hw k
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul]
      have : w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hw
      rw [this, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul]
      have : w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hw
      rw [this, one_zpow, one_mul]
  rcases zp ha i with h1 | h1 <;> rcases zp hb j with h2 | h2
  · left; rw [h1, h2, one_mul]
  · right; right; left; rw [h1, h2, one_mul]
  · right; left; rw [h1, h2, mul_one]
  · right; right; right; rw [h1, h2]

theorem relIndex_two_pigeon {X H : Subgroup G} (hH : H.relIndex X = 2) {x y : G} (hx : x ∈ X)
    (hy : y ∈ X) : x ∈ H ∨ y ∈ H ∨ x⁻¹ * y ∈ H := by
  have h2 : (H.subgroupOf X).index = 2 := hH
  have hN : (H.subgroupOf X).Normal := Subgroup.normal_of_index_eq_two h2
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 h2
  by_contra hcon
  push Not at hcon
  obtain ⟨hxH, hyH, hxy⟩ := hcon
  have hx' : (⟨x, hx⟩ : ↥X) ∉ H.subgroupOf X := hxH
  have hy' : (⟨y, hy⟩ : ↥X) ∉ H.subgroupOf X := hyH
  have hxy' : (⟨x, hx⟩ : ↥X)⁻¹ * ⟨y, hy⟩ ∉ H.subgroupOf X := hxy
  have h3 : (⟨x, hx⟩ : ↥X) * a ∈ H.subgroupOf X := by
    rcases ha ⟨x, hx⟩ with h | h
    · exact h.1
    · exact absurd h.1 hx'
  have h4 : (⟨y, hy⟩ : ↥X) * a ∈ H.subgroupOf X := by
    rcases ha ⟨y, hy⟩ with h | h
    · exact h.1
    · exact absurd h.1 hy'
  have h5 : ((⟨x, hx⟩ : ↥X) * a)⁻¹ * ((⟨y, hy⟩ : ↥X) * a) ∈ H.subgroupOf X :=
    (H.subgroupOf X).mul_mem ((H.subgroupOf X).inv_mem h3) h4
  have h6 : a⁻¹ * ((⟨x, hx⟩ : ↥X)⁻¹ * ⟨y, hy⟩) * a⁻¹⁻¹ ∈ H.subgroupOf X := by
    have e : ((⟨x, hx⟩ : ↥X) * a)⁻¹ * ((⟨y, hy⟩ : ↥X) * a) =
        a⁻¹ * ((⟨x, hx⟩ : ↥X)⁻¹ * ⟨y, hy⟩) * a⁻¹⁻¹ := by group
    rw [← e]; exact h5
  have h7 := hN.conj_mem _ h6 a
  have e2 : a * (a⁻¹ * ((⟨x, hx⟩ : ↥X)⁻¹ * ⟨y, hy⟩) * a⁻¹⁻¹) * a⁻¹ =
      (⟨x, hx⟩ : ↥X)⁻¹ * ⟨y, hy⟩ := by group
  rw [e2] at h7
  exact hxy' h7

theorem sq_mem_of_relIndex_two {X H : Subgroup G} (hH : H.relIndex X = 2) {x : G} (hx : x ∈ X) :
    x * x ∈ H := by
  have h2 : (H.subgroupOf X).index = 2 := hH
  have := Subgroup.mul_self_mem_of_index_two h2 ⟨x, hx⟩
  exact this

theorem conj_mem_of_relIndex_two {X H : Subgroup G} (hH : H.relIndex X = 2) {x h : G} (hx : x ∈ X)
    (hh : h ∈ H) (hHX : H ≤ X) : x * h * x⁻¹ ∈ H := by
  have h2 : (H.subgroupOf X).index = 2 := hH
  have hN : (H.subgroupOf X).Normal := Subgroup.normal_of_index_eq_two h2
  have h1 : (⟨h, hHX hh⟩ : ↥X) ∈ H.subgroupOf X := hh
  exact hN.conj_mem _ h1 ⟨x, hx⟩

theorem card_eq_two_mul_of_relIndex_two {A B : Subgroup G} (hAB : A ≤ B) (h : A.relIndex B = 2) :
    Nat.card ↥B = 2 * Nat.card ↥A := by
  have := Subgroup.relIndex_mul_card A B
  rw [inf_eq_left.2 hAB, h] at this
  omega

theorem relIndex_le_two_of_pigeon [Finite G] {X H : Subgroup G}
    (h : ∀ x ∈ X, ∀ y ∈ X, x ∈ H ∨ y ∈ H ∨ x⁻¹ * y ∈ H) : H.relIndex X ≤ 2 := by
  by_contra hcon
  push Not at hcon
  classical
  have := Fintype.ofFinite (↥X ⧸ H.subgroupOf X)
  have h3 : 2 < Fintype.card (↥X ⧸ H.subgroupOf X) := by
    rw [← Nat.card_eq_fintype_card]; exact hcon
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h3
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective c
  have hxy : x⁻¹ * y ∉ H.subgroupOf X := fun hmem => hab (QuotientGroup.eq.2 hmem)
  have hxw : x⁻¹ * w ∉ H.subgroupOf X := fun hmem => hac (QuotientGroup.eq.2 hmem)
  have hyw : y⁻¹ * w ∉ H.subgroupOf X := fun hmem => hbc (QuotientGroup.eq.2 hmem)
  rcases h (x⁻¹ * y : ↥X) (X.mul_mem (X.inv_mem x.2) y.2) (x⁻¹ * w : ↥X)
    (X.mul_mem (X.inv_mem x.2) w.2) with h1 | h1 | h1
  · exact hxy h1
  · exact hxw h1
  · apply hyw
    have e : ((x⁻¹ * y : ↥X) : G)⁻¹ * ((x⁻¹ * w : ↥X) : G) = ((y⁻¹ * w : ↥X) : G) := by
      simp [mul_assoc]
    rw [Subgroup.mem_subgroupOf]
    rw [← e]
    exact h1

theorem relIndex_eq_pow_of_pgroup [Finite G] {X H : Subgroup G} (hX : IsPGroup 2 ↥X) (hHX : H ≤ X) :
    ∃ k : ℕ, H.relIndex X = 2 ^ k := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hX
  have h1 := Subgroup.relIndex_mul_card H X
  rw [inf_eq_left.2 hHX] at h1
  have hdvd : H.relIndex X ∣ 2 ^ n := by
    rw [← hn, ← h1]; exact Dvd.intro _ rfl
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨k, hk⟩

theorem relIndex_cases [Finite G] {X H : Subgroup G} (hX : IsPGroup 2 ↥X) (hHX : H ≤ X)
    (h4 : H.relIndex X ≤ 4) : H.relIndex X = 1 ∨ H.relIndex X = 2 ∨ H.relIndex X = 4 := by
  obtain ⟨k, hk⟩ := relIndex_eq_pow_of_pgroup hX hHX
  rw [hk] at h4 ⊢
  have hk2 : k ≤ 2 := by
    by_contra hcon
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp

theorem card_quat {Q : Subgroup G} {N : ℕ} [NeZero N] (e : ↥Q ≃* QuaternionGroup N) :
    Nat.card ↥Q = 4 * N := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem four_dvd_of_card [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q) {N : ℕ} [NeZero N]
    (e : ↥Q ≃* QuaternionGroup N) (h16 : 16 ≤ Nat.card ↥Q) : 4 ∣ N := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQ
  have hc := card_quat e
  have hn4 : 4 ≤ n := by
    by_contra hcon
    have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2 : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have h3 : N = 2 ^ (n - 2) := by omega
  rw [h3, show n - 2 = 2 + (n - 4) by omega, pow_add]
  exact Dvd.intro _ rfl

theorem N_eq_two_of_card {P : Subgroup G} {N : ℕ} [NeZero N] (e : ↥P ≃* QuaternionGroup N)
    (h8 : Nat.card ↥P = 8) : N = 2 := by
  have := card_quat e
  omega

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.A
