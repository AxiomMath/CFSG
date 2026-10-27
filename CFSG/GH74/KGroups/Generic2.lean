module

public import CFSG.GH74.KGroups.Generic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify

public section

namespace CFSG.GH74.KGroups

open scoped commutatorElement

theorem pow_two_pow_eq_one_of_card {H : Type*} [Group H] {v m : ℕ}
    (hN : Nat.card H = 2 ^ v * m) (hm : Odd m) {a : H} {n : ℕ} (ha : a ^ (2 ^ n) = 1) :
    a ^ (2 ^ v) = 1 := by
  have h1 : orderOf a ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one ha
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h2 : orderOf a ∣ Nat.card H := orderOf_dvd_natCard a
  rw [hN, hj'] at h2
  have hcop : Nat.Coprime (2 ^ j) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
  have h3 : 2 ^ j ∣ 2 ^ v := hcop.dvd_of_dvd_mul_right h2
  have h4 : j ≤ v := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h3
  refine orderOf_dvd_iff_pow_eq_one.1 ?_
  rw [hj']
  exact Nat.pow_dvd_pow 2 h4

theorem AutModel.inner_of_le {K G : Type*} [Group K] [Group G] (M : AutModel K G)
    (h : M.A ≤ M.P) (φ : MulAut K) : ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹ :=
  M.inner_of_mem φ (h (M.Φ φ).2)

theorem AutModel.out_inner_two {K G : Type*} [Group K] [Group G] (M : AutModel K G) {v m : ℕ}
    (hN : Nat.card (MulAut K) = 2 ^ v * m) (hm : Odd m)
    (hA : ∀ τ ∈ M.A, τ ^ (2 ^ v) = 1 → τ ∈ M.P) (φ : MulAut K) (n : ℕ)
    (hφ : φ ^ (2 ^ n) = 1) : ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹ := by
  have h1 : φ ^ (2 ^ v) = 1 := pow_two_pow_eq_one_of_card hN hm hφ
  refine M.inner_of_mem φ (hA _ (M.Φ φ).2 ?_)
  have h2 : (M.Φ (φ ^ (2 ^ v)) : G) = 1 := by rw [h1, M.Φ_one]
  rwa [M.Φ_pow] at h2

theorem one_class_of_model {K G : Type*} [Group K] [Group G] (P : Subgroup G) (e : K ≃* P)
    (t : G) (h : ∀ u ∈ P, u ^ 2 = 1 → u ≠ 1 → ∃ g ∈ P, g * t * g⁻¹ = u) :
    ∀ u v : K, orderOf u = 2 → orderOf v = 2 → ∃ g : K, g * u * g⁻¹ = v := by
  intro u v hu hv
  have key : ∀ w : K, orderOf w = 2 → ∃ g : P, (g : G) * t * (g : G)⁻¹ = ((e w : P) : G) := by
    intro w hw
    have hw' := orderOf_eq_prime_iff.1 hw
    have h2 : ((e w : P) : G) ^ 2 = 1 := by
      have := congrArg (fun z : P => (z : G)) (show (e w) ^ 2 = 1 by rw [← map_pow, hw'.1, map_one])
      simpa using this
    have h1 : ((e w : P) : G) ≠ 1 := by
      intro h1
      apply hw'.2
      apply e.injective
      apply Subtype.ext
      simpa using h1
    obtain ⟨g, hg, hgt⟩ := h _ (e w).2 h2 h1
    exact ⟨⟨g, hg⟩, hgt⟩
  obtain ⟨g1, h1⟩ := key u hu
  obtain ⟨g2, h2⟩ := key v hv
  refine ⟨e.symm (g2 * g1⁻¹), ?_⟩
  apply e.injective
  apply Subtype.ext
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← h2, ← h1]
  group

section Sylow

open Pointwise

variable {K G : Type*} [Group K] [Group G]

theorem exists_iso_of_sylow [Finite K] (P : Subgroup G) (e : K ≃* P) (S : Subgroup G) (hSP : S ≤ P)
    {v m : ℕ} (hS : Nat.card S = 2 ^ v) (hK : Nat.card K = 2 ^ v * m) (hm : Odd m)
    (T : Sylow 2 K) :
    ∃ e' : K ≃* P, ∀ k : K, k ∈ (T : Subgroup K) ↔ ((e' k : P) : G) ∈ S := by
  classical
  set T0 : Subgroup K := (S.subgroupOf P).comap e.toMonoidHom with hT0
  have hT0mem : ∀ k : K, k ∈ T0 ↔ ((e k : P) : G) ∈ S := fun k => Iff.rfl
  have hcard : Nat.card T0 = 2 ^ v := by
    have h1 : Nat.card T0 = Nat.card (S.subgroupOf P) := by
      refine Nat.card_congr ?_
      exact (MulEquiv.subgroupMap e T0).toEquiv.trans
        (Equiv.subtypeEquivProp (by
          ext y
          simp only [hT0, Subgroup.mem_map, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact hx
          · intro hy
            exact ⟨e.symm y, by simpa using hy, by simp⟩))
    rw [h1, ← hS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv
  have hp0 : IsPGroup 2 T0 := IsPGroup.of_card (n := v) hcard
  have hindex : T0.index = m := by
    have h1 := Subgroup.card_mul_index T0
    rw [hcard, hK] at h1
    have : 0 < 2 ^ v := by positivity
    exact Nat.eq_of_mul_eq_mul_left this h1
  have hnd : ¬ 2 ∣ T0.index := by
    rw [hindex]
    exact fun h => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K (hp0.toSylow hnd) T
  refine ⟨(MulAut.conj g⁻¹).trans e, fun k => ?_⟩
  have h1 : k ∈ (T : Subgroup K) ↔ g⁻¹ * k * g ∈ T0 := by
    have hT : (T : Subgroup K) = MulAut.conj g • (T0 : Subgroup K) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      rfl
    rw [hT, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  rw [h1, hT0mem]
  simp

theorem sylow_equiv_of_model [Finite K] (P : Subgroup G) (e : K ≃* P) (S : Subgroup G)
    (hSP : S ≤ P) {v m : ℕ} (hS : Nat.card S = 2 ^ v) (hK : Nat.card K = 2 ^ v * m) (hm : Odd m)
    (T : Subgroup K) (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) : Nonempty (T ≃* S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e', he'⟩ := exists_iso_of_sylow P e S hSP hS hK hm (hT.toSylow hTi)
  have hmem : ∀ k : K, k ∈ T ↔ ((e' k : P) : G) ∈ S := fun k => he' k
  have hmap : T.map e'.toMonoidHom = S.subgroupOf P := by
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).1 hx
    · intro hy
      refine ⟨e'.symm y, (hmem _).2 (by simpa using hy), by simp⟩
  exact ⟨(MulEquiv.subgroupMap e' T).trans
    ((MulEquiv.subgroupCongr hmap).trans (Subgroup.subgroupOfEquivOfLe hSP))⟩

section Transport

variable {P : Subgroup G} (e' : K ≃* P) {S : Subgroup G} {Q : Subgroup K}

theorem iso_symm_mem (hSP : S ≤ P) (hmem : ∀ k : K, k ∈ Q ↔ ((e' k : P) : G) ∈ S) {s : G}
    (hs : s ∈ S) : ∃ k ∈ Q, ((e' k : P) : G) = s :=
  ⟨e'.symm ⟨s, hSP hs⟩, (hmem _).2 (by simpa using hs), by simp⟩

theorem iso_central (hSP : S ≤ P) (hmem : ∀ k : K, k ∈ Q ↔ ((e' k : P) : G) ∈ S) {a : K} :
    (∀ y ∈ Q, y * a = a * y) ↔ ∀ z ∈ S, z * ((e' a : P) : G) = ((e' a : P) : G) * z := by
  constructor
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := iso_symm_mem e' hSP hmem hz
    have := congrArg (fun w : K => ((e' w : P) : G)) (h y hy)
    simpa using this
  · intro h y hy
    apply e'.injective
    apply Subtype.ext
    have := h _ ((hmem y).1 hy)
    simpa using this

theorem iso_commutator (hSP : S ≤ P) (hmem : ∀ k : K, k ∈ Q ↔ ((e' k : P) : G) ∈ S) {a : K}
    (h : ∃ u ∈ S, ∃ w ∈ S, u * w * u⁻¹ * w⁻¹ = ((e' a : P) : G)) : a ∈ ⁅Q, Q⁆ := by
  obtain ⟨u, hu, w, hw, huw⟩ := h
  obtain ⟨u', hu', rfl⟩ := iso_symm_mem e' hSP hmem hu
  obtain ⟨w', hw', rfl⟩ := iso_symm_mem e' hSP hmem hw
  have : a = ⁅u', w'⁆ := by
    apply e'.injective
    apply Subtype.ext
    rw [← huw]
    simp [commutatorElement_def]
  rw [this]
  exact Subgroup.commutator_mem_commutator hu' hw'

theorem smallTable_of_model [Finite K] (P : Subgroup G) (e : K ≃* P) (S : Subgroup G)
    (hSP : S ≤ P) {v m : ℕ} (hS : Nat.card S = 2 ^ v) (hK : Nat.card K = 2 ^ v * m)
    (hm : Odd m) (hone : ∀ u w : K, orderOf u = 2 → orderOf w = 2 → ∃ g : K, g * u * g⁻¹ = w)
    (s0 : G) (hs0S : s0 ∈ S) (hs01 : s0 ≠ 1) (hs02 : s0 ^ 2 = 1)
    (hs0c : ∀ y ∈ S, y * s0 = s0 * y)
    (h2 : ∀ a ∈ S, (∀ y ∈ S, y * a = a * y) → a ^ 2 = 1 →
      ∃ u ∈ S, ∃ w ∈ S, u * w * u⁻¹ * w⁻¹ = a)
    (h3 : ∀ a ∈ S, (∀ y ∈ S, y * a = a * y) → a ^ 2 = 1 → a = 1 ∨ a = s0)
    (Q : Subgroup K) (hQ : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.index) :
    (∀ x ∈ Q, x ^ 2 = 1 → ∃ k : K, k⁻¹ * x * k ∈ Q ∧
      ∀ y ∈ Q, y * (k⁻¹ * x * k) = (k⁻¹ * x * k) * y) ∧
    (∀ a ∈ Q, (∀ y ∈ Q, y * a = a * y) → a ^ 2 = 1 → a ∈ ⁅Q, Q⁆) ∧
    (∃ s : K, ∀ a ∈ Q, (∀ y ∈ Q, y * a = a * y) → a ^ 2 = 1 → a = 1 ∨ a = s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e', he'⟩ := exists_iso_of_sylow P e S hSP hS hK hm (hQ.toSylow hQi)
  have hmem : ∀ k : K, k ∈ Q ↔ ((e' k : P) : G) ∈ S := fun k => he' k
  obtain ⟨z, hzQ, hz⟩ := iso_symm_mem e' hSP hmem hs0S
  have hzc : ∀ y ∈ Q, y * z = z * y := (iso_central e' hSP hmem).2 (by rw [hz]; exact hs0c)
  have hz2 : orderOf z = 2 := by
    apply orderOf_eq_prime_iff.2
    constructor
    · apply e'.injective
      apply Subtype.ext
      simpa [hz] using hs02
    · intro h1
      apply hs01
      rw [← hz, h1]
      simp
  have key : ∀ a ∈ Q, (∀ y ∈ Q, y * a = a * y) → a ^ 2 = 1 →
      (((e' a : P) : G) ∈ S ∧ ((e' a : P) : G) ^ 2 = 1 ∧
        ∀ y ∈ S, y * ((e' a : P) : G) = ((e' a : P) : G) * y) := by
    intro a ha hac ha2
    refine ⟨(hmem a).1 ha, ?_, (iso_central e' hSP hmem).1 hac⟩
    have := congrArg (fun w : K => ((e' w : P) : G)) ha2
    simpa using this
  refine ⟨?_, ?_, ⟨z, ?_⟩⟩
  · intro x hx hx2
    by_cases hx1 : x = 1
    · exact ⟨1, by simp [hx1], by simp [hx1]⟩
    · have hxo : orderOf x = 2 := orderOf_eq_prime_iff.2 ⟨hx2, hx1⟩
      obtain ⟨g, hg⟩ := hone z x hz2 hxo
      refine ⟨g, ?_, ?_⟩
      · have : g⁻¹ * x * g = z := by rw [← hg]; group
        rw [this]; exact hzQ
      · have : g⁻¹ * x * g = z := by rw [← hg]; group
        rw [this]; exact hzc
  · intro a ha hac ha2
    obtain ⟨haS, ha2', hacS⟩ := key a ha hac ha2
    exact iso_commutator e' hSP hmem (h2 _ haS hacS ha2')
  · intro a ha hac ha2
    obtain ⟨haS, ha2', hacS⟩ := key a ha hac ha2
    rcases h3 _ haS hacS ha2' with h | h
    · left
      apply e'.injective
      apply Subtype.ext
      simpa using h
    · right
      apply e'.injective
      apply Subtype.ext
      rw [h, hz]

theorem sylow_comm_of_model [Finite K] (P : Subgroup G) (e : K ≃* P) (S : Subgroup G)
    (hSP : S ≤ P) {v m : ℕ} (hS : Nat.card S = 2 ^ v) (hK : Nat.card K = 2 ^ v * m)
    (hm : Odd m) (h : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (Q : Subgroup K) (hQ : IsPGroup 2 Q)
    (hQi : ¬ 2 ∣ Q.index) : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e', he'⟩ := exists_iso_of_sylow P e S hSP hS hK hm (hQ.toSylow hQi)
  intro a ha b hb
  apply e'.injective
  apply Subtype.ext
  have := h _ ((he' a).1 ha) _ ((he' b).1 hb)
  simpa using this

theorem benderTable_of_model [Finite K] (P : Subgroup G) (e : K ≃* P) (S : Subgroup G)
    (hSP : S ≤ P) {v m : ℕ} (hS : Nat.card S = 2 ^ v) (hK : Nat.card K = 2 ^ v * m)
    (hm : Odd m) (h1 : ∀ x ∈ S, x ^ 2 = 1 → ∀ y ∈ S, y * x = x * y)
    (h2 : ∀ a ∈ S, (∀ y ∈ S, y * a = a * y) → a ^ 2 = 1)
    (h3 : ∀ a ∈ S, (∀ y ∈ S, y * a = a * y) → ∃ u ∈ S, ∃ w ∈ S, u * w * u⁻¹ * w⁻¹ = a)
    (t : G) (htP : t ∈ P) (htN1 : ∀ y ∈ S, t * y * t⁻¹ ∈ S) (htN2 : ∀ y ∈ S, t⁻¹ * y * t ∈ S)
    (h4 : ∀ a ∈ S, (∀ y ∈ S, y * a = a * y) → a ≠ 1 → ∀ b ∈ S, (∀ y ∈ S, y * b = b * y) →
      b ≠ 1 → ∃ k : ℕ, t ^ k * a * (t ^ k)⁻¹ = b)
    (Q : Subgroup K) (hQ : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.index) :
    (∀ x ∈ Q, x ^ 2 = 1 → ∀ y ∈ Q, y * x = x * y) ∧
    (∀ a ∈ Q ⊓ Subgroup.centralizer (Q : Set K), a ^ 2 = 1) ∧
    (Q ⊓ Subgroup.centralizer (Q : Set K) ≤ ⁅Q, Q⁆) ∧
    (∃ x : K, x ∈ Subgroup.normalizer (Q : Set K) ∧
      ∀ a ∈ Q ⊓ Subgroup.centralizer (Q : Set K), ∀ b ∈ Q ⊓ Subgroup.centralizer (Q : Set K),
        a ≠ 1 → b ≠ 1 → ∃ k : ℕ, x ^ k * a * (x ^ k)⁻¹ = b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e', he'⟩ := exists_iso_of_sylow P e S hSP hS hK hm (hQ.toSylow hQi)
  have hmem : ∀ k : K, k ∈ Q ↔ ((e' k : P) : G) ∈ S := fun k => he' k
  have hcent : ∀ a : K, a ∈ Q ⊓ Subgroup.centralizer (Q : Set K) ↔
      (a ∈ Q ∧ ∀ y ∈ Q, y * a = a * y) := by
    intro a
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨ha, hc⟩
      exact ⟨ha, fun y hy => (hc y hy)⟩
    · rintro ⟨ha, hc⟩
      exact ⟨ha, fun y hy => hc y hy⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hx2 y hy
    apply e'.injective
    apply Subtype.ext
    have hx2' : ((e' x : P) : G) ^ 2 = 1 := by
      have := congrArg (fun w : K => ((e' w : P) : G)) hx2
      simpa using this
    have := h1 _ ((hmem x).1 hx) hx2' _ ((hmem y).1 hy)
    simpa using this
  · intro a ha
    obtain ⟨haQ, hac⟩ := (hcent a).1 ha
    have := h2 _ ((hmem a).1 haQ) ((iso_central e' hSP hmem).1 hac)
    apply e'.injective
    apply Subtype.ext
    simpa using this
  · intro a ha
    obtain ⟨haQ, hac⟩ := (hcent a).1 ha
    exact iso_commutator e' hSP hmem
      (h3 _ ((hmem a).1 haQ) ((iso_central e' hSP hmem).1 hac))
  · refine ⟨e'.symm ⟨t, htP⟩, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro k
      rw [hmem k, hmem]
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      constructor
      · exact htN1 _
      · intro hk
        have := htN2 _ hk
        simpa [mul_assoc] using this
    · intro a ha b hb ha1 hb1
      obtain ⟨haQ, hac⟩ := (hcent a).1 ha
      obtain ⟨hbQ, hbc⟩ := (hcent b).1 hb
      obtain ⟨k, hk⟩ := h4 _ ((hmem a).1 haQ) ((iso_central e' hSP hmem).1 hac)
        (by
          intro h
          apply ha1
          apply e'.injective
          apply Subtype.ext
          simpa using h)
        _ ((hmem b).1 hbQ) ((iso_central e' hSP hmem).1 hbc)
        (by
          intro h
          apply hb1
          apply e'.injective
          apply Subtype.ext
          simpa using h)
      refine ⟨k, ?_⟩
      apply e'.injective
      apply Subtype.ext
      simpa using hk

end Transport

end Sylow

end CFSG.GH74.KGroups
