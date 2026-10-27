module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ComponentClassification.CatFactsSp4

open Subgroup

variable {G : Type*} [Group G]

theorem mem_or_mul_mem_of_mem_sup {I : Subgroup G} [I.Normal] {a : G} (ha2 : a * a = 1)
    {x : G} (hx : x ∈ I ⊔ zpowers a) : x ∈ I ∨ x * a ∈ I := by
  have hx' : x ∈ ((I ⊔ zpowers a : Subgroup G) : Set G) := hx
  rw [normal_mul] at hx'
  obtain ⟨i, hi, z, hz, rfl⟩ := hx'
  show i * z ∈ I ∨ i * z * a ∈ I
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  have hord : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha2)
  have hk : a ^ k = a ^ (k % 2) := by
    rw [← zpow_mod_orderOf]
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h1 | h2
    · rw [h1, Int.natCast_one, Int.emod_one, zpow_zero]
      rw [orderOf_eq_one_iff] at h1
      rw [h1, one_zpow]
    · rw [h2]
      rfl
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [hk, h0, zpow_zero, mul_one]
    exact hi
  · right
    rw [hk, h1, zpow_one, mul_assoc, ha2, mul_one]
    exact hi

variable [Finite G]

theorem exists_inner_normalizing {I : Subgroup G} [I.Normal] {a : G} (ha2 : a * a = 1)
    {Q : Subgroup G} (hQC : Q ≤ (I ⊔ zpowers a) ⊓ centralizer ({a} : Set G))
    (hQS : ∃ T : Sylow 2 ↥((I ⊔ zpowers a) ⊓ centralizer ({a} : Set G)),
      (T : Subgroup _) = Q.subgroupOf ((I ⊔ zpowers a) ⊓ centralizer ({a} : Set G)))
    (hdvd : 2 * Nat.card Q ∣ Nat.card (I ⊔ zpowers a : Subgroup G)) :
    ∃ g : G, g ∈ I ∧ g ∈ normalizer (Q : Set G) ∧ g ∉ Q ∧ g * g ∈ Q ∧ a * (g⁻¹ * a * g) ∈ I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := I ⊔ zpowers a with hN
  set C := N ⊓ centralizer ({a} : Set G) with hC
  obtain ⟨T, hT⟩ := hQS
  have hQ2 : IsPGroup 2 Q := by
    have h := T.isPGroup'
    rw [hT] at h
    exact h.of_equiv (subgroupOfEquivOfLe hQC)
  have haC : a ∈ C := ⟨mem_sup_right (mem_zpowers a), mem_centralizer_singleton_iff.mpr rfl⟩
  have haQ : a ∈ Q := by
    set a' : C := ⟨a, haC⟩
    have hn : (zpowers a').Normal := by
      refine ⟨fun x hx c => ?_⟩
      have hxc : c * x * c⁻¹ = x := by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
        have hca : c * a' = a' * c := by
          apply Subtype.ext
          have := mem_centralizer_singleton_iff.mp c.2.2
          exact this
        have : Commute c (a' ^ k) := (Commute.zpow_right hca k)
        rw [this.eq, mul_inv_cancel_right]
      rw [hxc]
      exact hx
    have hp : IsPGroup 2 (zpowers a') := by
      rintro ⟨x, hx⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      refine ⟨1, Subtype.ext ?_⟩
      have ha'2 : a' ^ 2 = 1 := by rw [pow_two]; exact Subtype.ext ha2
      change (a' ^ k) ^ 2 ^ 1 = 1
      rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha'2, one_zpow]
    have := hp.le_sylow_of_normal T
    have ha'T : a' ∈ (T : Subgroup C) := this (mem_zpowers a')
    rw [hT] at ha'T
    exact ha'T
  obtain ⟨n, hn⟩ := hQ2.exists_card_eq
  set H : Subgroup N := Q.subgroupOf N with hH
  have hQN : Q ≤ N := hQC.trans inf_le_left
  have hHc : Nat.card H = 2 ^ n := by
    rw [hH, Nat.card_congr (subgroupOfEquivOfLe hQN).toEquiv, hn]
  have hdvd' : 2 ^ (n + 1) ∣ Nat.card N := by
    rw [pow_succ, mul_comm, ← hn]
    exact hdvd
  have h2 : 2 ∣ Nat.card (normalizer (H : Set N) ⧸ H.subgroupOf (normalizer (H : Set N))) :=
    Sylow.prime_dvd_card_quotient_normalizer hdvd' hHc
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (H : Set N) ⧸
    H.subgroupOf (normalizer (H : Set N))) 2 h2
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hy1 : (y : N) ∉ H := by
    intro hyH
    have : (QuotientGroup.mk y : normalizer (H : Set N) ⧸
        H.subgroupOf (normalizer (H : Set N))) = 1 :=
      (QuotientGroup.eq_one_iff y).mpr hyH
    rw [this, orderOf_one] at hx
    omega
  have hy2 : ((y : N) * (y : N)) ∈ H := by
    have h1 := pow_orderOf_eq_one (QuotientGroup.mk y : normalizer (H : Set N) ⧸
      H.subgroupOf (normalizer (H : Set N)))
    rw [hx, pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at h1
    exact h1
  set g₀ : G := ((y : N) : G) with hg₀
  have hg₀N : g₀ ∈ N := (y : N).2
  have hg₀Q : g₀ ∈ normalizer (Q : Set G) := by
    rw [mem_normalizer_iff]
    intro q
    have hyn := mem_normalizer_iff.mp y.2
    constructor
    · intro hq
      have := (hyn ⟨q, hQN hq⟩).mp hq
      exact this
    · intro hq
      have hqN : q ∈ N := by
        have h1 : g₀ * q * g₀⁻¹ ∈ N := hQN hq
        have h2 : g₀⁻¹ * (g₀ * q * g₀⁻¹) * g₀ ∈ N :=
          mul_mem (mul_mem (inv_mem hg₀N) h1) hg₀N
        simpa [mul_assoc] using h2
      exact (hyn ⟨q, hqN⟩).mpr hq
  have hg₀1 : g₀ ∉ Q := fun h => hy1 h
  have hg₀2 : g₀ * g₀ ∈ Q := hy2
  rcases mem_or_mul_mem_of_mem_sup ha2 hg₀N with hI | hI
  · refine ⟨g₀, hI, hg₀Q, hg₀1, hg₀2, ?_⟩
    have h1 : a * g₀⁻¹ * a⁻¹ ∈ I := (inferInstance : I.Normal).conj_mem _ (inv_mem hI) a
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have : a * (g₀⁻¹ * a * g₀) = a * g₀⁻¹ * a⁻¹ * g₀ := by rw [hainv]; group
    rw [this]
    exact mul_mem h1 hI
  · have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have haN : a ∈ normalizer (Q : Set G) := le_normalizer haQ
    refine ⟨g₀ * a, hI, mul_mem hg₀Q haN, fun h => hg₀1 ?_, ?_, ?_⟩
    · have := mul_mem h (inv_mem haQ)
      rwa [mul_inv_cancel_right] at this
    · have hc : g₀⁻¹ * a * g₀ ∈ Q := by
        have := (mem_normalizer_iff.mp (inv_mem hg₀Q) a).mp haQ
        simpa using this
      have : g₀ * a * (g₀ * a) = g₀ * g₀ * (g₀⁻¹ * a * g₀) * a := by group
      rw [this]
      exact mul_mem (mul_mem hg₀2 hc) haQ
    · have h1 : a * (g₀ * a)⁻¹ * a⁻¹ ∈ I :=
        (inferInstance : I.Normal).conj_mem _ (inv_mem hI) a
      have : a * ((g₀ * a)⁻¹ * a * (g₀ * a)) = a * (g₀ * a)⁻¹ * a⁻¹ * (g₀ * a) := by
        rw [hainv]; group
      rw [this]
      exact mul_mem h1 hI

end CFSG.ComponentClassification.CatFactsSp4
