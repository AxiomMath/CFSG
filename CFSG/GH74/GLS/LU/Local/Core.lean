module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup
open scoped commutatorElement

theorem conj_mem_of_cyclic {G : Type*} [Group G] {A N : Subgroup G} [IsCyclic A] (hNA : N ≤ A)
    {c : G} (hc : c ∈ normalizer (A : Set G)) {x : G} (hx : x ∈ N) : c * x * c⁻¹ ∈ N := by
  obtain ⟨a, ha⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top A).mp inferInstance
  have haA : a ∈ A := ha ▸ mem_zpowers a
  have hcaA : c * a * c⁻¹ ∈ A := (mem_normalizer_iff.mp hc a).mp haA
  rw [← ha] at hcaA
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hcaA
  have hxA : x ∈ zpowers a := ha ▸ hNA hx
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hxA
  have h1 : c * x * c⁻¹ = x ^ m := by
    rw [← hk, ← conj_zpow, ← hm, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [h1]
  exact N.zpow_mem hx m

theorem normalizer_le_of_cyclic {G : Type*} [Group G] {A N : Subgroup G} [IsCyclic A]
    (hNA : N ≤ A) : normalizer (A : Set G) ≤ normalizer (N : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_of_cyclic hNA hc hh, fun hh => ?_⟩
  have hc' : c⁻¹ ∈ normalizer (A : Set G) := inv_mem hc
  have := conj_mem_of_cyclic hNA hc' hh
  simpa [mul_assoc] using this

theorem perfect_le_centralizer_of_cyclic {G : Type*} [Group G] {A P : Subgroup G} [IsCyclic A]
    (hP : ⁅P, P⁆ = P) (hPN : P ≤ normalizer (A : Set G)) : P ≤ centralizer (A : Set G) := by
  obtain ⟨a, ha⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top A).mp inferInstance
  have haA : a ∈ A := ha ▸ mem_zpowers a
  have hact : ∀ g ∈ normalizer (A : Set G), ∃ m : ℤ, g * a * g⁻¹ = a ^ m := by
    intro g hg
    have hgA : g * a * g⁻¹ ∈ A := (mem_normalizer_iff.mp hg a).mp haA
    rw [← ha] at hgA
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hgA
    exact ⟨m, hm.symm⟩
  have hAeq : ∀ y ∈ A, ∃ k : ℤ, y = a ^ k := by
    intro y hy
    rw [← ha] at hy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy
    exact ⟨k, hk.symm⟩
  have hcomm : ∀ g ∈ normalizer (A : Set G), ∀ h ∈ normalizer (A : Set G), ∀ y ∈ A,
      g * h * y * (g * h)⁻¹ = h * g * y * (h * g)⁻¹ := by
    intro g hg h hh y hy
    obtain ⟨m₁, h₁⟩ := hact g hg
    obtain ⟨m₂, h₂⟩ := hact h hh
    obtain ⟨k, rfl⟩ := hAeq y hy
    have e12 : g * h * a ^ k * (g * h)⁻¹ = a ^ (m₁ * m₂ * k) := by
      calc g * h * a ^ k * (g * h)⁻¹ = g * (h * a ^ k * h⁻¹) * g⁻¹ := by group
        _ = g * ((h * a * h⁻¹) ^ k) * g⁻¹ := by rw [conj_zpow]
        _ = g * ((a ^ m₂) ^ k) * g⁻¹ := by rw [h₂]
        _ = (g * a * g⁻¹) ^ (m₂ * k) := by rw [← zpow_mul, conj_zpow]
        _ = (a ^ m₁) ^ (m₂ * k) := by rw [h₁]
        _ = a ^ (m₁ * m₂ * k) := by rw [← zpow_mul, mul_assoc]
    have e21 : h * g * a ^ k * (h * g)⁻¹ = a ^ (m₁ * m₂ * k) := by
      calc h * g * a ^ k * (h * g)⁻¹ = h * (g * a ^ k * g⁻¹) * h⁻¹ := by group
        _ = h * ((g * a * g⁻¹) ^ k) * h⁻¹ := by rw [conj_zpow]
        _ = h * ((a ^ m₁) ^ k) * h⁻¹ := by rw [h₁]
        _ = (h * a * h⁻¹) ^ (m₁ * k) := by rw [← zpow_mul, conj_zpow]
        _ = (a ^ m₂) ^ (m₁ * k) := by rw [h₂]
        _ = a ^ (m₂ * (m₁ * k)) := by rw [← zpow_mul]
        _ = a ^ (m₁ * m₂ * k) := by congr 1; ring
    rw [e12, e21]
  have key : ⁅P, P⁆ ≤ centralizer (A : Set G) := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    have hgN := hPN hg
    have hhN := hPN hh
    rw [mem_centralizer_iff]
    intro y hy
    have hc' : ∀ y ∈ A, ((h * g)⁻¹ * (g * h)) * y * ((h * g)⁻¹ * (g * h))⁻¹ = y := by
      intro y hy
      have := hcomm g hgN h hhN y hy
      calc ((h * g)⁻¹ * (g * h)) * y * ((h * g)⁻¹ * (g * h))⁻¹
          = (h * g)⁻¹ * (g * h * y * (g * h)⁻¹) * (h * g) := by group
        _ = (h * g)⁻¹ * (h * g * y * (h * g)⁻¹) * (h * g) := by rw [this]
        _ = y := by group
    have hcomm_eq : ⁅g, h⁆ = (h * g) * ((h * g)⁻¹ * (g * h)) * (h * g)⁻¹ := by
      simp only [commutatorElement_def]; group
    have hhgN : (h * g) ∈ normalizer (A : Set G) := mul_mem hhN hgN
    have hy2 : (h * g)⁻¹ * y * (h * g) ∈ A := by
      have := (mem_normalizer_iff.mp (inv_mem hhgN) y).mp hy
      simpa using this
    have h6 := hc' _ hy2
    have h7 : ⁅g, h⁆ * y * ⁅g, h⁆⁻¹ = y := by
      rw [hcomm_eq]
      calc (h * g) * ((h * g)⁻¹ * (g * h)) * (h * g)⁻¹ * y *
            ((h * g) * ((h * g)⁻¹ * (g * h)) * (h * g)⁻¹)⁻¹
          = (h * g) * (((h * g)⁻¹ * (g * h)) * ((h * g)⁻¹ * y * (h * g)) *
              ((h * g)⁻¹ * (g * h))⁻¹) * (h * g)⁻¹ := by group
        _ = (h * g) * ((h * g)⁻¹ * y * (h * g)) * (h * g)⁻¹ := by rw [h6]
        _ = y := by group
    have : ⁅g, h⁆ * y = y * ⁅g, h⁆ := by
      rw [mul_inv_eq_iff_eq_mul] at h7; exact h7
    exact this.symm
  intro g hg
  have hg' : g ∈ ⁅P, P⁆ := by rw [hP]; exact hg
  exact key hg'

theorem centralizes_of_perfect_mod_center {G : Type*} [Group G] {J : Subgroup G} (hJ : ⁅J, J⁆ = J)
    {x : G} (h : ∀ j ∈ J, ∃ c ∈ J, (∀ g ∈ J, c * g = g * c) ∧ x * j * x⁻¹ = c * j) :
    ∀ j ∈ J, x * j * x⁻¹ = j := by
  have key : ⁅J, J⁆ ≤ centralizer ({x} : Set G) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨c₁, hc₁J, hc₁, e₁⟩ := h g₁ hg₁
    obtain ⟨c₂, hc₂J, hc₂, e₂⟩ := h g₂ hg₂
    rw [mem_centralizer_singleton_iff]
    have h1 : x * ⁅g₁, g₂⁆ * x⁻¹ = ⁅x * g₁ * x⁻¹, x * g₂ * x⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    have h2 : ⁅c₁ * g₁, c₂ * g₂⁆ = ⁅g₁, g₂⁆ := by
      have a1 : c₁ * g₁ = g₁ * c₁ := hc₁ g₁ hg₁
      have a2 : c₁ * g₂ = g₂ * c₁ := hc₁ g₂ hg₂
      have a3 : c₁ * c₂ = c₂ * c₁ := hc₁ c₂ hc₂J
      have b1 : c₂ * g₁ = g₁ * c₂ := hc₂ g₁ hg₁
      have b2 : c₂ * g₂ = g₂ * c₂ := hc₂ g₂ hg₂
      simp only [commutatorElement_def, mul_inv_rev]
      calc c₁ * g₁ * (c₂ * g₂) * (g₁⁻¹ * c₁⁻¹) * (g₂⁻¹ * c₂⁻¹)
          = c₁ * (g₁ * c₂ * g₂ * g₁⁻¹) * c₁⁻¹ * (g₂⁻¹ * c₂⁻¹) := by group
        _ = (g₁ * c₂ * g₂ * g₁⁻¹) * (g₂⁻¹ * c₂⁻¹) := by
            have : c₁ * (g₁ * c₂ * g₂ * g₁⁻¹) = (g₁ * c₂ * g₂ * g₁⁻¹) * c₁ := by
              calc c₁ * (g₁ * c₂ * g₂ * g₁⁻¹) = (c₁ * g₁) * c₂ * g₂ * g₁⁻¹ := by group
                _ = g₁ * c₁ * c₂ * g₂ * g₁⁻¹ := by rw [a1]
                _ = g₁ * (c₁ * c₂) * g₂ * g₁⁻¹ := by group
                _ = g₁ * (c₂ * c₁) * g₂ * g₁⁻¹ := by rw [a3]
                _ = g₁ * c₂ * (c₁ * g₂) * g₁⁻¹ := by group
                _ = g₁ * c₂ * (g₂ * c₁) * g₁⁻¹ := by rw [a2]
                _ = g₁ * c₂ * g₂ * (c₁ * g₁⁻¹) := by group
                _ = g₁ * c₂ * g₂ * g₁⁻¹ * c₁ := by
                    have : c₁ * g₁⁻¹ = g₁⁻¹ * c₁ := by
                      have := hc₁ g₁⁻¹ (inv_mem hg₁); exact this
                    rw [this]; group
            rw [this]; group
        _ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by
            have c2g1 : c₂ * g₁⁻¹ = g₁⁻¹ * c₂ := hc₂ g₁⁻¹ (inv_mem hg₁)
            have c2g2 : c₂ * g₂⁻¹ = g₂⁻¹ * c₂ := hc₂ g₂⁻¹ (inv_mem hg₂)
            calc g₁ * c₂ * g₂ * g₁⁻¹ * (g₂⁻¹ * c₂⁻¹)
                = g₁ * (c₂ * g₂ * g₁⁻¹ * g₂⁻¹) * c₂⁻¹ := by group
              _ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹ * c₂) * c₂⁻¹ := by
                  congr 2
                  calc c₂ * g₂ * g₁⁻¹ * g₂⁻¹ = (c₂ * g₂) * g₁⁻¹ * g₂⁻¹ := by group
                    _ = g₂ * c₂ * g₁⁻¹ * g₂⁻¹ := by rw [b2]
                    _ = g₂ * (c₂ * g₁⁻¹) * g₂⁻¹ := by group
                    _ = g₂ * (g₁⁻¹ * c₂) * g₂⁻¹ := by rw [c2g1]
                    _ = g₂ * g₁⁻¹ * (c₂ * g₂⁻¹) := by group
                    _ = g₂ * g₁⁻¹ * (g₂⁻¹ * c₂) := by rw [c2g2]
                    _ = g₂ * g₁⁻¹ * g₂⁻¹ * c₂ := by group
              _ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by group
    rw [e₁, e₂, h2] at h1
    have := h1
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  intro j hj
  have hj' : j ∈ ⁅J, J⁆ := by rw [hJ]; exact hj
  have := key hj'
  rw [mem_centralizer_singleton_iff] at this
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

theorem centralizes_of_diagonal {G : Type*} [Group G] {J₁ J₂ I : Subgroup G}
    (h₁ : ⁅J₁, J₁⁆ = J₁) (h₂ : ⁅J₂, J₂⁆ = J₂) (hc : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a)
    (hI₁ : ∀ j ∈ J₁, ∃ i ∈ I, ∃ b ∈ J₂, j = i * b)
    (hI₂ : ∀ j ∈ J₂, ∃ i ∈ I, ∃ b ∈ J₁, j = i * b)
    {x : G} (hx₁ : ∀ a ∈ J₁, x * a * x⁻¹ ∈ J₁) (hx₂ : ∀ a ∈ J₂, x * a * x⁻¹ ∈ J₂)
    (hxI : ∀ i ∈ I, x * i * x⁻¹ = i) :
    (∀ j ∈ J₁, x * j * x⁻¹ = j) ∧ (∀ j ∈ J₂, x * j * x⁻¹ = j) := by
  have key : ∀ {A B : Subgroup G}, ⁅A, A⁆ = A →
      (∀ a ∈ B, ∀ b ∈ A, a * b = b * a) → (∀ j ∈ A, ∃ i ∈ I, ∃ b ∈ B, j = i * b) →
      (∀ a ∈ A, x * a * x⁻¹ ∈ A) → (∀ a ∈ B, x * a * x⁻¹ ∈ B) →
      ∀ j ∈ A, x * j * x⁻¹ = j := by
    intro A B hA hcBA hIA hxA hxB
    refine centralizes_of_perfect_mod_center hA ?_
    intro j hj
    obtain ⟨i, hi, b, hb, hjib⟩ := hIA j hj
    have e : x * j * x⁻¹ = i * (x * b * x⁻¹) := by
      have := hxI i hi
      calc x * j * x⁻¹ = x * (i * b) * x⁻¹ := by rw [hjib]
        _ = (x * i * x⁻¹) * (x * b * x⁻¹) := by group
        _ = i * (x * b * x⁻¹) := by rw [this]
    have hcB : j⁻¹ * (x * j * x⁻¹) ∈ B := by
      rw [e, hjib]
      have : (i * b)⁻¹ * (i * (x * b * x⁻¹)) = b⁻¹ * (x * b * x⁻¹) := by group
      rw [this]
      exact B.mul_mem (B.inv_mem hb) (hxB b hb)
    have hcA : j⁻¹ * (x * j * x⁻¹) ∈ A := A.mul_mem (A.inv_mem hj) (hxA _ hj)
    refine ⟨j⁻¹ * (x * j * x⁻¹), hcA, ?_, ?_⟩
    · intro g hg
      exact hcBA _ hcB g hg
    · calc x * j * x⁻¹ = j * (j⁻¹ * (x * j * x⁻¹)) := by group
        _ = (j⁻¹ * (x * j * x⁻¹)) * j := (hcBA _ hcB j hj).symm
  exact ⟨key h₁ (fun a ha b hb => (hc b hb a ha).symm) hI₁ hx₁ hx₂,
    key h₂ hc hI₂ hx₂ hx₁⟩

theorem inverts_of_fixed_eq_bot {G : Type*} [Group G] {A : Subgroup G} {t : G} (ht : t * t = 1)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (htn : ∀ a ∈ A, t * a * t⁻¹ ∈ A)
    (hfix : ∀ a ∈ A, t * a * t⁻¹ = a → a = 1) : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ := by
  intro a ha
  have hb : a * (t * a * t⁻¹) ∈ A := A.mul_mem ha (htn a ha)
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hti : t⁻¹ * t⁻¹ = 1 := by rw [ht']; exact ht
  have hfixed : t * (a * (t * a * t⁻¹)) * t⁻¹ = a * (t * a * t⁻¹) := by
    have e : t * (a * (t * a * t⁻¹)) * t⁻¹ = (t * a * t⁻¹) * a := by
      calc t * (a * (t * a * t⁻¹)) * t⁻¹
          = (t * a * t⁻¹) * ((t * t) * a * (t⁻¹ * t⁻¹)) := by group
        _ = (t * a * t⁻¹) * a := by rw [ht, hti]; group
    rw [e]
    exact hAc _ (htn a ha) a ha
  have h1 := hfix _ hb hfixed
  have h2 : a * (t * a * t⁻¹) = 1 := h1
  exact eq_inv_of_mul_eq_one_right h2

theorem lemma62a_core {G : Type*} [Group G] [Finite G] {z : G} {A₀ J₁ J₂ I : Subgroup G}
    [IsCyclic A₀]
    (hA₀n : ∀ c ∈ centralizer ({z} : Set G), c ∈ normalizer (A₀ : Set G))
    (hAI : ∀ a ∈ A₀, ∀ i ∈ I, a * i = i * a)
    (hdiag : ∀ x : G, (∀ i ∈ I, x * i * x⁻¹ = i) → (∀ a ∈ J₁, x * a * x⁻¹ ∈ J₁) →
      (∀ a ∈ J₂, x * a * x⁻¹ ∈ J₂) →
      (∀ j ∈ J₁, x * j * x⁻¹ = j) ∧ (∀ j ∈ J₂, x * j * x⁻¹ = j))
    {t : G}
    (hnorm : ∀ x ∈ A₀, x * t = t * x →
      (∀ a ∈ J₁, x * a * x⁻¹ ∈ J₁) ∧ (∀ a ∈ J₂, x * a * x⁻¹ ∈ J₂))
    (hmax : ∀ Y : Subgroup G, Y ≠ ⊥ → (∃ r : ℕ, r.Prime ∧ IsPGroup r Y) →
      centralizer ({z} : Set G) ≤ normalizer (Y : Set G) →
        normalizer (Y : Set G) = centralizer ({z} : Set G))
    (hJC : ¬ (J₁ ⊔ J₂ ≤ centralizer ({z} : Set G))) :
    ∀ a ∈ A₀, a * t = t * a → a = 1 := by
  intro a ha hat
  by_contra hne
  have h1 : orderOf a ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd h1
  set b := a ^ (orderOf a / r) with hb
  have hbo : orderOf b = r := orderOf_pow_orderOf_div (orderOf_pos a).ne' hrd
  have hbA : b ∈ A₀ := A₀.pow_mem ha _
  have hbt : b * t = t * b := by
    have := (Commute.pow_left (show Commute a t from hat) (orderOf a / r))
    exact this.eq
  set R := zpowers b with hR
  have hRA : R ≤ A₀ := (Subgroup.zpowers_le).mpr hbA
  have hRne : R ≠ ⊥ := by
    intro h
    have : b = 1 := by
      have hb1 : b ∈ R := mem_zpowers b
      rw [h] at hb1; exact hb1
    rw [this, orderOf_one] at hbo
    exact hr.one_lt.ne hbo
  have hRp : IsPGroup r R := by
    have hcard : Nat.card R = r := by
      rw [hR, Nat.card_zpowers, hbo]
    have : Fact r.Prime := ⟨hr⟩
    exact IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  have hCN : centralizer ({z} : Set G) ≤ normalizer (R : Set G) := fun c hc' =>
    normalizer_le_of_cyclic hRA (hA₀n c hc')
  have hN := hmax R hRne ⟨r, hr, hRp⟩ hCN
  obtain ⟨hb₁, hb₂⟩ := hnorm b hbA hbt
  have hcent := hdiag b (fun i hi => by
    have := hAI b hbA i hi
    rw [this]; group) hb₁ hb₂
  have hnormR : ∀ j : G, b * j * b⁻¹ = j → j ∈ normalizer (R : Set G) := by
    intro j hj
    have hcomm : Commute j b := by
      have : b * j = j * b := by
        rw [mul_inv_eq_iff_eq_mul] at hj; exact hj
      exact this.symm
    rw [mem_normalizer_iff]
    intro y
    have key : ∀ y ∈ R, j * y * j⁻¹ = y := by
      intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      have := (Commute.zpow_right hcomm k).eq
      rw [this]; group
    constructor
    · intro hy; rw [key y hy]; exact hy
    · intro hy
      have hcomm' : Commute j⁻¹ b := hcomm.inv_left
      have key' : ∀ y ∈ R, j⁻¹ * y * j = y := by
        intro y hy
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        have := (Commute.zpow_right hcomm' k).eq
        rw [this]; group
      have h3 := key' _ hy
      rw [show j⁻¹ * (j * y * j⁻¹) * j = y by group] at h3
      rw [← h3] at hy
      exact hy
  have hJ : J₁ ⊔ J₂ ≤ centralizer ({z} : Set G) := by
    have hJN : J₁ ⊔ J₂ ≤ normalizer (R : Set G) := by
      refine sup_le (fun j hj => hnormR j (hcent.1 j hj)) (fun j hj => hnormR j (hcent.2 j hj))
    rw [← hN]; exact hJN
  exact hJC hJ

theorem lemma62b_core {G : Type*} [Group G] {A₀ : Subgroup G} {t t₀ q' u : G}
    (hq : ∀ a ∈ A₀, q' * a * q'⁻¹ = a) (ht : ∀ a ∈ A₀, t * a * t⁻¹ = a⁻¹)
    (ht₀ : ∀ a ∈ A₀, t₀ * a * t₀⁻¹ = a⁻¹) (h : t₀ = q' * u * t) :
    ∀ a ∈ A₀, u * a * u⁻¹ = a := by
  intro a ha
  have h1 : t₀ * a * t₀⁻¹ = q' * u * (t * a * t⁻¹) * u⁻¹ * q'⁻¹ := by
    rw [h]; group
  rw [ht₀ a ha, ht a ha] at h1
  have hqa : q' * u * a⁻¹ * u⁻¹ * q'⁻¹ = a⁻¹ := h1.symm
  have hq' : q'⁻¹ * a⁻¹ * q' = a⁻¹ := by
    have := hq a⁻¹ (A₀.inv_mem ha)
    calc q'⁻¹ * a⁻¹ * q' = q'⁻¹ * (q' * a⁻¹ * q'⁻¹) * q' := by rw [this]
      _ = a⁻¹ := by group
  have h2 : u * a⁻¹ * u⁻¹ = a⁻¹ := by
    calc u * a⁻¹ * u⁻¹ = q'⁻¹ * (q' * u * a⁻¹ * u⁻¹ * q'⁻¹) * q' := by group
      _ = q'⁻¹ * a⁻¹ * q' := by rw [hqa]
      _ = a⁻¹ := hq'
  have h3 : u * a * u⁻¹ = a := by
    have := congrArg (·⁻¹) h2
    simpa [mul_assoc] using this
  exact h3


@[expose] def cj {G : Type*} [Group G] (H : Subgroup G) (g : G) : Subgroup G :=
  H.map (MulAut.conj g⁻¹).toMonoidHom

theorem mem_cj {G : Type*} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ cj H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    have : g * ((MulAut.conj g⁻¹).toMonoidHom h) * g⁻¹ = h := by
      show g * (g⁻¹ * h * g⁻¹⁻¹) * g⁻¹ = h
      group
    rw [this]; exact hh
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
    group

theorem cj_commutator {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    ⁅cj H g, cj H g⁆ = cj ⁅H, H⁆ g := by
  unfold cj
  rw [Subgroup.map_commutator]

theorem cj_sup {G : Type*} [Group G] (H K : Subgroup G) (g : G) :
    cj (H ⊔ K) g = cj H g ⊔ cj K g := by
  unfold cj
  rw [Subgroup.map_sup]

theorem cj_card {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Nat.card (cj H g) = Nat.card H := by
  unfold cj
  exact Nat.card_congr ((MulAut.conj g⁻¹).subgroupMap H).toEquiv.symm

@[expose] def diagHom {G : Type*} [Group G] (K₁ K₂ : Subgroup G) (t : G)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (ht : ∀ k ∈ K₁, t * k * t⁻¹ ∈ K₂) : K₁ →* G where
  toFun k := (k : G) * (t * (k : G) * t⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have h1 : (a : G) * (t * (b : G) * t⁻¹) = (t * (b : G) * t⁻¹) * a := hc a a.2 _ (ht b b.2)
    have h2 : (b : G) * (t * (a : G) * t⁻¹) = (t * (a : G) * t⁻¹) * b := hc b b.2 _ (ht a a.2)
    have h3 : (t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹) = t * ((a : G) * b) * t⁻¹ := by group
    show (↑(a * b) : G) * (t * ↑(a * b) * t⁻¹) = (↑a * (t * ↑a * t⁻¹)) * (↑b * (t * ↑b * t⁻¹))
    have e : (↑(a * b) : G) = (a : G) * b := rfl
    rw [e]
    calc ((a : G) * b) * (t * ((a : G) * b) * t⁻¹)
        = (a : G) * (b * ((t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹))) := by
          rw [← h3]; group
      _ = (a : G) * ((b * (t * (a : G) * t⁻¹)) * (t * (b : G) * t⁻¹)) := by group
      _ = (a : G) * (((t * (a : G) * t⁻¹) * b) * (t * (b : G) * t⁻¹)) := by rw [h2]
      _ = (↑a * (t * ↑a * t⁻¹)) * (↑b * (t * ↑b * t⁻¹)) := by group

theorem diagHom_apply {G : Type*} [Group G] {K₁ K₂ : Subgroup G} {t : G}
    {hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a} {ht : ∀ k ∈ K₁, t * k * t⁻¹ ∈ K₂} (k : K₁) :
    diagHom K₁ K₂ t hc ht k = (k : G) * (t * (k : G) * t⁻¹) := rfl

theorem diagHom_ker_map {G : Type*} [Group G] {K₁ K₂ : Subgroup G} {t z : G}
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (ht : ∀ k ∈ K₁, t * k * t⁻¹ ∈ K₂)
    (hz2 : z * z = 1) (hzt : t * z * t⁻¹ = z) (hKz : K₁ ⊓ K₂ = zpowers z) :
    (diagHom K₁ K₂ t hc ht).ker.map K₁.subtype = zpowers z := by
  set φ := diagHom K₁ K₂ t hc ht with hφ
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : k ∈ φ.ker := hk
    rw [MonoidHom.mem_ker, hφ, diagHom_apply] at hk'
    have h1 : t * (k : G) * t⁻¹ = (k : G)⁻¹ := by
      have : (k : G) * (t * (k : G) * t⁻¹) = 1 := hk'
      exact eq_inv_of_mul_eq_one_right this
    have h2 : (k : G)⁻¹ ∈ K₂ := h1 ▸ ht k k.2
    have h3 : (k : G) ∈ K₁ ⊓ K₂ := ⟨k.2, by simpa using K₂.inv_mem h2⟩
    rw [hKz] at h3
    exact h3
  · intro hx
    have hxK : x ∈ K₁ ⊓ K₂ := by rw [hKz]; exact hx
    refine ⟨⟨x, hxK.1⟩, ?_, rfl⟩
    show (⟨x, hxK.1⟩ : K₁) ∈ φ.ker
    rw [MonoidHom.mem_ker, hφ, diagHom_apply]
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hx
    have : t * z ^ j * t⁻¹ = z ^ j := by rw [← conj_zpow, hzt]
    show z ^ j * (t * z ^ j * t⁻¹) = 1
    rw [this]
    calc z ^ j * z ^ j = (z * z) ^ j := ((Commute.refl z).mul_zpow j).symm
      _ = 1 := by rw [hz2, one_zpow]

theorem diagHom_card {G : Type*} [Group G] [Finite G] {K₁ K₂ : Subgroup G} {t z : G}
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (ht : ∀ k ∈ K₁, t * k * t⁻¹ ∈ K₂)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzt : t * z * t⁻¹ = z) (hKz : K₁ ⊓ K₂ = zpowers z) :
    Nat.card (diagHom K₁ K₂ t hc ht).range * 2 = Nat.card K₁ := by
  set φ := diagHom K₁ K₂ t hc ht with hφ
  have hker := diagHom_ker_map hc ht hz2 hzt hKz
  have hord : orderOf z = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hcardker : Nat.card φ.ker = 2 := by
    have h1 : Nat.card φ.ker = Nat.card (φ.ker.map K₁.subtype) :=
      Nat.card_congr (Subgroup.equivMapOfInjective φ.ker K₁.subtype K₁.subtype_injective).toEquiv
    rw [hker, Nat.card_zpowers, hord] at h1
    exact h1
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hcardker] at h1
  omega

theorem diagHom_range_equiv {G : Type*} [Group G] {K₁ K₂ : Subgroup G} {t z : G}
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (ht : ∀ k ∈ K₁, t * k * t⁻¹ ∈ K₂)
    (hz2 : z * z = 1) (hzt : t * z * t⁻¹ = z) (hKz : K₁ ⊓ K₂ = zpowers z)
    (hZ : (center ↥K₁).map K₁.subtype = zpowers z) :
    Nonempty (↥K₁ ⧸ center ↥K₁ ≃* ↥(diagHom K₁ K₂ t hc ht).range) := by
  set φ := diagHom K₁ K₂ t hc ht with hφ
  have hker : φ.ker = center ↥K₁ := by
    apply Subgroup.map_injective K₁.subtype_injective
    rw [hZ]
    exact diagHom_ker_map hc ht hz2 hzt hKz
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange φ)⟩

theorem diagHom_range_simple {G : Type*} [Group G] {K₁ K₂ : Subgroup G} {t z : G}
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (ht : ∀ k ∈ K₁, t * k * t⁻¹ ∈ K₂)
    (hz2 : z * z = 1) (hzt : t * z * t⁻¹ = z) (hKz : K₁ ⊓ K₂ = zpowers z)
    (hZ : (center ↥K₁).map K₁.subtype = zpowers z)
    (hs : IsSimpleGroup (↥K₁ ⧸ center ↥K₁)) :
    IsSimpleGroup ↥(diagHom K₁ K₂ t hc ht).range := by
  obtain ⟨e⟩ := diagHom_range_equiv hc ht hz2 hzt hKz hZ
  exact (MulEquiv.isSimpleGroup_congr e).mp hs

theorem perfect_no_index_two {G : Type*} [Group G] [Finite G] {J D : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (hDJ : D ≤ J) (hcard : Nat.card D * 2 = Nat.card J) : False := by
  set D' : Subgroup J := D.subgroupOf J with hD'
  have hidx : D'.index = 2 := by
    have h1 : Nat.card J = Nat.card D' * D'.index := (Subgroup.card_mul_index D').symm
    have h2 : Nat.card D' = Nat.card D := by
      rw [hD']
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDJ).toEquiv
    rw [h1, h2] at hcard
    have hpos : 0 < Nat.card D := Nat.card_pos
    nlinarith
  have hnorm : D'.Normal := Subgroup.normal_of_index_eq_two hidx
  have hq : Nat.card (J ⧸ D') = 2 := by rw [← Subgroup.index]; exact hidx
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (J ⧸ D') := isCyclic_of_prime_card (p := 2) hq
  have hc : ∀ a b : J ⧸ D', a * b = b * a := fun a b =>
    (IsCyclic.isMulCommutative (α := J ⧸ D')).is_comm.comm a b
  have hcomm : commutator J ≤ D' := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr ?_
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff]
    rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    calc (a : J ⧸ D') * b * (a : J ⧸ D')⁻¹ * (b : J ⧸ D')⁻¹
        = (b * a) * (a : J ⧸ D')⁻¹ * (b : J ⧸ D')⁻¹ := by rw [hc a b]
      _ = 1 := by group
  have h1 : (commutator J).map J.subtype = ⁅J, J⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have h2 : D'.map J.subtype = D := by
    rw [hD', Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hDJ
  have h3 : J ≤ D := by
    rw [← hJ, ← h1, ← h2]
    exact Subgroup.map_mono hcomm
  have h4 : D = J := le_antisymm hDJ h3
  rw [h4] at hcard
  have hpos : 0 < Nat.card J := Nat.card_pos
  omega

theorem diag_surj {G : Type*} [Group G] [Finite G] {J₁ J₂ D : Subgroup G}
    (hD : D ≤ J₁ ⊔ J₂) (hDJ₂ : D ⊓ J₂ = ⊥)
    (hcard : Nat.card D * Nat.card J₂ = Nat.card ↥(J₁ ⊔ J₂)) :
    ∀ j ∈ J₁ ⊔ J₂, ∃ i ∈ D, ∃ b ∈ J₂, j = i * b := by
  have hJ₂ : J₂ ≤ J₁ ⊔ J₂ := le_sup_right
  let f : D × J₂ → ↥(J₁ ⊔ J₂) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), (J₁ ⊔ J₂).mul_mem (hD p.1.2) (hJ₂ p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨i, hi⟩, ⟨b, hb⟩⟩ ⟨⟨i', hi'⟩, ⟨b', hb'⟩⟩ h
    have h' : i * b = i' * b' := congrArg Subtype.val h
    have hmem : i'⁻¹ * i ∈ D ⊓ J₂ := by
      refine ⟨D.mul_mem (D.inv_mem hi') hi, ?_⟩
      have : i'⁻¹ * i = b' * b⁻¹ := by
        calc i'⁻¹ * i = i'⁻¹ * (i * b) * b⁻¹ := by group
          _ = i'⁻¹ * (i' * b') * b⁻¹ := by rw [h']
          _ = b' * b⁻¹ := by group
      rw [this]
      exact J₂.mul_mem hb' (J₂.inv_mem hb)
    rw [hDJ₂, Subgroup.mem_bot] at hmem
    have hii : i = i' := by
      have := inv_mul_eq_one.mp hmem
      exact this.symm
    subst hii
    have hbb : b = b' := mul_left_cancel h'
    subst hbb
    rfl
  have hbij : Function.Bijective f := by
    refine (Function.Injective.bijective_of_nat_card_le hinj ?_)
    rw [Nat.card_prod, hcard]
  intro j hj
  obtain ⟨⟨i, b⟩, hib⟩ := hbij.2 ⟨j, hj⟩
  refine ⟨i, i.2, b, b.2, ?_⟩
  exact (congrArg Subtype.val hib).symm

theorem odd_no_swap {G : Type*} [Group G] {K₁ K₂ : Subgroup G} {c : G} (hodd : Odd (orderOf c))
    (h1 : ∀ a ∈ K₁, c * a * c⁻¹ ∈ K₂) (h2 : ∀ a ∈ K₂, c * a * c⁻¹ ∈ K₁) :
    ∀ a ∈ K₁, a ∈ K₂ := by
  obtain ⟨m, hm⟩ := hodd
  have hc : c ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one c
  have ev : ∀ k : ℕ, (∀ a ∈ K₁, c ^ (2 * k) * a * (c ^ (2 * k))⁻¹ ∈ K₁) ∧
      (∀ a ∈ K₂, c ^ (2 * k) * a * (c ^ (2 * k))⁻¹ ∈ K₂) := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · have e : c ^ (2 * (n + 1)) * a * (c ^ (2 * (n + 1)))⁻¹ =
            c * (c * (c ^ (2 * n) * a * (c ^ (2 * n))⁻¹) * c⁻¹) * c⁻¹ := by
          rw [show 2 * (n + 1) = 1 + 1 + 2 * n by ring, pow_add, pow_add]; group
        rw [e]
        exact h2 _ (h1 _ (ih.1 a ha))
      · have e : c ^ (2 * (n + 1)) * a * (c ^ (2 * (n + 1)))⁻¹ =
            c * (c * (c ^ (2 * n) * a * (c ^ (2 * n))⁻¹) * c⁻¹) * c⁻¹ := by
          rw [show 2 * (n + 1) = 1 + 1 + 2 * n by ring, pow_add, pow_add]; group
        rw [e]
        exact h1 _ (h2 _ (ih.2 a ha))
  intro a ha
  have h3 := h1 _ ((ev m).1 a ha)
  have e : c * (c ^ (2 * m) * a * (c ^ (2 * m))⁻¹) * c⁻¹ = a := by
    have : c ^ (2 * m + 1) = c * c ^ (2 * m) := by rw [pow_succ']
    calc c * (c ^ (2 * m) * a * (c ^ (2 * m))⁻¹) * c⁻¹
        = (c * c ^ (2 * m)) * a * (c * c ^ (2 * m))⁻¹ := by group
      _ = c ^ (2 * m + 1) * a * (c ^ (2 * m + 1))⁻¹ := by rw [this]
      _ = a := by rw [hc]; group
  rw [e] at h3
  exact h3


theorem diag_setup {G : Type*} [Group G] [Finite G] {z t g : G} {K₁ K₂ : Subgroup G}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (htz : t ≠ z) (hzt : z * t = t * z)
    (hg : g⁻¹ * z * g = t)
    (hK₁p : ⁅K₁, K₁⁆ = K₁) (hK₂p : ⁅K₂, K₂⁆ = K₂)
    (hKc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hKz : K₁ ⊓ K₂ = zpowers z) (hKcard : Nat.card K₁ = Nat.card K₂)
    (hKsup : Nat.card ↥(K₁ ⊔ K₂) * 2 = Nat.card K₁ * Nat.card K₂)
    (hts₁ : ∀ k ∈ K₁, t * k * t⁻¹ ∈ K₂)
    (hZ : (center ↥K₁).map K₁.subtype = zpowers z)
    (hKs : IsSimpleGroup (↥K₁ ⧸ center ↥K₁))
    (hDJ : (diagHom K₁ K₂ t hKc hts₁).range ≤ cj K₁ g ⊔ cj K₂ g)
    (hCK : ∀ s : G, s * s = 1 → s * z = z * s → (∀ k ∈ K₁ ⊔ K₂, s * k = k * s) →
      s = 1 ∨ s = z) :
    (∀ x : G, (∀ i ∈ (diagHom K₁ K₂ t hKc hts₁).range, x * i * x⁻¹ = i) →
      (∀ a ∈ cj K₁ g, x * a * x⁻¹ ∈ cj K₁ g) → (∀ a ∈ cj K₂ g, x * a * x⁻¹ ∈ cj K₂ g) →
      (∀ j ∈ cj K₁ g, x * j * x⁻¹ = j) ∧ (∀ j ∈ cj K₂ g, x * j * x⁻¹ = j)) ∧
    ¬ (cj K₁ g ⊔ cj K₂ g ≤ centralizer ({z} : Set G)) := by
  set D := (diagHom K₁ K₂ t hKc hts₁).range with hD
  set J₁ := cj K₁ g with hJ₁
  set J₂ := cj K₂ g with hJ₂
  have hz1' : z ∈ K₁ ⊓ K₂ := by rw [hKz]; exact mem_zpowers z
  have htzt : t * z * t⁻¹ = z := by
    have : z * t = t * z := hzt
    calc t * z * t⁻¹ = z * t * t⁻¹ := by rw [this]
      _ = z := by group
  have hDcard : Nat.card D * 2 = Nat.card K₁ := diagHom_card hKc hts₁ hz2 hz1 htzt hKz
  have hDsimple : IsSimpleGroup ↥D := diagHom_range_simple hKc hts₁ hz2 htzt hKz hZ hKs
  have hJ₁p : ⁅J₁, J₁⁆ = J₁ := by rw [hJ₁, cj_commutator, hK₁p]
  have hJ₂p : ⁅J₂, J₂⁆ = J₂ := by rw [hJ₂, cj_commutator, hK₂p]
  have hJc : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := by
    intro a ha b hb
    have := hKc _ (mem_cj.mp ha) _ (mem_cj.mp hb)
    have e : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := this
        _ = g * (b * a) * g⁻¹ := by group
    simpa using e
  have hJ₁card : Nat.card J₁ = Nat.card K₁ := cj_card K₁ g
  have hJ₂card : Nat.card J₂ = Nat.card K₂ := cj_card K₂ g
  have hJsup : Nat.card ↥(J₁ ⊔ J₂) = Nat.card ↥(K₁ ⊔ K₂) := by
    rw [hJ₁, hJ₂, ← cj_sup]; exact cj_card _ g
  have hJ₁N : J₁ ⊔ J₂ ≤ normalizer (J₁ : Set G) := by
    refine sup_le (Subgroup.le_normalizer : J₁ ≤ normalizer (J₁ : Set G)) (fun a ha => ?_)
    have : a ∈ centralizer (J₁ : Set G) := by
      rw [mem_centralizer_iff]; intro h hh; exact hJc h hh a ha
    exact Subgroup.centralizer_le_normalizer (J₁ : Set G) this
  have hJ₂N : J₁ ⊔ J₂ ≤ normalizer (J₂ : Set G) := by
    refine sup_le (fun a ha => ?_) (Subgroup.le_normalizer : J₂ ≤ normalizer (J₂ : Set G))
    have : a ∈ centralizer (J₂ : Set G) := by
      rw [mem_centralizer_iff]; intro h hh; exact (hJc a ha h hh).symm
    exact Subgroup.centralizer_le_normalizer (J₂ : Set G) this
  have hDinf : ∀ {J J' : Subgroup G}, ⁅J, J⁆ = J → Nat.card J = Nat.card K₁ →
      D ≤ J ⊔ J' → J ⊔ J' ≤ normalizer (J : Set G) → D ⊓ J = ⊥ := by
    intro J J' hJp hJcard hDle hJN
    have hnorm : ((D ⊓ J).subgroupOf D).Normal := by
      refine ⟨fun n hn d => ?_⟩
      have hdn : (d : G) ∈ normalizer (J : Set G) := hJN (hDle d.2)
      have hn' : (n : G) ∈ D ⊓ J := hn
      refine ⟨D.mul_mem (D.mul_mem d.2 n.2) (D.inv_mem d.2), ?_⟩
      have := (mem_normalizer_iff.mp hdn (n : G)).mp hn'.2
      exact this
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exact (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le inf_le_left
    · exfalso
      have hDJ' : D ≤ J := by
        have := Subgroup.subgroupOf_eq_top.mp h
        exact this.trans inf_le_right
      exact perfect_no_index_two hJp hDJ' (by rw [hJcard]; exact hDcard)
  have hDle₁ : D ≤ J₁ ⊔ J₂ := hDJ
  have hDle₂ : D ≤ J₂ ⊔ J₁ := by rw [sup_comm]; exact hDJ
  have hDJ₁ : D ⊓ J₁ = ⊥ := hDinf hJ₁p (hJ₁card) hDle₁ hJ₁N
  have hDJ₂ : D ⊓ J₂ = ⊥ := hDinf hJ₂p (hJ₂card.trans hKcard.symm) hDle₂
    (by rw [sup_comm]; exact hJ₂N)
  have hcard₂ : Nat.card D * Nat.card J₂ = Nat.card ↥(J₁ ⊔ J₂) := by
    rw [hJsup, hJ₂card, ← hKcard]
    have hpos : 0 < Nat.card D := Nat.card_pos
    nlinarith
  have hcard₁ : Nat.card D * Nat.card J₁ = Nat.card ↥(J₂ ⊔ J₁) := by
    rw [sup_comm, hJsup, hJ₁card]
    have hpos : 0 < Nat.card D := Nat.card_pos
    nlinarith
  have hI₁ : ∀ j ∈ J₁, ∃ i ∈ D, ∃ b ∈ J₂, j = i * b := fun j hj =>
    diag_surj hDle₁ hDJ₂ hcard₂ j ((le_sup_left : J₁ ≤ J₁ ⊔ J₂) hj)
  have hI₂ : ∀ j ∈ J₂, ∃ i ∈ D, ∃ b ∈ J₁, j = i * b := fun j hj =>
    diag_surj hDle₂ hDJ₁ hcard₁ j ((le_sup_left : J₂ ≤ J₂ ⊔ J₁) hj)
  refine ⟨fun x hxD hx₁ hx₂ => centralizes_of_diagonal hJ₁p hJ₂p hJc hI₁ hI₂ hx₁ hx₂ hxD, ?_⟩
  intro hJle
  set s := g * z * g⁻¹ with hs
  have hs2 : s * s = 1 := by
    rw [hs]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hcommK : ∀ k ∈ K₁ ⊔ K₂, s * k = k * s := by
    intro k hk
    have hsub : K₁ ⊔ K₂ ≤ centralizer ({s} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · have haJ : g⁻¹ * a * g ∈ J₁ := by
          rw [hJ₁, mem_cj]
          have : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
          rw [this]; exact ha
        have := mem_centralizer_singleton_iff.mp (hJle ((le_sup_left : J₁ ≤ J₁ ⊔ J₂) haJ))
        rw [mem_centralizer_singleton_iff]
        have e : (g⁻¹ * a * g) * z = z * (g⁻¹ * a * g) := this
        calc a * s = g * ((g⁻¹ * a * g) * z) * g⁻¹ := by rw [hs]; group
          _ = g * (z * (g⁻¹ * a * g)) * g⁻¹ := by rw [e]
          _ = s * a := by rw [hs]; group
      · have haJ : g⁻¹ * a * g ∈ J₂ := by
          rw [hJ₂, mem_cj]
          have : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
          rw [this]; exact ha
        have := mem_centralizer_singleton_iff.mp (hJle ((le_sup_right : J₂ ≤ J₁ ⊔ J₂) haJ))
        rw [mem_centralizer_singleton_iff]
        have e : (g⁻¹ * a * g) * z = z * (g⁻¹ * a * g) := this
        calc a * s = g * ((g⁻¹ * a * g) * z) * g⁻¹ := by rw [hs]; group
          _ = g * (z * (g⁻¹ * a * g)) * g⁻¹ := by rw [e]
          _ = s * a := by rw [hs]; group
    have := mem_centralizer_singleton_iff.mp (hsub hk)
    exact this.symm
  have hszc : s * z = z * s := hcommK z ((le_sup_left : K₁ ≤ K₁ ⊔ K₂) hz1'.1)
  rcases hCK s hs2 hszc hcommK with h1 | h1
  · have : z = 1 := by
      have : g⁻¹ * s * g = z := by rw [hs]; group
      rw [h1] at this; simpa using this.symm
    exact hz1 this
  · apply htz
    rw [← hg]
    have : g⁻¹ * s * g = g⁻¹ * z * g := by rw [h1]
    rw [← this, hs]; group

theorem lemma62a_math {G : Type*} [Group G] [Finite G] {z t g : G} {K₁ K₂ A₀ : Subgroup G}
    [IsCyclic A₀]
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (htz : t ≠ z) (hzt : z * t = t * z)
    (hg : g⁻¹ * z * g = t)
    (hK₁C : ∀ k ∈ K₁, k * z = z * k) (hK₂C : ∀ k ∈ K₂, k * z = z * k)
    (hK₁p : ⁅K₁, K₁⁆ = K₁) (hK₂p : ⁅K₂, K₂⁆ = K₂)
    (hKc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hKz : K₁ ⊓ K₂ = zpowers z) (hKcard : Nat.card K₁ = Nat.card K₂)
    (hKsup : Nat.card ↥(K₁ ⊔ K₂) * 2 = Nat.card K₁ * Nat.card K₂)
    (hts₁ : ∀ k ∈ K₁, t * k * t⁻¹ ∈ K₂)
    (hperm : ∀ c ∈ centralizer ({z} : Set G),
      ((∀ a ∈ K₁, c * a * c⁻¹ ∈ K₁) ∧ (∀ a ∈ K₂, c * a * c⁻¹ ∈ K₂)) ∨
      ((∀ a ∈ K₁, c * a * c⁻¹ ∈ K₂) ∧ (∀ a ∈ K₂, c * a * c⁻¹ ∈ K₁)))
    (hZ : (center ↥K₁).map K₁.subtype = zpowers z)
    (hKs : IsSimpleGroup (↥K₁ ⧸ center ↥K₁))
    (hA₀n : ∀ c ∈ centralizer ({z} : Set G), c ∈ normalizer (A₀ : Set G))
    (hA₀odd : ∀ a ∈ A₀, Odd (orderOf a))
    (hDJ : (diagHom K₁ K₂ t hKc hts₁).range ≤ cj K₁ g ⊔ cj K₂ g)
    (hmax : ∀ Y : Subgroup G, Y ≠ ⊥ → (∃ r : ℕ, r.Prime ∧ IsPGroup r Y) →
      centralizer ({z} : Set G) ≤ normalizer (Y : Set G) →
        normalizer (Y : Set G) = centralizer ({z} : Set G))
    (hCK : ∀ s : G, s * s = 1 → s * z = z * s → (∀ k ∈ K₁ ⊔ K₂, s * k = k * s) →
      s = 1 ∨ s = z) :
    ∀ a ∈ A₀, a * t = t * a → a = 1 := by
  obtain ⟨hdiag, hJC⟩ := diag_setup hz2 hz1 htz hzt hg hK₁p hK₂p hKc hKz hKcard hKsup hts₁ hZ hKs
    hDJ hCK
  set D := (diagHom K₁ K₂ t hKc hts₁).range with hD
  set J₁ := cj K₁ g with hJ₁
  set J₂ := cj K₂ g with hJ₂
  have hK₁N : K₁ ≤ normalizer (A₀ : Set G) := fun k hk =>
    hA₀n k (by rw [mem_centralizer_singleton_iff]; exact hK₁C k hk)
  have hK₂N : K₂ ≤ normalizer (A₀ : Set G) := fun k hk =>
    hA₀n k (by rw [mem_centralizer_singleton_iff]; exact hK₂C k hk)
  have hK₁cen := perfect_le_centralizer_of_cyclic hK₁p hK₁N
  have hK₂cen := perfect_le_centralizer_of_cyclic hK₂p hK₂N
  have hAK₁ : ∀ a ∈ A₀, ∀ k ∈ K₁, a * k = k * a := fun a ha k hk => by
    have := mem_centralizer_iff.mp (hK₁cen hk) a ha
    exact this
  have hAK₂ : ∀ a ∈ A₀, ∀ k ∈ K₂, a * k = k * a := fun a ha k hk => by
    have := mem_centralizer_iff.mp (hK₂cen hk) a ha
    exact this
  have hAI : ∀ a ∈ A₀, ∀ i ∈ D, a * i = i * a := by
    intro a ha i hi
    obtain ⟨k, rfl⟩ := hi
    show a * ((k : G) * (t * (k : G) * t⁻¹)) = ((k : G) * (t * (k : G) * t⁻¹)) * a
    have e1 := hAK₁ a ha k k.2
    have e2 := hAK₂ a ha _ (hts₁ k k.2)
    calc a * ((k : G) * (t * (k : G) * t⁻¹)) = (a * k) * (t * (k : G) * t⁻¹) := by group
      _ = (k * a) * (t * (k : G) * t⁻¹) := by rw [e1]
      _ = k * (a * (t * (k : G) * t⁻¹)) := by group
      _ = k * ((t * (k : G) * t⁻¹) * a) := by rw [e2]
      _ = _ := by group
  have hnorm : ∀ x ∈ A₀, x * t = t * x →
      (∀ a ∈ J₁, x * a * x⁻¹ ∈ J₁) ∧ (∀ a ∈ J₂, x * a * x⁻¹ ∈ J₂) := by
    intro x hx hxt
    set c := g * x * g⁻¹ with hc
    have hcz : c ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 : x * (g⁻¹ * z * g) = (g⁻¹ * z * g) * x := by rw [hg]; exact hxt
      have : z * c = c * z := by
        calc z * c = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by rw [hc]; group
          _ = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by rw [h1]
          _ = c * z := by rw [hc]; group
      exact this.symm
    have hcodd : Odd (orderOf c) := by
      have : orderOf c = orderOf x := by
        have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
        simpa [hc, MulAut.conj_apply] using this
      rw [this]; exact hA₀odd x hx
    have key : ∀ a : G, g * (x * a * x⁻¹) * g⁻¹ = c * (g * a * g⁻¹) * c⁻¹ := by
      intro a; rw [hc]; group
    rcases hperm c hcz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · rw [hJ₁, mem_cj, key]; exact h1 _ (mem_cj.mp ha)
      · rw [hJ₂, mem_cj, key]; exact h2 _ (mem_cj.mp ha)
    · exfalso
      have hle := odd_no_swap hcodd h1 h2
      have hz1' : z ∈ K₁ ⊓ K₂ := by rw [hKz]; exact mem_zpowers z
      have hK₁le : K₁ ≤ zpowers z := by
        intro a ha
        rw [← hKz]; exact ⟨ha, hle a ha⟩
      have hcomm : ⁅K₁, K₁⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro a ha b hb
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hK₁le ha)
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hK₁le hb)
        rw [Subgroup.mem_bot]
        have : z ^ i * z ^ j = z ^ j * z ^ i := (Commute.zpow_zpow_self z i j).eq
        simp [commutatorElement_def, this]
      have hz0 : z ∈ K₁ := hz1'.1
      rw [← hK₁p, hcomm, Subgroup.mem_bot] at hz0
      exact hz1 hz0
  exact lemma62a_core hA₀n hAI hdiag hnorm hmax hJC

end CFSG.GH74.GLS.LU.Local
