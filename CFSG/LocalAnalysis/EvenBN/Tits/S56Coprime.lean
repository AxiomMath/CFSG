module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.S56

open Subgroup
open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

private theorem conj_mem_of_gens (P X : Subgroup Γ) (g : Γ)
    (h : ∀ a ∈ P, ∀ x ∈ X, g * ⁅a, x⁆ * g⁻¹ ∈ ⁅P, X⁆) {q : Γ} (hq : q ∈ ⁅P, X⁆) :
    g * q * g⁻¹ ∈ ⁅P, X⁆ := by
  rw [Subgroup.commutator_def] at hq
  induction hq using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    exact h a ha x hx
  | one => simpa using one_mem _
  | mul a b _ _ iha ihb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact mul_mem iha ihb
  | inv a _ iha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem iha

private theorem conj_mem_of_mem_left (P X : Subgroup Γ) {g q : Γ} (hg : g ∈ P)
    (hq : q ∈ ⁅P, X⁆) : g * q * g⁻¹ ∈ ⁅P, X⁆ := by
  refine conj_mem_of_gens P X g (fun a ha x hx => ?_) hq
  have e : g * ⁅a, x⁆ * g⁻¹ = ⁅g * a, x⁆ * ⁅g, x⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (commutator_mem_commutator (P.mul_mem hg ha) hx)
    (inv_mem (commutator_mem_commutator hg hx))

private theorem conj_mem_of_mem_right (P X : Subgroup Γ) {g q : Γ} (hg : g ∈ X)
    (hq : q ∈ ⁅P, X⁆) : g * q * g⁻¹ ∈ ⁅P, X⁆ := by
  refine conj_mem_of_gens P X g (fun a ha x hx => ?_) hq
  have e : g * ⁅a, x⁆ * g⁻¹ = ⁅a, g⁆⁻¹ * ⁅a, g * x⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (inv_mem (commutator_mem_commutator ha hg))
    (commutator_mem_commutator ha (X.mul_mem hg hx))

private theorem le_normalizer_of_conj_mem {H K : Subgroup Γ}
    (h : ∀ g ∈ K, ∀ q ∈ H, g * q * g⁻¹ ∈ H) : K ≤ normalizer (H : Set Γ) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro q
  refine ⟨h g hg q, fun hq => ?_⟩
  have h' := h g⁻¹ (K.inv_mem hg) _ hq
  have e : g⁻¹ * (g * q * g⁻¹) * g⁻¹⁻¹ = q := by group
  rwa [e] at h'

theorem commutator_normalized (P X : Subgroup Γ) : P ⊔ X ≤ normalizer (⁅P, X⁆ : Subgroup Γ) :=
  sup_le
    (le_normalizer_of_conj_mem fun _ hg _ hq => conj_mem_of_mem_left P X hg hq)
    (le_normalizer_of_conj_mem fun _ hg _ hq => conj_mem_of_mem_right P X hg hq)

private theorem commutator_le_of_le_normalizer {P X : Subgroup Γ}
    (hXP : X ≤ normalizer (P : Set Γ)) : ⁅P, X⁆ ≤ P := by
  rw [commutator_le]
  intro a ha x hx
  have h1 : x * a⁻¹ * x⁻¹ ∈ P := ((mem_normalizer_iff.1 (hXP hx)) a⁻¹).1 (P.inv_mem ha)
  have e : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact P.mul_mem ha h1

private theorem exists_centralized_mem_rightCoset [Finite Γ] {p r : ℕ} [Fact p.Prime]
    [Fact r.Prime] (hpr : p ≠ r) {Y X : Subgroup Γ} {q : Γ} (hY : IsPGroup p Y)
    (hX : IsPGroup r X) (hstab : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y)
    (hcomm : ∀ x ∈ X, x * q * x⁻¹ * q⁻¹ ∈ Y) :
    ∃ k : Γ, k * q⁻¹ ∈ Y ∧ ∀ x ∈ X, x * k * x⁻¹ = k := by
  let S : Set Γ := {z | z * q⁻¹ ∈ Y}
  have hS : ∀ x ∈ X, ∀ z ∈ S, x * z * x⁻¹ ∈ S := by
    intro x hx z hz
    show x * z * x⁻¹ * q⁻¹ ∈ Y
    have e : x * z * x⁻¹ * q⁻¹ = (x * (z * q⁻¹) * x⁻¹) * (x * q * x⁻¹ * q⁻¹) := by group
    rw [e]
    exact Y.mul_mem (hstab x hx _ hz) (hcomm x hx)
  letI : MulAction X S :=
    { smul := fun x z => ⟨x * z * x⁻¹, hS x x.2 z z.2⟩
      one_smul := fun z => Subtype.ext (by
        change (1 : X).1 * z.1 * ((1 : X).1)⁻¹ = z.1
        simp)
      mul_smul := fun x y z => Subtype.ext (by
        change (x * y : X).1 * z.1 * ((x * y : X).1)⁻¹ = x.1 * (y.1 * z.1 * y.1⁻¹) * x.1⁻¹
        simp [mul_assoc]) }
  have hcard : Nat.card S = Nat.card Y :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulRight q⁻¹) fun z => Iff.rfl)
  have hndvd : ¬ r ∣ Nat.card S := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hY
    rw [hcard, hn]
    intro hdvd
    exact hpr ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) (Fact.out : p.Prime)).1
      ((Fact.out : r.Prime).dvd_of_dvd_pow hdvd)).symm
  obtain ⟨⟨k, hk⟩, hfix⟩ := hX.nonempty_fixed_point_of_prime_not_dvd_card S hndvd
  refine ⟨k, hk, fun x hx => ?_⟩
  exact congrArg Subtype.val (hfix ⟨x, hx⟩)

theorem coprime_decomp_mem [Finite Γ] {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    {P X : Subgroup Γ} (hP : IsPGroup p P) (hX : IsPGroup r X)
    (hXP : X ≤ normalizer (P : Set Γ)) {q : Γ} (hq : q ∈ P) :
    ∃ c ∈ ⁅P, X⁆, ∃ k ∈ P ⊓ centralizer (X : Set Γ), q = c * k := by
  have hYP : ⁅P, X⁆ ≤ P := commutator_le_of_le_normalizer hXP
  have hY : IsPGroup p (⁅P, X⁆ : Subgroup Γ) := hP.to_le hYP
  obtain ⟨k, hk, hfix⟩ := exists_centralized_mem_rightCoset hpr hY hX
    (fun x hx y hy => conj_mem_of_mem_right P X hx hy)
    (fun x hx => by
      have h : ⁅x, q⁆ ∈ ⁅X, P⁆ := commutator_mem_commutator hx hq
      rw [commutator_comm] at h
      simpa [commutatorElement_def] using h)
  refine ⟨(k * q⁻¹)⁻¹, inv_mem hk, k, mem_inf.2 ⟨?_, ?_⟩, by group⟩
  · have h : k = (k * q⁻¹) * q := by group
    rw [h]
    exact P.mul_mem (hYP hk) hq
  · rw [mem_centralizer_iff]
    intro x hx
    exact mul_inv_eq_iff_eq_mul.1 (hfix x hx)

end CFSG.LocalAnalysis.EvenBN.Tits.S56
