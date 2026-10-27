module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Y
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Alg

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup

variable {Γ : Type*} [Group Γ]

namespace IsF20

variable {U : Subgroup Γ} {x v : Γ}

theorem subgroup_eq_bot_or_top [Finite Γ] (h : IsF20 U x v) {D : Subgroup Γ} (hDU : D ≤ U)
    (hx : x ∈ normalizer (D : Set Γ)) : D = ⊥ ∨ D = U := by
  have hmod : Nat.card D ≡ Nat.card (⊥ : Subgroup Γ) [MOD 5] :=
    CFSG.LocalAnalysis.EvenBN.Tits.S56.card_modEq_of_centralizer_le h.orderOf_x bot_le hDU
      (by
        rw [mem_normalizer_iff]
        intro g
        simp [Subgroup.mem_bot]) hx
      (fun c hc hxc => by
        rw [Subgroup.mem_bot]
        exact h.fpf c hc (by rw [hxc]; group))
  rw [Subgroup.card_bot] at hmod
  have hdvd : Nat.card D ∣ 2 ^ 4 := by
    have := Subgroup.card_dvd_of_le hDU
    rw [h.card] at this
    simpa using this
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hk] at hmod
  have hk' : k = 0 ∨ k = 4 := by
    interval_cases k <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hmod; decide)
  rcases hk' with rfl | rfl
  · left
    exact Subgroup.eq_bot_of_card_eq D (by rw [hk]; norm_num)
  · right
    exact Subgroup.eq_of_le_of_card_ge hDU (by rw [h.card, hk]; norm_num)

theorem centralizes_of_isPGroup_two [Finite Γ] (h : IsF20 U x v) {P : Subgroup Γ} (hP : IsPGroup 2 P)
    (hPU : P ≤ normalizer (U : Set Γ)) (hxP : ∀ p ∈ P, x * p * x⁻¹ ∈ P) :
    ∀ p ∈ P, ∀ u ∈ U, p * u = u * p := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite U := Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)
  letI : MulAction P U :=
    { smul := fun p u => ⟨(p : Γ) * u * (p : Γ)⁻¹, (mem_normalizer_iff.1 (hPU p.2) u).1 u.2⟩
      one_smul := fun u => Subtype.ext (by
        change (1 : P).1 * u.1 * ((1 : P).1)⁻¹ = u.1
        simp)
      mul_smul := fun p q u => Subtype.ext (by
        change (p * q : P).1 * u.1 * ((p * q : P).1)⁻¹ = p.1 * (q.1 * u.1 * q.1⁻¹) * p.1⁻¹
        simp [mul_assoc]) }
  set C : Subgroup Γ := U ⊓ centralizer (P : Set Γ) with hCdef
  have hC : ∀ c, c ∈ C ↔ c ∈ U ∧ ∀ p ∈ P, p * c = c * p := by
    intro c
    rw [hCdef, Subgroup.mem_inf, mem_centralizer_iff]
    exact ⟨fun ⟨hu, hc⟩ => ⟨hu, hc⟩, fun ⟨hu, hc⟩ => ⟨hu, hc⟩⟩
  have hxpow : ∀ n : ℕ, ∀ p ∈ P, x ^ n * p * (x ^ n)⁻¹ ∈ P := by
    intro n
    induction n with
    | zero => intro p hp; simpa using hp
    | succ n ih =>
      intro p hp
      have := hxP _ (ih p hp)
      have e : x * (x ^ n * p * (x ^ n)⁻¹) * x⁻¹ = x ^ (n + 1) * p * (x ^ (n + 1))⁻¹ := by group
      rwa [e] at this
  have hxinv : ∀ p ∈ P, x⁻¹ * p * x ∈ P := by
    intro p hp
    have := hxpow 4 p hp
    rwa [← h.inv_eq_pow_four, inv_inv] at this
  have hconj : ∀ y : Γ, (∀ p ∈ P, y⁻¹ * p * y ∈ P) → y ∈ normalizer (U : Set Γ) →
      ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
    intro y hy hyU c hc
    obtain ⟨hcU, hcP⟩ := (hC c).1 hc
    rw [hC]
    refine ⟨(mem_normalizer_iff.1 hyU c).1 hcU, fun p hp => ?_⟩
    have h1 := hcP (y⁻¹ * p * y) (hy p hp)
    calc p * (y * c * y⁻¹) = y * ((y⁻¹ * p * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * p * y)) * y⁻¹ := by rw [h1]
      _ = (y * c * y⁻¹) * p := by group
  have hxC : x ∈ normalizer (C : Set Γ) := by
    rw [mem_normalizer_iff]
    intro g
    constructor
    · exact hconj x hxinv h.x_norm g
    · intro hg
      have := hconj x⁻¹ (fun p hp => by simpa using hxP p hp) (inv_mem h.x_norm) _ hg
      simpa [mul_assoc] using this
  have hCbot : C ≠ ⊥ := by
    have hdvd : 2 ∣ Nat.card U := by rw [h.card]; norm_num
    have h1 : (1 : U) ∈ MulAction.fixedPoints P U := by
      rw [MulAction.mem_fixedPoints]
      intro p
      exact Subtype.ext (by
        change (p : Γ) * (1 : U) * (p : Γ)⁻¹ = 1
        simp)
    obtain ⟨b, hb, hb1⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hdvd h1
    rw [MulAction.mem_fixedPoints] at hb
    have hbC : (b : Γ) ∈ C := by
      rw [hC]
      refine ⟨b.2, fun p hp => ?_⟩
      have := congrArg Subtype.val (hb ⟨p, hp⟩)
      change (p : Γ) * b * (p : Γ)⁻¹ = b at this
      calc p * (b : Γ) = ((p : Γ) * b * (p : Γ)⁻¹) * p := by group
        _ = b * p := by rw [this]
    intro hbot
    apply hb1
    have : (b : Γ) = 1 := by
      have := hbC
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    exact Subtype.ext (by simpa using this.symm)
  rcases h.subgroup_eq_bot_or_top inf_le_left hxC with h1 | h1
  · exact absurd h1 hCbot
  · intro p hp u hu
    have hu' : u ∈ C := by
      show u ∈ U ⊓ centralizer (P : Set Γ)
      rw [h1]
      exact hu
    exact ((hC u).1 hu').2 p hp

end IsF20

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
