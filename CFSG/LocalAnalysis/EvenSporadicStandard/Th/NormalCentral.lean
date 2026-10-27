module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup
open scoped commutatorElement

theorem eq_bot_of_commutator_top_eq {H : Type*} [Group H] [Group.IsNilpotent H] {N : Subgroup H}
    (h : ⁅N, ⊤⁆ = N) : N = ⊥ := by
  have key : ∀ k, N ≤ (⊤ : Subgroup H).lowerCentralSeries k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      calc N = ⁅N, ⊤⁆ := h.symm
        _ ≤ ⁅(⊤ : Subgroup H).lowerCentralSeries k, ⊤⁆ := commutator_mono ih le_rfl
  obtain ⟨n, hn⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries (G := H)).1 inferInstance
  exact eq_bot_iff.2 (hn ▸ key n)

variable {G : Type*} [Group G] [Finite G]

theorem eq_bot_of_commutator_eq {P N : Subgroup G} (hP : IsPGroup 2 P) (hNP : N ≤ P)
    (h : ⁅N, P⁆ = N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  set N' : Subgroup ↥P := N.subgroupOf P with hN'
  have hmap : N'.map P.subtype = N := Subgroup.map_subgroupOf_eq_of_le hNP
  have htop : (⊤ : Subgroup ↥P).map P.subtype = P := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have h1 : ⁅N', ⊤⁆ = N' := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator, hmap, htop, h]
  have h2 := eq_bot_of_commutator_top_eq h1
  rw [← hmap, h2, Subgroup.map_bot]

theorem two_mul_card_commutator_le {P N : Subgroup G} (hP : IsPGroup 2 P) (hNP : N ≤ P)
    (hNn : ∀ s ∈ P, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (hN : N ≠ ⊥) :
    2 * Nat.card (⁅N, P⁆ : Subgroup G) ≤ Nat.card N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : ⁅N, P⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro n hn s hs
    have := N.mul_mem hn (hNn s hs n⁻¹ (N.inv_mem hn))
    simpa [commutatorElement_def, mul_assoc] using this
  have hne : ⁅N, P⁆ ≠ N := fun h => hN (eq_bot_of_commutator_eq hP hNP h)
  obtain ⟨a, ha⟩ := (hP.to_le hNP).exists_card_eq
  obtain ⟨b, hb⟩ := (hP.to_le (hle.trans hNP)).exists_card_eq
  have hlt : Nat.card (⁅N, P⁆ : Subgroup G) < Nat.card N :=
    lt_of_le_of_ne (Subgroup.card_le_of_le hle) fun h =>
      hne (Subgroup.eq_of_le_of_card_ge hle h.symm.le)
  rw [ha, hb] at hlt ⊢
  have hba : b < a := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  calc 2 * 2 ^ b = 2 ^ (b + 1) := by ring
    _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hba

omit [Finite G] in
theorem commutator_normalized {P N : Subgroup G}
    (hNn : ∀ s ∈ P, ∀ n ∈ N, s * n * s⁻¹ ∈ N) :
    ∀ s ∈ P, ∀ n ∈ ⁅N, P⁆, s * n * s⁻¹ ∈ ⁅N, P⁆ := by
  intro s hs n hn
  have : ∀ m ∈ ⁅N, P⁆, s * m * s⁻¹ ∈ ⁅N, P⁆ := by
    intro m hm
    refine Subgroup.closure_induction (p := fun m _ => s * m * s⁻¹ ∈ ⁅N, P⁆) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨a, ha, c, hc, rfl⟩
      have : s * ⁅a, c⁆ * s⁻¹ = ⁅s * a * s⁻¹, s * c * s⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact Subgroup.commutator_mem_commutator (hNn s hs a ha) (P.mul_mem (P.mul_mem hs hc)
        (P.inv_mem hs))
    · simp
    · intro x y _ _ hx hy
      have : s * (x * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
    · intro x _ hx
      have : s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx
  exact this n hn

@[expose] def iterComm (P : Subgroup G) : Subgroup G → ℕ → Subgroup G
  | N, 0 => N
  | N, k + 1 => iterComm P ⁅N, P⁆ k

theorem iterComm_eq_bot {P : Subgroup G} (hP : IsPGroup 2 P) :
    ∀ (k : ℕ) (N : Subgroup G), N ≤ P → (∀ s ∈ P, ∀ n ∈ N, s * n * s⁻¹ ∈ N) →
      Nat.card N ≤ 2 ^ k → iterComm P N k = ⊥ := by
  intro k
  induction k with
  | zero =>
    intro N _ _ hc
    exact Subgroup.eq_bot_of_card_le N (by simpa using hc)
  | succ k ih =>
    intro N hNP hNn hc
    have hle : ⁅N, P⁆ ≤ N := by
      rw [Subgroup.commutator_le]
      intro n hn s hs
      have := N.mul_mem hn (hNn s hs n⁻¹ (N.inv_mem hn))
      simpa [commutatorElement_def, mul_assoc] using this
    refine ih ⁅N, P⁆ (hle.trans hNP) (commutator_normalized hNn) ?_
    by_cases hN : N = ⊥
    · subst hN
      rw [Subgroup.commutator_bot_left]
      simpa using Nat.one_le_two_pow
    · have := two_mul_card_commutator_le hP hNP hNn hN
      rw [pow_succ] at hc
      omega

theorem commutator_four_eq_one {P N : Subgroup G} (hP : IsPGroup 2 P) (hNP : N ≤ P)
    (hNn : ∀ s ∈ P, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (hc : Nat.card N ≤ 16) {x : G} (hx : x ∈ N)
    {s₁ s₂ s₃ s₄ : G} (h₁ : s₁ ∈ P) (h₂ : s₂ ∈ P) (h₃ : s₃ ∈ P) (h₄ : s₄ ∈ P) :
    ⁅⁅⁅⁅x, s₁⁆, s₂⁆, s₃⁆, s₄⁆ = 1 := by
  have h := iterComm_eq_bot hP 4 N hNP hNn (by simpa using hc)
  have e : iterComm P N 4 = ⁅⁅⁅⁅N, P⁆, P⁆, P⁆, P⁆ := rfl
  rw [e] at h
  have : ⁅⁅⁅⁅x, s₁⁆, s₂⁆, s₃⁆, s₄⁆ ∈ ⁅⁅⁅⁅N, P⁆, P⁆, P⁆, P⁆ :=
    Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator
        (Subgroup.commutator_mem_commutator hx h₁) h₂) h₃) h₄
  rw [h] at this
  exact this

end CFSG.EvenSporadicStandard.ThStd
