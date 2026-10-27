module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_le_normal_card_eq {p : ℕ} [Fact p.Prime] {S Y : Subgroup G} [Finite S]
    (hS : IsPGroup p S) (hYS : Y ≤ S)
    (hYn : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) {k : ℕ}
    (hk : p ^ k ≤ Nat.card Y) :
    ∃ Y₀ : Subgroup G, Y₀ ≤ Y ∧ Nat.card Y₀ = p ^ k ∧
      (∀ s ∈ S, ∀ y ∈ Y₀, s * y * s⁻¹ ∈ Y₀) := by
  let Ys : Subgroup ↥S := Y.subgroupOf S
  have hYsN : Ys.Normal :=
    (Subgroup.normal_subgroupOf_iff hYS).2 fun y s hy hs => hYn s hs y hy
  have hYscard : Nat.card Ys = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYS).toEquiv
  obtain ⟨m, hm⟩ := (hS.to_subgroup Ys).exists_card_eq
  have hkm : k ≤ m := by
    have hle : p ^ k ≤ p ^ m := by rw [← hm, hYscard]; exact hk
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle
  letI : Fact (IsPGroup p ↥S) := ⟨hS⟩
  obtain ⟨K, hKN, hKY, hKcard⟩ :=
    CFSG.exists_normal_subgroup_card_pow_of_normal (p := p) (G := ↥S) (N := Ys)
      hYsN (k := m) hm k hkm
  refine ⟨K.map S.subtype, ?_, ?_, ?_⟩
  · calc K.map S.subtype ≤ Ys.map S.subtype := Subgroup.map_mono hKY
      _ = Y := Subgroup.map_subgroupOf_eq_of_le hYS
  · rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact hKcard
  · intro s hs y hy
    obtain ⟨k₀, hk₀, rfl⟩ := hy
    exact ⟨⟨s, hs⟩ * k₀ * ⟨s, hs⟩⁻¹, hKN.conj_mem k₀ hk₀ ⟨s, hs⟩, rfl⟩

@[expose] def iteratedCommutator (y : G) (s : ℕ → G) : ℕ → G
  | 0 => y
  | k + 1 => iteratedCommutator ⁅y, s 0⁆ (fun i => s (i + 1)) k

private theorem eq_bot_of_commutator_top_eq {H : Type*} [Group H] [Group.IsNilpotent H]
    {N : Subgroup H} (h : ⁅N, ⊤⁆ = N) : N = ⊥ := by
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

private theorem eq_bot_of_commutator_eq {p : ℕ} [Fact p.Prime] {P N : Subgroup G} [Finite P]
    (hP : IsPGroup p P) (hNP : N ≤ P) (h : ⁅N, P⁆ = N) : N = ⊥ := by
  have : Fact (Nat.Prime p) := inferInstance
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

private theorem commutator_normalized {P N : Subgroup G}
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

private theorem p_mul_card_commutator_le {p : ℕ} [Fact p.Prime] {P N : Subgroup G} [Finite P]
    (hP : IsPGroup p P) (hNP : N ≤ P)
    (hNn : ∀ s ∈ P, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (hN : N ≠ ⊥) :
    p * Nat.card (⁅N, P⁆ : Subgroup G) ≤ Nat.card N := by
  haveI : Finite N :=
    Finite.of_injective (Subgroup.inclusion hNP) (Subgroup.inclusion_injective hNP)
  have hle : ⁅N, P⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro n hn s hs
    have := N.mul_mem hn (hNn s hs n⁻¹ (N.inv_mem hn))
    simpa [commutatorElement_def, mul_assoc] using this
  have hne : ⁅N, P⁆ ≠ N := fun h => hN (eq_bot_of_commutator_eq hP hNP h)
  haveI : Finite (⁅N, P⁆ : Subgroup G) :=
    Finite.of_injective (Subgroup.inclusion (hle.trans hNP))
      (Subgroup.inclusion_injective (hle.trans hNP))
  obtain ⟨a, ha⟩ := (hP.to_le hNP).exists_card_eq
  obtain ⟨b, hb⟩ := (hP.to_le (hle.trans hNP)).exists_card_eq
  have hlt : Nat.card (⁅N, P⁆ : Subgroup G) < Nat.card N :=
    lt_of_le_of_ne (Subgroup.card_le_of_le hle) fun h =>
      hne (Subgroup.eq_of_le_of_card_ge hle h.symm.le)
  rw [ha, hb] at hlt ⊢
  have hba : b < a := (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).1 hlt
  calc p * p ^ b = p ^ (b + 1) := by ring
    _ ≤ p ^ a := Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le hba

theorem iteratedCommutator_eq_one {p : ℕ} [Fact p.Prime] {S Y : Subgroup G} [Finite S]
    (hS : IsPGroup p S) (hYS : Y ≤ S)
    (hYn : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) :
    ∀ (k : ℕ), Nat.card Y ≤ p ^ k → ∀ {y : G}, y ∈ Y → ∀ s : ℕ → G,
      (∀ i, s i ∈ S) → iteratedCommutator y s k = 1
  | 0, hc, y, hy, _s, _hs => by
    haveI : Finite Y :=
      Finite.of_injective (Subgroup.inclusion hYS) (Subgroup.inclusion_injective hYS)
    have hYbot : Y = ⊥ := Subgroup.eq_bot_of_card_le (H := Y) (by simpa using hc)
    rw [hYbot] at hy
    simpa [iteratedCommutator] using hy
  | k + 1, hc, y, hy, s, hs => by
    let N : Subgroup G := ⁅Y, S⁆
    have hNY : N ≤ Y := by
      rw [Subgroup.commutator_le]
      intro n hn t ht
      have := Y.mul_mem hn (hYn t ht n⁻¹ (Y.inv_mem hn))
      simpa [commutatorElement_def, mul_assoc] using this
    have hNS : N ≤ S := hNY.trans hYS
    have hNn : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N := commutator_normalized hYn
    have hNcard : Nat.card N ≤ p ^ k := by
      by_cases hYbot : Y = ⊥
      · have hNbot : N = ⊥ := le_bot_iff.1 (hYbot ▸ hNY)
        rw [hNbot, Subgroup.card_bot]
        exact Nat.one_le_pow k p (Fact.out : p.Prime).pos
      · have hmul : p * Nat.card N ≤ Nat.card Y := p_mul_card_commutator_le hS hYS hYn hYbot
        rw [pow_succ] at hc
        have hle : p * Nat.card N ≤ p * p ^ k := by
          calc p * Nat.card N ≤ Nat.card Y := hmul
            _ ≤ p ^ k * p := hc
            _ = p * p ^ k := by rw [mul_comm]
        exact Nat.le_of_mul_le_mul_left hle (Fact.out : p.Prime).pos
    have hmem : ⁅y, s 0⁆ ∈ N := Subgroup.commutator_mem_commutator hy (hs 0)
    change iteratedCommutator ⁅y, s 0⁆ (fun i => s (i + 1)) k = 1
    exact iteratedCommutator_eq_one hS hNS hNn k hNcard hmem
      (fun i => s (i + 1)) (fun i => hs (i + 1))

theorem commutator_four_eq_one_of_card_le {p : ℕ} [Fact p.Prime] {S Y : Subgroup G} [Finite S]
    (hS : IsPGroup p S) (hYS : Y ≤ S)
    (hYn : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y)
    (hc : Nat.card Y ≤ p ^ 4) :
    ∀ y ∈ Y, ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ s₃ ∈ S, ∀ s₄ ∈ S,
      ⁅⁅⁅⁅y, s₁⁆, s₂⁆, s₃⁆, s₄⁆ = 1 := by
  intro y hy s₁ h₁ s₂ h₂ s₃ h₃ s₄ h₄
  let s : ℕ → G := fun i => match i with
    | 0 => s₁
    | 1 => s₂
    | 2 => s₃
    | _ => s₄
  have hs : ∀ i, s i ∈ S := by
    rintro (_ | _ | _ | i) <;> simp [s, h₁, h₂, h₃, h₄]
  have h := iteratedCommutator_eq_one hS hYS hYn 4 (by simpa using hc) hy s hs
  have hcomp : iteratedCommutator y s 4 = ⁅⁅⁅⁅y, s₁⁆, s₂⁆, s₃⁆, s₄⁆ := by
    rfl
  rwa [hcomp] at h

end CFSG.GroupTheory
