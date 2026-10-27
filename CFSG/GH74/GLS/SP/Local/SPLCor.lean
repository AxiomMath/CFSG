module

public import CFSG.GH74.GLS.Stage4.LocalCor97

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
open scoped Pointwise

variable {G : Type} [Group G]

structure Cor41 (p : ℕ) (H : Subgroup G) (r₁ r₂ : G) (U : Subgroup G) (root : ℤ → Subgroup G) :
    Prop where
  prime : p.Prime
  comm_H : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a
  conj_H₁ : ∀ h ∈ H, r₁ * h * r₁⁻¹ ∈ H
  conj_H₂ : ∀ h ∈ H, r₂ * h * r₂⁻¹ ∈ H
  sq₁ : r₁ * r₁ ∈ H
  sq₂ : r₂ * r₂ ∈ H
  pow : (r₁ * r₂) ^ 4 ∈ H
  H_pPrime : ∀ h ∈ H, ¬ p ∣ orderOf h
  U_pGroup : IsPGroup p U
  U_gen : U = ⨆ k ∈ Set.Icc (1 : ℤ) 4, root k
  ne_bot : ∀ i, IsRoot 4 i → root i ≠ ⊥
  invariant : ∀ i, IsRoot 4 i → ∀ h ∈ H, ∀ x ∈ root i, h * x * h⁻¹ ∈ root i
  act₁ : conjBy r₁⁻¹ (root 1) = root (-1) ∧ conjBy r₁⁻¹ (root (-1)) = root 1 ∧
    ∀ i : ℤ, 2 ≤ i → i ≤ 4 → conjBy r₁⁻¹ (root i) = root (6 - i) ∧
      conjBy r₁⁻¹ (root (-i)) = root (-(6 - i))
  act₂ : conjBy r₂⁻¹ (root 4) = root (-4) ∧ conjBy r₂⁻¹ (root (-4)) = root 4 ∧
    ∀ i : ℤ, 1 ≤ i → i ≤ 3 → conjBy r₂⁻¹ (root i) = root (4 - i) ∧
      conjBy r₂⁻¹ (root (-i)) = root (-(4 - i))
  opp : U ⊓ conjBy ((r₁ * r₂) ^ 2) U = ⊥
  L42 : ∀ Z : Subgroup G, Z ≤ U → (∀ h ∈ H, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z) →
    ∀ l : List ℤ, (l.Pairwise (· < ·) ∨ l.Pairwise (· > ·)) →
      (∀ i, i ∈ l ↔ (1 ≤ i ∧ i ≤ 4) ∧ root i ≤ Z) →
      (Z : Set G) = chainProd root l ∧ Nat.card Z = (l.map fun i => Nat.card (root i)).prod
  bruhat₁ : ∀ y ∈ root (-1), y ≠ 1 →
    y ∈ (root 1 : Set G) * (H : Set G) * {r₁} * (root 1 : Set G)
  bruhat₂ : ∀ y ∈ root (-4), y ≠ 1 →
    y ∈ (root 4 : Set G) * (H : Set G) * {r₂} * (root 4 : Set G)

@[expose] def ActsAs4 (root : ℤ → Subgroup G) (u : G) (σ : ℤ → ℤ) : Prop :=
  ∀ q : ℤ, ∀ x : G, x ∈ root (Rt 4 q) ↔ u * x * u⁻¹ ∈ root (Rt 4 (σ q))

theorem ActsAs4.mul {root : ℤ → Subgroup G} {u v : G} {σ τ : ℤ → ℤ} (hu : ActsAs4 root u σ)
    (hv : ActsAs4 root v τ) : ActsAs4 root (u * v) (fun q => σ (τ q)) := by
  intro q x
  rw [hv q x, hu (τ q) (v * x * v⁻¹)]
  have e : u * (v * x * v⁻¹) * u⁻¹ = u * v * x * (u * v)⁻¹ := by group
  rw [e]

theorem ActsAs4.congr {root : ℤ → Subgroup G} {u : G} {σ τ : ℤ → ℤ} (h : ActsAs4 root u σ)
    (hστ : ∀ q, σ q = τ q) : ActsAs4 root u τ := by
  intro q x
  rw [← hστ q]
  exact h q x

theorem ActsAs4.one {root : ℤ → Subgroup G} : ActsAs4 root (1 : G) (fun q => q) := by
  intro q x
  simp

theorem Rt4_val0 : Rt 4 0 = 1 := by decide
theorem Rt4_val1 : Rt 4 1 = 2 := by decide
theorem Rt4_val2 : Rt 4 2 = 3 := by decide
theorem Rt4_val3 : Rt 4 3 = 4 := by decide
theorem Rt4_val4 : Rt 4 4 = -1 := by decide
theorem Rt4_val5 : Rt 4 5 = -2 := by decide
theorem Rt4_val6 : Rt 4 6 = -3 := by decide
theorem Rt4_val7 : Rt 4 7 = -4 := by decide

theorem Rt4_emod (q : ℤ) : Rt 4 q = Rt 4 (q % 8) := Rt_congr (by simp)

theorem Rt4_of_lt {q : ℤ} (h0 : 0 ≤ q) (h1 : q ≤ 3) : Rt 4 q = q + 1 :=
  Rt_of_lt h0 (by push_cast; omega)

theorem Rt4_of_ge {q : ℤ} (h0 : 4 ≤ q) (h1 : q ≤ 7) : Rt 4 q = -(q - 3) := by
  rw [Rt_of_ge (by push_cast; omega) (by push_cast; omega)]
  push_cast
  ring

theorem Rt4_isRoot (q : ℤ) : IsRoot 4 (Rt 4 q) := Rt_isRoot (by norm_num) q

theorem Rt4_add8 (q : ℤ) : Rt 4 (q + 8) = Rt 4 q := by
  have := Rt_add_mul 4 q 1
  simpa using this

theorem actsAs4_r₁ {root : ℤ → Subgroup G} {r₁ : G}
    (h : conjBy r₁⁻¹ (root 1) = root (-1) ∧ conjBy r₁⁻¹ (root (-1)) = root 1 ∧
      ∀ i : ℤ, 2 ≤ i → i ≤ 4 → conjBy r₁⁻¹ (root i) = root (6 - i) ∧
        conjBy r₁⁻¹ (root (-i)) = root (-(6 - i))) :
    ActsAs4 root r₁ (fun q => 4 - q) := by
  obtain ⟨a1, a2, a3⟩ := h
  intro q x
  have hq : Rt 4 q = Rt 4 (q % 8) := Rt4_emod q
  have hq' : Rt 4 (4 - q) = Rt 4 ((4 - q % 8) % 8) := by
    rw [Rt4_emod (4 - q)]
    congr 1
    omega
  show x ∈ root (Rt 4 q) ↔ r₁ * x * r₁⁻¹ ∈ root (Rt 4 (4 - q))
  rw [hq, hq']
  have h0 := Int.emod_nonneg q (by norm_num : (8 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos q (by norm_num : (0 : ℤ) < 8)
  generalize q % 8 = v at *
  interval_cases v
  · norm_num [Rt4_val0, Rt4_val4]
    exact iff_of_conjBy a1 x
  · norm_num [Rt4_val1, Rt4_val3]
    exact iff_of_conjBy (a3 2 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt4_val2]
    exact iff_of_conjBy (a3 3 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt4_val3, Rt4_val1]
    exact iff_of_conjBy (a3 4 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt4_val4, Rt4_val0]
    exact iff_of_conjBy a2 x
  · norm_num [Rt4_val5, Rt4_val7]
    exact iff_of_conjBy (a3 2 (by norm_num) (by norm_num)).2 x
  · norm_num [Rt4_val6]
    exact iff_of_conjBy (a3 3 (by norm_num) (by norm_num)).2 x
  · norm_num [Rt4_val7, Rt4_val5]
    exact iff_of_conjBy (a3 4 (by norm_num) (by norm_num)).2 x

theorem actsAs4_r₂ {root : ℤ → Subgroup G} {r₂ : G}
    (h : conjBy r₂⁻¹ (root 4) = root (-4) ∧ conjBy r₂⁻¹ (root (-4)) = root 4 ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ 3 → conjBy r₂⁻¹ (root i) = root (4 - i) ∧
        conjBy r₂⁻¹ (root (-i)) = root (-(4 - i))) :
    ActsAs4 root r₂ (fun q => 2 - q) := by
  obtain ⟨b1, b2, b3⟩ := h
  intro q x
  have hq : Rt 4 q = Rt 4 (q % 8) := Rt4_emod q
  have hq' : Rt 4 (2 - q) = Rt 4 ((2 - q % 8) % 8) := by
    rw [Rt4_emod (2 - q)]
    congr 1
    omega
  show x ∈ root (Rt 4 q) ↔ r₂ * x * r₂⁻¹ ∈ root (Rt 4 (2 - q))
  rw [hq, hq']
  have h0 := Int.emod_nonneg q (by norm_num : (8 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos q (by norm_num : (0 : ℤ) < 8)
  generalize q % 8 = v at *
  interval_cases v
  · norm_num [Rt4_val0, Rt4_val2]
    exact iff_of_conjBy (b3 1 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt4_val1]
    exact iff_of_conjBy (b3 2 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt4_val2, Rt4_val0]
    exact iff_of_conjBy (b3 3 (by norm_num) (by norm_num)).1 x
  · norm_num [Rt4_val3, Rt4_val7]
    exact iff_of_conjBy b1 x
  · norm_num [Rt4_val4, Rt4_val6]
    exact iff_of_conjBy (b3 1 (by norm_num) (by norm_num)).2 x
  · norm_num [Rt4_val5]
    exact iff_of_conjBy (b3 2 (by norm_num) (by norm_num)).2 x
  · norm_num [Rt4_val6, Rt4_val4]
    exact iff_of_conjBy (b3 3 (by norm_num) (by norm_num)).2 x
  · norm_num [Rt4_val7, Rt4_val3]
    exact iff_of_conjBy b2 x

theorem actsAs4_rot {root : ℤ → Subgroup G} {r₁ r₂ : G} (h₁ : ActsAs4 root r₁ (fun q => 4 - q))
    (h₂ : ActsAs4 root r₂ (fun q => 2 - q)) (k : ℕ) :
    ActsAs4 root ((r₁ * r₂) ^ k) (fun q => q + 2 * (k : ℤ)) := by
  induction k with
  | zero =>
    simpa using (ActsAs4.one : ActsAs4 root (1 : G) (fun q => q))
  | succ k ih =>
    rw [pow_succ]
    refine (ih.mul (h₁.mul h₂)).congr (fun q => ?_)
    push_cast
    ring


namespace Cor41

variable {p : ℕ} {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G} {root : ℤ → Subgroup G}
  (D : Cor41 p H r₁ r₂ U root)

include D in
theorem actsAs₁ : ActsAs4 root r₁ (fun q => 4 - q) := actsAs4_r₁ D.act₁

include D in
theorem actsAs₂ : ActsAs4 root r₂ (fun q => 2 - q) := actsAs4_r₂ D.act₂

include D in
theorem root_le_U {k : ℤ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) : root k ≤ U := by
  rw [D.U_gen]
  exact le_iSup₂_of_le k ⟨hk1, hk4⟩ le_rfl

include D in
theorem pos_mod_le_three {q : ℤ} (hq : ∀ x ∈ root (Rt 4 q), x ∈ U) : q % 8 ≤ 3 := by
  by_contra hcon
  have hcon' : 4 ≤ q % 8 := by omega
  have h0 := Int.emod_nonneg q (by norm_num : (8 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos q (by norm_num : (0 : ℤ) < 8)
  have hw := actsAs4_rot D.actsAs₁ D.actsAs₂ 2
  have hbot : root (Rt 4 q) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy' : y ∈ root (Rt 4 (q % 8)) := by rwa [← Rt4_emod]
    have e : (r₁ * r₂) ^ 2 * (((r₁ * r₂) ^ 2)⁻¹ * y * (r₁ * r₂) ^ 2) * ((r₁ * r₂) ^ 2)⁻¹ = y := by
      group
    have hx : ((r₁ * r₂) ^ 2)⁻¹ * y * (r₁ * r₂) ^ 2 ∈ root (Rt 4 (q % 8 - 4)) := by
      rw [hw (q % 8 - 4), e]
      have : q % 8 - 4 + 2 * ((2 : ℕ) : ℤ) = q % 8 := by push_cast; ring
      show y ∈ root (Rt 4 (q % 8 - 4 + 2 * ((2 : ℕ) : ℤ)))
      rw [this]
      exact hy'
    have hxU : ((r₁ * r₂) ^ 2)⁻¹ * y * (r₁ * r₂) ^ 2 ∈ U := by
      refine D.root_le_U (k := Rt 4 (q % 8 - 4)) ?_ ?_ hx
      · rw [Rt4_of_lt (by omega) (by omega)]; omega
      · rw [Rt4_of_lt (by omega) (by omega)]; omega
    have hxc : ((r₁ * r₂) ^ 2)⁻¹ * y * (r₁ * r₂) ^ 2 ∈ conjBy ((r₁ * r₂) ^ 2) U := by
      rw [mem_conjBy_iff, e]
      exact hq y hy
    have hx1 : ((r₁ * r₂) ^ 2)⁻¹ * y * (r₁ * r₂) ^ 2 = 1 := by
      have : ((r₁ * r₂) ^ 2)⁻¹ * y * (r₁ * r₂) ^ 2 ∈ U ⊓ conjBy ((r₁ * r₂) ^ 2) U := ⟨hxU, hxc⟩
      rw [D.opp] at this
      exact this
    have : y = 1 := by
      rw [hx1] at e
      simpa using e.symm
    simp [this]
  exact D.ne_bot _ (Rt4_isRoot q) hbot

include D in
theorem exists_window (c : ℕ) : ∃ u : G,
    (∀ j : ℤ, 0 ≤ j → j ≤ 3 → ∀ x ∈ root (Rt 4 (c + j)), u⁻¹ * x * u ∈ U) ∧
    (∀ m : ℤ, (∀ x ∈ root (Rt 4 m), u⁻¹ * x * u ∈ U) →
      ∃ j : ℤ, 0 ≤ j ∧ j ≤ 3 ∧ (m - c - j) % 8 = 0) := by
  have hrU : ∀ q : ℤ, 0 ≤ q → q ≤ 3 → root (Rt 4 q) ≤ U := fun q h0 h1 =>
    D.root_le_U (by rw [Rt4_of_lt h0 h1]; omega) (by rw [Rt4_of_lt h0 h1]; omega)
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' c
  ·
    have hr := actsAs4_rot D.actsAs₁ D.actsAs₂ k
    refine ⟨(r₁ * r₂) ^ k, ?_, ?_⟩
    · intro j hj0 hj3 x hx
      have hy : ((r₁ * r₂) ^ k)⁻¹ * x * (r₁ * r₂) ^ k ∈ root (Rt 4 j) := by
        rw [hr j]
        have e : (r₁ * r₂) ^ k * (((r₁ * r₂) ^ k)⁻¹ * x * (r₁ * r₂) ^ k) * ((r₁ * r₂) ^ k)⁻¹ = x := by
          group
        rw [e]
        have : j + 2 * (k : ℤ) = (c : ℤ) + j := by rw [hk]; push_cast; ring
        show x ∈ root (Rt 4 (j + 2 * (k : ℤ)))
        rw [this]
        exact hx
      exact hrU j hj0 hj3 hy
    · intro m hm
      have hq : ∀ y ∈ root (Rt 4 (m - 2 * (k : ℤ))), y ∈ U := by
        intro y hy
        have hx : (r₁ * r₂) ^ k * y * ((r₁ * r₂) ^ k)⁻¹ ∈ root (Rt 4 m) := by
          have := (hr (m - 2 * (k : ℤ)) y).1 hy
          have e : m - 2 * (k : ℤ) + 2 * (k : ℤ) = m := by ring
          simpa only [e] using this
        have := hm _ hx
        simpa [mul_assoc] using this
      have h3 := D.pos_mod_le_three hq
      have h0 := Int.emod_nonneg (m - 2 * (k : ℤ)) (by norm_num : (8 : ℤ) ≠ 0)
      refine ⟨(m - 2 * (k : ℤ)) % 8, h0, h3, ?_⟩
      rw [hk]
      push_cast
      omega
  ·
    have hr := (actsAs4_rot D.actsAs₁ D.actsAs₂ k).mul D.actsAs₁
    refine ⟨(r₁ * r₂) ^ k * r₁, ?_, ?_⟩
    · intro j hj0 hj3 x hx
      have hy : ((r₁ * r₂) ^ k * r₁)⁻¹ * x * ((r₁ * r₂) ^ k * r₁) ∈ root (Rt 4 (3 - j)) := by
        rw [hr (3 - j)]
        have e : ((r₁ * r₂) ^ k * r₁) * (((r₁ * r₂) ^ k * r₁)⁻¹ * x * ((r₁ * r₂) ^ k * r₁)) *
            ((r₁ * r₂) ^ k * r₁)⁻¹ = x := by
          group
        rw [e]
        have : (4 - (3 - j)) + 2 * (k : ℤ) = (c : ℤ) + j := by rw [hk]; push_cast; ring
        show x ∈ root (Rt 4 ((4 - (3 - j)) + 2 * (k : ℤ)))
        rw [this]
        exact hx
      exact hrU (3 - j) (by omega) (by omega) hy
    · intro m hm
      have hq : ∀ y ∈ root (Rt 4 (4 + 2 * (k : ℤ) - m)), y ∈ U := by
        intro y hy
        have hx : ((r₁ * r₂) ^ k * r₁) * y * ((r₁ * r₂) ^ k * r₁)⁻¹ ∈ root (Rt 4 m) := by
          have := (hr (4 + 2 * (k : ℤ) - m) y).1 hy
          have e : (4 - (4 + 2 * (k : ℤ) - m)) + 2 * (k : ℤ) = m := by ring
          simpa only [e] using this
        have := hm _ hx
        simpa [mul_assoc] using this
      have h3 := D.pos_mod_le_three hq
      have h0 := Int.emod_nonneg (4 + 2 * (k : ℤ) - m) (by norm_num : (8 : ℤ) ≠ 0)
      refine ⟨3 - (4 + 2 * (k : ℤ) - m) % 8, by omega, by omega, ?_⟩
      rw [hk]
      push_cast
      omega

include D in
theorem Zij_le_U {i j : ℤ} (hi : 1 ≤ i) (hj : j ≤ 4) : Cor97.Zij root i j ≤ U :=
  iSup₂_le fun k hk => D.root_le_U (by have := hk.1; omega) (by have := hk.2; omega)

include D in
theorem Zij_inv {i j : ℤ} (hi : 1 ≤ i) (hj : j ≤ 4) :
    ∀ h ∈ H, ∀ z ∈ Cor97.Zij root i j, h * z * h⁻¹ ∈ Cor97.Zij root i j := by
  intro h hh z hz
  have : Cor97.Zij root i j ≤ (Cor97.Zij root i j).comap (MulAut.conj h).toMonoidHom := by
    refine iSup₂_le fun k hk x hx => ?_
    rw [Subgroup.mem_comap]
    have hk' : IsRoot 4 k := ⟨by have := hk.1; omega, by have := hk.1; have := hk.2; omega⟩
    exact Cor97.le_Zij hk (D.invariant k hk' h hh x hx)
  have h2 := this hz
  rw [Subgroup.mem_comap] at h2
  simpa [MulAut.conj_apply] using h2

include D in
theorem root_le_Zij_iff {i j k : ℤ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 4) (hk : IsRoot 4 k) :
    root k ≤ Cor97.Zij root i j ↔ i ≤ k ∧ k ≤ j := by
  refine ⟨fun hle => ?_, fun h => Cor97.le_Zij h⟩
  have hk0 := hk.1
  have hk4 : k.natAbs ≤ 4 := hk.2
  obtain ⟨uA, hA1, hA2⟩ := D.exists_window (j + 4).toNat
  obtain ⟨uB, hB1, hB2⟩ := D.exists_window (i - 1).toNat
  have hgenA : ∀ l : ℤ, i ≤ l → l ≤ j → ∀ x ∈ root l, uA⁻¹ * x * uA ∈ U := by
    intro l hl1 hl2 x hx
    have := hA1 (l - j + 3) (by omega) (by omega) x
    refine this ?_
    have e : (((j + 4).toNat : ℕ) : ℤ) + (l - j + 3) = (l - 1) + 8 := by omega
    rw [e, Rt4_add8, Rt4_of_lt (by omega) (by omega)]
    have : l - 1 + 1 = l := by ring
    rw [this]
    exact hx
  have hgenB : ∀ l : ℤ, i ≤ l → l ≤ j → ∀ x ∈ root l, uB⁻¹ * x * uB ∈ U := by
    intro l hl1 hl2 x hx
    have := hB1 (l - i) (by omega) (by omega) x
    refine this ?_
    have e : (((i - 1).toNat : ℕ) : ℤ) + (l - i) = l - 1 := by omega
    rw [e, Rt4_of_lt (by omega) (by omega)]
    have : l - 1 + 1 = l := by ring
    rw [this]
    exact hx
  have hZA := Cor97.Zij_conj_mem hgenA
  have hZB := Cor97.Zij_conj_mem hgenB
  obtain ⟨P, hP, hPk⟩ : ∃ P : ℤ, Rt 4 P = k ∧ (0 < k → P = k - 1) ∧ (k < 0 → P = 3 - k) := by
    rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · refine ⟨3 - k, ?_, fun h => by omega, fun _ => rfl⟩
      rw [Rt4_of_ge (by omega) (by omega)]
      ring
    · refine ⟨k - 1, ?_, fun _ => rfl, fun h => by omega⟩
      rw [Rt4_of_lt (by omega) (by omega)]
      ring
  obtain ⟨j₁, hj₁0, hj₁3, hj₁⟩ := hA2 P (fun x hx => hZA _ (hle (hP ▸ hx)))
  obtain ⟨j₂, hj₂0, hj₂3, hj₂⟩ := hB2 P (fun x hx => hZB _ (hle (hP ▸ hx)))
  have hPk' := hPk.1
  have hPk'' := hPk.2
  have hk' : -4 ≤ k ∧ k ≤ 4 := by omega
  have e1 : (((j + 4).toNat : ℕ) : ℤ) = j + 4 := by omega
  have e2 : (((i - 1).toNat : ℕ) : ℤ) = i - 1 := by omega
  rw [e1] at hj₁
  rw [e2] at hj₂
  rcases lt_or_gt_of_ne hk0 with hneg | hpos
  · have := hPk'' hneg
    omega
  · have := hPk' hpos
    omega

theorem intList_pairwise_lt (i j : ℤ) : (intList i j).Pairwise (· < ·) := by
  unfold intList
  rw [List.pairwise_map]
  have := List.pairwise_lt_range (n := (j + 1 - i).toNat)
  exact this.imp (by intro a b h; simpa using h)

theorem intList_reverse_pairwise_gt (i j : ℤ) : (intList i j).reverse.Pairwise (· > ·) := by
  rw [List.pairwise_reverse]
  exact intList_pairwise_lt i j

include D in
theorem Zij_eq_chainProd {i j : ℤ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 4) (l : List ℤ)
    (hl : l.Pairwise (· < ·) ∨ l.Pairwise (· > ·)) (hlm : ∀ k, k ∈ l ↔ i ≤ k ∧ k ≤ j) :
    (Cor97.Zij root i j : Set G) = chainProd root l ∧
      Nat.card (Cor97.Zij root i j) = (l.map fun k => Nat.card (root k)).prod := by
  refine D.L42 _ (D.Zij_le_U hi hj) (D.Zij_inv hi hj) l hl ?_
  intro k
  rw [hlm k]
  constructor
  · intro h
    exact ⟨⟨by omega, by omega⟩, Cor97.le_Zij h⟩
  · rintro ⟨hk, hle⟩
    exact (D.root_le_Zij_iff hi hij hj ⟨by omega, by omega⟩).1 hle

include D in
theorem Zij_one_four : Cor97.Zij root 1 4 = U := D.U_gen.symm

include D in
theorem root_le_normalizer [Finite G] {i j i' j' k : ℤ} (hi' : 1 ≤ i') (hii' : i' ≤ i)
    (hij : i ≤ j) (hjj' : j ≤ j') (hj' : j' ≤ 4) (hk : IsRoot 4 k) (hkV' : i' ≤ k ∧ k ≤ j')
    (hkV : ¬ (i ≤ k ∧ k ≤ j)) (hrest : ∀ l, i' ≤ l → l ≤ j' → l ≠ k → i ≤ l ∧ l ≤ j) :
    root k ≤ normalizer (Cor97.Zij root i j : Set G) := by
  have hi : 1 ≤ i := le_trans hi' hii'
  have hj : j ≤ 4 := le_trans hjj' hj'
  have hij' : i' ≤ j' := le_trans hii' (le_trans hij hjj')
  have hVV' : Cor97.Zij root i j ≤ Cor97.Zij root i' j' :=
    iSup₂_le fun l hl => Cor97.le_Zij ⟨le_trans hii' hl.1, le_trans hl.2 hjj'⟩
  have hp' : IsPGroup p (Cor97.Zij root i' j') := D.U_pGroup.to_le (D.Zij_le_U hi' hj')
  have : Fact p.Prime := ⟨D.prime⟩
  have hlt : Cor97.Zij root i j < Cor97.Zij root i' j' := by
    refine lt_of_le_of_ne hVV' ?_
    intro heq
    apply hkV
    have h1 : root k ≤ Cor97.Zij root i' j' := Cor97.le_Zij hkV'
    rw [← heq] at h1
    exact (D.root_le_Zij_iff hi hij hj hk).1 h1
  obtain ⟨x₀, hx₀V', hx₀n, hx₀V⟩ := exists_mem_normalizer_of_lt hp' hlt
  by_cases hkN : root k ≤ normalizer (Cor97.Zij root i j : Set G) ⊓ Cor97.Zij root i' j'
  · exact hkN.trans inf_le_left
  · exfalso
    have hVinv := D.Zij_inv hi hj
    have hV'inv := D.Zij_inv hi' hj'
    have hNinv : ∀ h ∈ H, ∀ z ∈ normalizer (Cor97.Zij root i j : Set G) ⊓ Cor97.Zij root i' j',
        h * z * h⁻¹ ∈ normalizer (Cor97.Zij root i j : Set G) ⊓ Cor97.Zij root i' j' :=
      fun h hh z hz => ⟨normalizer_inv_of_inv hVinv hh hz.1, hV'inv h hh z hz.2⟩
    have hNp : IsPGroup p ↥(normalizer (Cor97.Zij root i j : Set G) ⊓ Cor97.Zij root i' j') :=
      hp'.to_le inf_le_right
    have hNroots : ∀ l, l ∈ intList i j ↔ (1 ≤ l ∧ l ≤ 4) ∧
        root l ≤ normalizer (Cor97.Zij root i j : Set G) ⊓ Cor97.Zij root i' j' := by
      intro l
      rw [mem_intList_iff]
      constructor
      · intro hl
        refine ⟨⟨by omega, by omega⟩, le_inf ((Cor97.le_Zij hl).trans (Subgroup.le_normalizer)) ?_⟩
        exact (Cor97.le_Zij hl).trans hVV'
      · rintro ⟨hl, hle⟩
        have h1 := (D.root_le_Zij_iff hi' hij' hj' ⟨by omega, by omega⟩).1 (hle.trans inf_le_right)
        by_cases hlk : l = k
        · exact absurd (hlk ▸ hle) hkN
        · exact hrest l h1.1 h1.2 hlk
    have hN := D.L42 _ (inf_le_right.trans (D.Zij_le_U hi' hj')) hNinv (intList i j)
      (Or.inl (intList_pairwise_lt i j)) hNroots
    have hV := (D.Zij_eq_chainProd hi hij hj (intList i j) (Or.inl (intList_pairwise_lt i j))
      (fun l => mem_intList_iff)).1
    have hx : x₀ ∈ normalizer (Cor97.Zij root i j : Set G) ⊓ Cor97.Zij root i' j' := ⟨hx₀n, hx₀V'⟩
    have hx2 : x₀ ∈ (Cor97.Zij root i j : Set G) := by
      rw [hV, ← hN.1]
      exact hx
    exact hx₀V hx2

include D in
theorem subgroup_aux [Finite G] (i j : ℤ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 4) :
    ∃ V : Subgroup G, (V : Set G) = chainProd root (intList i j) ∧ V ≤ U ∧
      (1 < i → ∀ x ∈ root (i - 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧
      (j < 4 → ∀ x ∈ root (j + 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) := by
  refine ⟨Cor97.Zij root i j,
    (D.Zij_eq_chainProd hi hij hj _ (Or.inl (intList_pairwise_lt i j)) (fun l => mem_intList_iff)).1,
    D.Zij_le_U hi hj, ?_, ?_⟩
  · intro hi1 x hx v hv
    have hnorm : root (i - 1) ≤ normalizer (Cor97.Zij root i j : Set G) :=
      D.root_le_normalizer (i := i) (j := j) (i' := i - 1) (j' := j) (k := i - 1) (by omega)
        (by omega) hij le_rfl hj ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
        (by intro l h1 h2 h3; omega)
    exact (mem_normalizer_iff.1 (hnorm hx) v).1 hv
  · intro hj1 x hx v hv
    have hnorm : root (j + 1) ≤ normalizer (Cor97.Zij root i j : Set G) :=
      D.root_le_normalizer (i := i) (j := j) (i' := i) (j' := j + 1) (k := j + 1) hi le_rfl hij
        (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
        (by intro l h1 h2 h3; omega)
    exact (mem_normalizer_iff.1 (hnorm hx) v).1 hv

include D in
theorem reverse_eq_aux (i j : ℤ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 4) :
    chainProd root (intList i j) = chainProd root (intList i j).reverse := by
  have h1 := (D.Zij_eq_chainProd hi hij hj (intList i j) (Or.inl (intList_pairwise_lt i j))
    (fun l => mem_intList_iff)).1
  have h2 := (D.Zij_eq_chainProd hi hij hj (intList i j).reverse
    (Or.inr (intList_reverse_pairwise_gt i j))
    (fun l => by rw [List.mem_reverse]; exact mem_intList_iff)).1
  rw [← h1, ← h2]

include D in
theorem U_inv : ∀ h ∈ H, ∀ z ∈ U, h * z * h⁻¹ ∈ U := by
  rw [← D.Zij_one_four]
  exact D.Zij_inv le_rfl le_rfl

include D in
theorem H_le_normalizer_U : H ≤ normalizer (U : Set G) := by
  intro h hh
  rw [mem_normalizer_iff]
  exact fun u => inv_iff_of_inv D.U_inv hh u

include D in
theorem coe_sup_HU : ((H ⊔ U : Subgroup G) : Set G) = (H : Set G) * (U : Set G) :=
  Subgroup.coe_mul_of_left_le_normalizer_right H U D.H_le_normalizer_U

include D in
theorem eq_one_of_pow_eq_one {h : G} (hh : h ∈ H) {k : ℕ} (hk : h ^ (p ^ k) = 1) : h = 1 := by
  have : Fact p.Prime := ⟨D.prime⟩
  have h1 : orderOf h ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨a, ha, hord⟩ := (Nat.dvd_prime_pow D.prime).1 h1
  by_cases ha0 : a = 0
  · rw [ha0, pow_zero] at hord
    exact orderOf_eq_one_iff.1 hord
  · exact absurd (hord ▸ dvd_pow_self p ha0) (D.H_pPrime h hh)

include D in
theorem U_inf_H : U ⊓ H = ⊥ := by
  have : Fact p.Prime := ⟨D.prime⟩
  rw [eq_bot_iff]
  rintro x ⟨hxU, hxH⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 D.U_pGroup ⟨x, hxU⟩
  have : x ^ (p ^ k) = 1 := by
    have h2 : orderOf x = p ^ k := by simpa using hk
    rw [← h2]
    exact pow_orderOf_eq_one x
  exact D.eq_one_of_pow_eq_one hxH this

include D in
theorem mem_U_of_pow_eq_one {x : G} (hxB : x ∈ H ⊔ U) {k : ℕ} (hxk : x ^ (p ^ k) = 1) : x ∈ U := by
  have : Fact p.Prime := ⟨D.prime⟩
  rw [← SetLike.mem_coe, D.coe_sup_HU] at hxB
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hxB
  have key : ∀ m : ℕ, ∃ u' ∈ U, (h * u) ^ m = h ^ m * u' := by
    intro m
    induction m with
    | zero => exact ⟨1, U.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨u', hu', he⟩ := ih
      refine ⟨h⁻¹ * u' * h * u, ?_, ?_⟩
      · have h1 : h⁻¹ * u' * h⁻¹⁻¹ ∈ U := D.U_inv h⁻¹ (H.inv_mem hh) u' hu'
        simpa using U.mul_mem h1 hu
      · rw [pow_succ, he]
        group
  obtain ⟨u', hu', he⟩ := key (p ^ k)
  rw [hxk] at he
  have hhm : h ^ (p ^ k) = 1 := by
    have : h ^ (p ^ k) = u'⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      have h3 := he.symm
      rw [mul_eq_one_iff_eq_inv] at h3
      rw [h3]
      simp
    have hmemU : h ^ (p ^ k) ∈ U := by rw [this]; exact U.inv_mem hu'
    have hmemH : h ^ (p ^ k) ∈ H := H.pow_mem hh _
    have : h ^ (p ^ k) ∈ U ⊓ H := ⟨hmemU, hmemH⟩
    rw [D.U_inf_H] at this
    exact this
  have h1 : h = 1 := D.eq_one_of_pow_eq_one hh hhm
  subst h1
  simpa using hu

include D in
theorem meet_one_aux : ∀ x ∈ H ⊔ U, x ∈ conjBy ((r₁ * r₂) ^ 2) U → x = 1 := by
  intro x hxB hxc
  have : Fact p.Prime := ⟨D.prime⟩
  rw [mem_conjBy_iff] at hxc
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 D.U_pGroup ⟨_, hxc⟩
  have hk' : orderOf ((r₁ * r₂) ^ 2 * x * ((r₁ * r₂) ^ 2)⁻¹) = p ^ k := by simpa using hk
  have hxk : x ^ (p ^ k) = 1 := by
    have h2 : orderOf x = p ^ k := by
      rw [← hk']
      exact (orderOf_injective (MulAut.conj ((r₁ * r₂) ^ 2)).toMonoidHom
        (MulAut.conj ((r₁ * r₂) ^ 2)).injective x).symm
    rw [← h2]
    exact pow_orderOf_eq_one _
  have hxU : x ∈ U := D.mem_U_of_pow_eq_one hxB hxk
  have h2 : x ∈ U ⊓ conjBy ((r₁ * r₂) ^ 2) U := ⟨hxU, mem_conjBy_iff.2 hxc⟩
  rw [D.opp] at h2
  exact h2

include D in
theorem negGen_le_conj : negGen 4 root ≤ conjBy ((r₁ * r₂) ^ 2) U := by
  have hw := actsAs4_rot D.actsAs₁ D.actsAs₂ 2
  refine iSup₂_le fun k hk x hx => ?_
  have hk1 : 1 ≤ k := hk.1
  have hk4 : k ≤ 4 := by have := hk.2; exact_mod_cast this
  rw [mem_conjBy_iff]
  have hx' : x ∈ root (Rt 4 (k + 3)) := by
    rw [Rt4_of_ge (by omega) (by omega)]
    have : -(k + 3 - 3) = -k := by ring
    rw [this]
    exact hx
  have h1 := (hw (k + 3) x).1 hx'
  have e : Rt 4 (k + 3 + 2 * ((2 : ℕ) : ℤ)) = k := by
    have : k + 3 + 2 * ((2 : ℕ) : ℤ) = (k - 1) + 8 := by push_cast; ring
    rw [this, Rt4_add8, Rt4_of_lt (by omega) (by omega)]
    ring
  have h2 : (r₁ * r₂) ^ 2 * x * ((r₁ * r₂) ^ 2)⁻¹ ∈ root k := by
    have := h1
    simp only [] at this
    rw [e] at this
    exact this
  exact D.root_le_U hk1 hk4 h2

include D in
theorem meet_one : ∀ x ∈ H ⊔ U, x ∈ negGen 4 root → x = 1 :=
  fun x hx hn => D.meet_one_aux x hx (D.negGen_le_conj hn)

include D in
theorem unique_aux [Finite G] :
    ∀ f g : ℤ → G, (∀ k ∈ intList 1 4, f k ∈ root k) → (∀ k ∈ intList 1 4, g k ∈ root k) →
      ((intList 1 4).map f).prod = ((intList 1 4).map g).prod → ∀ k ∈ intList 1 4, f k = g k := by
  have h := D.Zij_eq_chainProd (i := 1) (j := 4) le_rfl (by norm_num) le_rfl (intList 1 4)
    (Or.inl (intList_pairwise_lt 1 4)) (fun l => mem_intList_iff)
  rw [D.Zij_one_four] at h
  apply unique_of_card root (intList 1 4)
  rw [← h.2]
  rw [← h.1]
  rfl

include D in
theorem carrier_eq_aux [Finite G] : (U : Set G) = chainProd root (intList 1 4) := by
  have h := D.Zij_eq_chainProd (i := 1) (j := 4) le_rfl (by norm_num) le_rfl (intList 1 4)
    (Or.inl (intList_pairwise_lt 1 4)) (fun l => mem_intList_iff)
  rw [D.Zij_one_four] at h
  exact h.1

include D in
theorem toRGD2 [Finite G] : RGD2 4 H r₁ r₂ U root where
  three_le := by norm_num
  comm_H := D.comm_H
  nilpotent := by
    have : Fact p.Prime := ⟨D.prime⟩
    exact IsPGroup.isNilpotent D.U_pGroup
  conj_H₁ := D.conj_H₁
  conj_H₂ := D.conj_H₂
  sq₁ := D.sq₁
  sq₂ := D.sq₂
  pow := D.pow
  U_inf_H := D.U_inf_H
  ne_bot := D.ne_bot
  invariant := D.invariant
  carrier_eq := D.carrier_eq_aux
  unique := D.unique_aux
  reverse_eq := fun i j hi hij hj => D.reverse_eq_aux i j hi hij (by exact_mod_cast hj)
  subgroup := fun i j hi hij hj => D.subgroup_aux i j hi hij (by exact_mod_cast hj)
  act₁ := by
    obtain ⟨a1, a2, a3⟩ := D.act₁
    refine ⟨a1, a2, fun i h1 h2 => ?_⟩
    have := a3 i h1 (by exact_mod_cast h2)
    have e : ((4 : ℕ) : ℤ) + 2 - i = 6 - i := by push_cast; ring
    rw [e]
    exact this
  act₂ := by
    obtain ⟨b1, b2, b3⟩ := D.act₂
    refine ⟨b1, b2, fun i h1 h2 => ?_⟩
    have := b3 i h1 (by omega)
    have e : ((4 : ℕ) : ℤ) - i = 4 - i := by push_cast; ring
    rw [e]
    exact this
  meet_one := D.meet_one
  rank₁ := D.bruhat₁
  rank₂ := D.bruhat₂

end Cor41

end CFSG.GH74.GLS.SP.Local
