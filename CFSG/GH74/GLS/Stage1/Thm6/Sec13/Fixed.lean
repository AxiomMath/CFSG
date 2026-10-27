module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

theorem card_fix_modEq [Finite G] {p : ℕ} [Fact p.Prime] (S : Set G) (f : G) (k : ℕ)
    (hf : f ^ p ^ k = 1) (hN : ∀ v ∈ S, f * v * f⁻¹ ∈ S) :
    Nat.card S ≡ Nat.card {v : S // f * (v : G) * f⁻¹ = v} [MOD p] := by
  classical
  have : Fintype S := Fintype.ofFinite S
  let σ : Function.End S := fun v => ⟨f * v * f⁻¹, hN v v.2⟩
  have hit : ∀ n : ℕ, ∀ v : S, ((σ ^ n) v : G) = f ^ n * v * (f ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro v; show (v : G) = f ^ 0 * v * (f ^ 0)⁻¹; simp
    | succ n ih =>
      intro v
      rw [pow_succ]
      show ((σ ^ n) (σ v) : G) = _
      rw [ih]
      simp [σ, pow_succ, mul_assoc]
  have hσ : σ ^ p ^ k = 1 := by
    funext v
    apply Subtype.ext
    rw [hit, hf]
    show _ = (v : G)
    simp
  have h := Equiv.Perm.card_fixedPoints_modEq (f := σ) (p := p) (n := k) hσ
  rw [Nat.card_eq_fintype_card]
  have e : Nat.card {v : S // f * (v : G) * f⁻¹ = v} = Fintype.card (Function.fixedPoints σ) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun v => by
      simp [Function.mem_fixedPoints, Function.IsFixedPt, σ, Subtype.ext_iff] :
        ∀ v : S, f * (v : G) * f⁻¹ = v ↔ v ∈ Function.fixedPoints σ))]
    rw [Nat.card_eq_fintype_card]
  rw [e]
  exact h

theorem exists_fixed_of_not_dvd [Finite G] {p : ℕ} [hp : Fact p.Prime] (S : Set G) (f : G) (k : ℕ)
    (hf : f ^ p ^ k = 1) (hN : ∀ v ∈ S, f * v * f⁻¹ ∈ S) (hS : ¬ p ∣ Nat.card S) :
    ∃ v ∈ S, f * v * f⁻¹ = v := by
  have h := card_fix_modEq S f k hf hN
  by_contra hcon
  push Not at hcon
  have h0 : Nat.card {v : S // f * (v : G) * f⁻¹ = v} = 0 := by
    rw [Nat.card_eq_zero]
    left
    exact ⟨fun ⟨v, hv⟩ => hcon v v.2 hv⟩
  rw [h0] at h
  exact hS ((Nat.modEq_zero_iff_dvd).1 h)

theorem fixed_in_coset [Finite G] {p : ℕ} [hp : Fact p.Prime] (N : Subgroup G) (f g : G) (k : ℕ)
    (hf : f ^ p ^ k = 1) (hN : ∀ n ∈ N, f * n * f⁻¹ ∈ N) (hg : g⁻¹ * (f * g * f⁻¹) ∈ N)
    (hNp : ¬ p ∣ Nat.card N) : ∃ n ∈ N, f * (g * n) * f⁻¹ = g * n := by
  let S : Set G := {y | g⁻¹ * y ∈ N}
  have hS : ∀ y ∈ S, f * y * f⁻¹ ∈ S := by
    intro y hy
    have e : g⁻¹ * (f * y * f⁻¹) = (g⁻¹ * (f * g * f⁻¹)) * (f * (g⁻¹ * y) * f⁻¹) := by group
    show g⁻¹ * (f * y * f⁻¹) ∈ N
    rw [e]
    exact N.mul_mem hg (hN _ hy)
  have hcard : Nat.card S = Nat.card N := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun y => ⟨g⁻¹ * y.1, y.2⟩
        invFun := fun n => ⟨g * n.1, by simp [S]⟩
        left_inv := fun y => by ext; simp
        right_inv := fun n => by ext; simp }
  obtain ⟨y, hy, hfix⟩ := exists_fixed_of_not_dvd S f k hf hS (by rwa [hcard])
  exact ⟨g⁻¹ * y, hy, by simpa using hfix⟩

theorem fix_free_four [Finite G] (V : Subgroup G) (f : G) (k : ℕ) (hf : f ^ 3 ^ k = 1)
    (hN : ∀ v ∈ V, f * v * f⁻¹ ∈ V) (hV : Nat.card V = 4)
    (hnc : ∃ v ∈ V, f * v * f⁻¹ ≠ v) : ∀ v ∈ V, f * v * f⁻¹ = v → v = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := card_fix_modEq (p := 3) (V : Set G) f k hf hN
  rw [show Nat.card (V : Set G) = 4 from hV] at h
  set F := {v : (V : Set G) // f * (v : G) * f⁻¹ = v} with hF
  have hinj : Function.Injective (fun z : F => (⟨z.1.1, z.1.2⟩ : V)) := by
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg Subtype.val hab
  have hle : Nat.card F ≤ 4 := by
    rw [← hV]
    exact Nat.card_le_card_of_injective _ hinj
  have hpos : 0 < Nat.card F := by
    apply Nat.card_pos_iff.2
    exact ⟨⟨⟨(1 : G), V.one_mem⟩, by simp⟩, inferInstance⟩
  have hmod : Nat.card F % 3 = 1 := by
    have := h.symm
    unfold Nat.ModEq at this
    simpa using this
  have hcases : Nat.card F = 1 ∨ Nat.card F = 4 := by omega
  rcases hcases with h1 | h4
  · intro v hv hfix
    by_contra hne
    have : 1 < Nat.card F := by
      rw [Finite.one_lt_card_iff_nontrivial]
      refine ⟨⟨⟨1, V.one_mem⟩, by simp⟩, ⟨⟨v, hv⟩, hfix⟩, ?_⟩
      intro heq
      apply hne
      have := congrArg (fun z : F => (z.1 : G)) heq
      simpa using this.symm
    omega
  · exfalso
    obtain ⟨v, hv, hne⟩ := hnc
    have hbij := hinj.bijective_of_nat_card_le (by rw [h4, hV])
    obtain ⟨z, hz⟩ := hbij.2 ⟨v, hv⟩
    apply hne
    have := z.2
    have hzv : (z.1 : G) = v := by simpa using congrArg Subtype.val hz
    rw [← hzv]
    exact this

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
