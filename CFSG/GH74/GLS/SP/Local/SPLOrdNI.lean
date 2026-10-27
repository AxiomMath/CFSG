module


import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

open Subgroup

namespace CFSG.GH74.GLS.SP.Local

theorem conj_not_inner {Y : Type} [Group Y] [Finite Y] (I N : Subgroup Y) [I.Normal] [N.Normal]
    (x : Y) (hY : ∀ y : Y, ∃ i ∈ I, ∃ k : ℤ, y = i * x ^ k) (_hN' : N = zpowers (x ^ 2))
    (hIN : I ⊓ N = ⊥) (hcard : 2 * Nat.card I = Nat.card (Y ⧸ N))
    (hcenter : ∀ p : Y ⧸ N, (∀ r : Y ⧸ N, p * r = r * p) → p = 1) :
    ¬ ∃ j ∈ I, ∀ i ∈ I, x * i * x⁻¹ = j * i * j⁻¹ := by
  rintro ⟨j, hjI, hj⟩
  have hyI : ∀ i ∈ I, Commute (j⁻¹ * x) i := by
    intro i hi
    have h := hj i hi
    show j⁻¹ * x * i = i * (j⁻¹ * x)
    calc j⁻¹ * x * i = j⁻¹ * (x * i * x⁻¹) * x := by group
      _ = j⁻¹ * (j * i * j⁻¹) * x := by rw [h]
      _ = i * (j⁻¹ * x) := by group
  have hyx : Commute (j⁻¹ * x) x := by
    have h := hj j⁻¹ (I.inv_mem hjI)
    have hxj : x * j⁻¹ = j⁻¹ * x := by
      calc x * j⁻¹ = x * j⁻¹ * x⁻¹ * x := by group
        _ = j * j⁻¹ * j⁻¹ * x := by rw [h]
        _ = j⁻¹ * x := by group
    show j⁻¹ * x * x = x * (j⁻¹ * x)
    calc j⁻¹ * x * x = x * j⁻¹ * x := by rw [hxj]
      _ = x * (j⁻¹ * x) := by group
  have hyY : ∀ w : Y, Commute (j⁻¹ * x) w := by
    intro w
    obtain ⟨i, hi, k, rfl⟩ := hY w
    exact (hyI i hi).mul_right (hyx.zpow_right k)
  have hyN : j⁻¹ * x ∈ N := by
    have h1 : ((j⁻¹ * x : Y) : Y ⧸ N) = 1 := by
      apply hcenter
      intro r
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective r
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (hyY w).eq]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hjx : ((j : Y) : Y ⧸ N) = (x : Y ⧸ N) := QuotientGroup.eq.mpr hyN
  have hbij : Function.Bijective (fun i : I => ((i : Y) : Y ⧸ N)) := by
    constructor
    · intro a b hab
      have hmem : (a : Y)⁻¹ * b ∈ I ⊓ N :=
        ⟨I.mul_mem (I.inv_mem a.2) b.2, QuotientGroup.eq.mp hab⟩
      rw [hIN, Subgroup.mem_bot] at hmem
      exact Subtype.ext (inv_mul_eq_one.mp hmem)
    · intro q
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨i, hi, k, rfl⟩ := hY w
      refine ⟨⟨i * j ^ k, I.mul_mem hi (I.zpow_mem hjI k)⟩, ?_⟩
      show ((i * j ^ k : Y) : Y ⧸ N) = ((i * x ^ k : Y) : Y ⧸ N)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_zpow,
        QuotientGroup.mk_zpow, hjx]
  have hpos : 0 < Nat.card I := Nat.card_pos
  have heq : Nat.card I = Nat.card (Y ⧸ N) := Nat.card_congr (Equiv.ofBijective _ hbij)
  omega

end CFSG.GH74.GLS.SP.Local
