module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.KC.OrbRow

open Subgroup

variable {α : Type*}

theorem card_ge_of_orbit (H : Subgroup (Equiv.Perm α)) [Finite H] (a : α) (s : Finset α)
    (hs : ∀ x ∈ s, ∃ h ∈ H, h a = x) (S : Subgroup (Equiv.Perm α)) (hS : ∀ g ∈ S, g ∈ H ∧ g a = a) :
    s.card * Nat.card S ≤ Nat.card H := by
  choose f hfH hfa using hs
  let F : s × S → H := fun p => ⟨f p.1 p.1.2 * p.2, H.mul_mem (hfH _ _) (hS _ p.2.2).1⟩
  have hF : Function.Injective F := by
    rintro ⟨⟨x, hx⟩, ⟨g, hg⟩⟩ ⟨⟨y, hy⟩, ⟨g', hg'⟩⟩ he
    have he' : f x hx * g = f y hy * g' := congrArg Subtype.val he
    have hxy : x = y := by
      have := congrArg (fun σ : Equiv.Perm α => σ a) he'
      simp only [Equiv.Perm.mul_apply, (hS g hg).2, (hS g' hg').2, hfa] at this
      exact this
    subst hxy
    have hgg : g = g' := mul_left_cancel he'
    subst hgg
    rfl
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := s), Fintype.card_coe] at this

@[expose] def stabB (P : Subgroup (Equiv.Perm α)) (b : ℕ → α) (i : ℕ) :
    Subgroup (Equiv.Perm α) where
  carrier := {g | g ∈ P ∧ ∀ t < i, g (b t) = b t}
  one_mem' := ⟨P.one_mem, fun _ _ => rfl⟩
  mul_mem' {g h} hg hh := ⟨P.mul_mem hg.1 hh.1, fun t ht => by
    rw [Equiv.Perm.mul_apply, hh.2 t ht, hg.2 t ht]⟩
  inv_mem' {g} hg := ⟨P.inv_mem hg.1, fun t ht => by
    rw [Equiv.Perm.inv_eq_iff_eq, hg.2 t ht]⟩

theorem mem_stabB {P : Subgroup (Equiv.Perm α)} {b : ℕ → α} {i : ℕ} {g : Equiv.Perm α} :
    g ∈ stabB P b i ↔ g ∈ P ∧ ∀ t < i, g (b t) = b t := Iff.rfl

theorem tight_chain (P : Subgroup (Equiv.Perm α)) [Finite P] (b : ℕ → α) (L : ℕ)
    (G : ℕ → Subgroup (Equiv.Perm α)) (k : ℕ → ℕ) (hGP : ∀ i ≤ L, G i ≤ P)
    (hfix : ∀ i ≤ L, ∀ g ∈ G i, ∀ t < i, g (b t) = b t) (hdec : ∀ i < L, G (i + 1) ≤ G i)
    (horb : ∀ i < L, ∃ s : Finset α, s.card = k i ∧ ∀ x ∈ s, ∃ g ∈ G i, g (b i) = x)
    (hprod : Nat.card P = ∏ t ∈ Finset.range L, k t) :
    ∀ i ≤ L, G i = stabB P b i ∧ Nat.card (G i) = ∏ t ∈ Finset.Ico i L, k t := by
  have hfinS : ∀ i, Finite (stabB P b i) := fun i =>
    Finite.of_injective (fun g : stabB P b i => (⟨g.1, g.2.1⟩ : P)) fun g h he => by
      apply Subtype.ext
      simpa using congrArg Subtype.val he
  have hGS : ∀ i ≤ L, G i ≤ stabB P b i := fun i hi g hg => ⟨hGP i hi hg, hfix i hi g hg⟩
  have hfinG : ∀ i ≤ L, Finite (G i) := fun i hi =>
    Finite.of_injective (fun g : G i => (⟨g.1, hGP i hi g.2⟩ : P)) fun g h he => by
      apply Subtype.ext
      simpa using congrArg Subtype.val he
  have hS : ∀ i < L, k i * Nat.card (stabB P b (i + 1)) ≤ Nat.card (stabB P b i) := by
    intro i hi
    obtain ⟨s, hs, hsx⟩ := horb i hi
    rw [← hs]
    refine card_ge_of_orbit _ (b i) s (fun x hx => ?_) _ (fun g hg => ?_)
    · obtain ⟨g, hg, hgx⟩ := hsx x hx
      exact ⟨g, hGS i hi.le hg, hgx⟩
    · exact ⟨⟨hg.1, fun t ht => hg.2 t (Nat.lt_succ_of_lt ht)⟩, hg.2 i (Nat.lt_succ_self i)⟩
  have hSup : ∀ i ≤ L, (∏ t ∈ Finset.range i, k t) * Nat.card (stabB P b i) ≤ Nat.card P := by
    intro i
    induction i with
    | zero =>
      intro _
      have : stabB P b 0 = P := by
        ext g
        exact ⟨fun h => h.1, fun h => ⟨h, fun t ht => absurd ht (Nat.not_lt_zero t)⟩⟩
      rw [Finset.prod_range_zero, one_mul, this]
    | succ i ih =>
      intro hi
      rw [Finset.prod_range_succ, mul_assoc]
      exact (Nat.mul_le_mul_left _ (hS i hi)).trans (ih (Nat.le_of_succ_le hi))
  have hGlow : ∀ d i, i + d = L → ∏ t ∈ Finset.Ico i L, k t ≤ Nat.card (G i) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      rw [Nat.add_zero] at hi
      subst hi
      rw [Finset.Ico_self, Finset.prod_empty]
      have := hfinG i le_rfl
      exact Nat.card_pos
    | succ d ih =>
      intro i hi
      have hiL : i < L := by omega
      have := hfinG i hiL.le
      rw [Finset.prod_eq_prod_Ico_succ_bot hiL]
      obtain ⟨s, hs, hsx⟩ := horb i hiL
      have hc := card_ge_of_orbit (G i) (b i) s hsx (G (i + 1))
        (fun g hg => ⟨hdec i hiL hg, hfix (i + 1) (by omega) g hg i (Nat.lt_succ_self i)⟩)
      rw [hs] at hc
      exact (Nat.mul_le_mul_left _ (ih (i + 1) (by omega))).trans hc
  intro i hi
  have := hfinS i
  have hpos : 0 < ∏ t ∈ Finset.range i, k t := by
    rcases Nat.eq_zero_or_pos (∏ t ∈ Finset.range i, k t) with h0 | h0
    · exfalso
      have hP := Finset.prod_range_mul_prod_Ico k hi
      rw [h0, zero_mul, ← hprod] at hP
      exact Nat.card_pos.ne' hP.symm
    · exact h0
  have hup : Nat.card (stabB P b i) ≤ ∏ t ∈ Finset.Ico i L, k t := by
    have h1 := hSup i hi
    rw [hprod, ← Finset.prod_range_mul_prod_Ico k hi] at h1
    exact Nat.le_of_mul_le_mul_left h1 hpos
  have hlow := hGlow (L - i) i (by omega)
  have hcard : Nat.card (stabB P b i) ≤ Nat.card (G i) := hup.trans hlow
  have heq : G i = stabB P b i := Subgroup.eq_of_le_of_card_ge (hGS i hi) hcard
  refine ⟨heq, le_antisymm ?_ hlow⟩
  rw [heq]
  exact hup

end CFSG.KC.OrbRow

end
