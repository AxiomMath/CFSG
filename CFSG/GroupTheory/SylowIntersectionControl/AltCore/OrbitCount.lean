module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
private theorem mem_orbit_iff_exists {P : Subgroup (Perm α)} {x y : α} :
    y ∈ orbit P x ↔ ∃ g ∈ P, g x = y := by
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

omit [Fintype α] [DecidableEq α] in
private theorem orbit_subset_of_stable {P : Subgroup (Perm α)} {S : Set α}
    (hS : ∀ g ∈ P, ∀ x ∈ S, g x ∈ S) {x : α} (hx : x ∈ S) : orbit P x ⊆ S := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := mem_orbit_iff_exists.mp hy
  exact hS g hg x hx

omit [Fintype α] [DecidableEq α] in
private theorem stable_sdiff_orbit {P : Subgroup (Perm α)} {S : Set α}
    (hS : ∀ g ∈ P, ∀ x ∈ S, g x ∈ S) (x : α) :
    ∀ g ∈ P, ∀ y ∈ S \ orbit P x, g y ∈ S \ orbit P x := by
  rintro g hg y ⟨hyS, hyO⟩
  refine ⟨hS g hg y hyS, fun h => hyO ?_⟩
  obtain ⟨f, hf, hfx⟩ := mem_orbit_iff_exists.mp h
  exact mem_orbit_iff_exists.mpr ⟨g⁻¹ * f, P.mul_mem (P.inv_mem hg) hf, by simp [hfx]⟩

omit [DecidableEq α] in
private theorem ncard_sdiff_orbit_add {P : Subgroup (Perm α)} {S : Set α}
    (hS : ∀ g ∈ P, ∀ x ∈ S, g x ∈ S) {x : α} (hx : x ∈ S) :
    (S \ orbit P x).ncard + Nat.card (orbit P x) = S.ncard :=
  Set.ncard_sdiff_add_ncard_of_subset (orbit_subset_of_stable hS hx) S.toFinite

omit [DecidableEq α] in
private theorem dvd_ncard_aux {P : Subgroup (Perm α)} {d : ℕ} (n : ℕ) :
    ∀ S : Set α, S.ncard = n → (∀ g ∈ P, ∀ x ∈ S, g x ∈ S) →
      (∀ x ∈ S, d ∣ Nat.card (orbit P x)) → d ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hSn hS hd
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp at hSn
      simp [← hSn]
    · have hcard := ncard_sdiff_orbit_add hS hx
      have hpos : 0 < Nat.card (orbit P x) :=
        have : Nonempty (orbit P x) := ⟨⟨x, mem_orbit_self x⟩⟩
        Nat.card_pos
      have := ih (S \ orbit P x).ncard (by omega) (S \ orbit P x) rfl (stable_sdiff_orbit hS x)
        fun y hy => hd y hy.1
      rw [← hSn, ← hcard]
      exact dvd_add this (hd x hx)

omit [DecidableEq α] in
theorem dvd_ncard_of_forall_dvd {P : Subgroup (Perm α)} {S : Set α} {d : ℕ}
    (hS : ∀ g ∈ P, ∀ x ∈ S, g x ∈ S) (hd : ∀ x ∈ S, d ∣ Nat.card (orbit P x)) :
    d ∣ S.ncard :=
  dvd_ncard_aux S.ncard S rfl hS hd

omit [DecidableEq α] in
private theorem ncard_add_le_aux {P : Subgroup (Perm α)} {lo : ℕ} (k : ℕ) :
    ∀ S : Set α, (∀ g ∈ P, ∀ x ∈ S, g x ∈ S) →
      (∀ x ∈ S, ∃ a, lo ≤ a ∧ a < lo + k ∧ Nat.card (orbit P x) = 2 ^ a) →
      (∀ x ∈ S, ∀ y ∈ S, Nat.card (orbit P x) = Nat.card (orbit P y) →
        orbit P x = orbit P y) →
      S.ncard + 2 ^ lo ≤ 2 ^ (lo + k) := by
  induction k with
  | zero =>
    intro S _ hsize _
    have hempty : S = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨a, h1, h2, -⟩ := hsize x hx
      omega
    simp [hempty]
  | succ k ih =>
    intro S hS hsize hdist
    by_cases hex : ∃ x ∈ S, Nat.card (orbit P x) = 2 ^ (lo + k)
    · obtain ⟨x, hx, hxc⟩ := hex
      have hcard := ncard_sdiff_orbit_add hS hx
      have := ih (S \ orbit P x) (stable_sdiff_orbit hS x) ?_
        fun y hy z hz => hdist y hy.1 z hz.1
      · rw [← add_assoc, pow_succ]
        omega
      · intro y hy
        obtain ⟨a, h1, h2, h3⟩ := hsize y hy.1
        refine ⟨a, h1, ?_, h3⟩
        by_contra hlt
        obtain rfl : a = lo + k := by omega
        refine hy.2 ?_
        rw [← hdist y hy.1 x hx (h3.trans hxc.symm)]
        exact mem_orbit_self y
    · have := ih S hS ?_ hdist
      · rw [← add_assoc, pow_succ]
        omega
      · intro y hy
        obtain ⟨a, h1, h2, h3⟩ := hsize y hy
        refine ⟨a, h1, ?_, h3⟩
        by_contra hlt
        obtain rfl : a = lo + k := by omega
        exact hex ⟨y, hy, h3⟩

omit [DecidableEq α] in
theorem ncard_add_le_of_card_orbit_injective {P : Subgroup (Perm α)} {S : Set α} {lo m : ℕ}
    (hlm : lo ≤ m) (hS : ∀ g ∈ P, ∀ x ∈ S, g x ∈ S)
    (hsize : ∀ x ∈ S, ∃ a, lo ≤ a ∧ a < m ∧ Nat.card (orbit P x) = 2 ^ a)
    (hdist : ∀ x ∈ S, ∀ y ∈ S, Nat.card (orbit P x) = Nat.card (orbit P y) →
      orbit P x = orbit P y) :
    S.ncard + 2 ^ lo ≤ 2 ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlm
  exact ncard_add_le_aux k S hS hsize hdist

end CFSG.GroupTheory.AltCore
