module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PGroupBlocks

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
private lemma mem_orbit_iff_exists {P : Subgroup (Perm α)} {x y : α} :
    y ∈ orbit P x ↔ ∃ g ∈ P, g x = y :=
  ⟨fun ⟨p, hp⟩ => ⟨p, p.2, hp⟩, fun ⟨g, hg, h⟩ => ⟨⟨g, hg⟩, h⟩⟩

omit [DecidableEq α] in
private lemma exists_card_orbit_two_pow {P : Subgroup (Perm α)} (hP : IsPGroup 2 P) (x : α) :
    ∃ j, Nat.card (orbit P x) = 2 ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have h1 : (stabilizer P x).index ∣ Nat.card P := index_dvd_card _
  rw [index_stabilizer, hm] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  exact ⟨j, by rw [Nat.card_coe_set_eq, hj]⟩

omit [DecidableEq α] in
private lemma exists_orbit_setoid {P : Subgroup (Perm α)} (hP : IsPGroup 2 P) {S : Set α} (i : ℕ)
    (hsize : ∀ x ∈ S, 2 ^ i ≤ Nat.card (orbit P x)) (O : Set α) :
    ∃ T : Setoid α, (∀ g ∈ P, ∀ y z, T.r (g y) (g z) ↔ T.r y z) ∧
      (∀ y z, T.r y z → (y ∈ O ↔ z ∈ O)) ∧ (∀ y, y ∉ O → ∀ z, T.r y z → z = y) ∧
      (∀ r ∈ S, O = orbit P r → ∀ y ∈ O, Nat.card {z // T.r y z} = 2 ^ i) ∧
      ((∀ r ∈ S, O ≠ orbit P r) → ∀ y z, T.r y z → z = y) := by
  by_cases h : ∃ r ∈ S, O = orbit P r
  · obtain ⟨r, hr, rfl⟩ := h
    obtain ⟨j, hj⟩ := exists_card_orbit_two_pow hP r
    have hij : i ≤ j := (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (hj ▸ hsize r hr)
    obtain ⟨B, hxB, hBO, hBc, hB⟩ := exists_block_of_isPGroup hP r hj hij
    obtain ⟨T, h1, h2, h3, h4, -⟩ := exists_setoid_of_block hxB hBO hB
    exact ⟨T, h1, h2, h3, fun _ _ _ y hy => (h4 y hy).trans hBc, fun h => absurd rfl (h r hr)⟩
  · refine ⟨⊥, fun g _ y z => g.injective.eq_iff, fun y z h => h ▸ Iff.rfl, fun y _ z h => h.symm,
      fun r hr hO => absurd ⟨r, hr, hO⟩ h, fun _ y z h => h.symm⟩

omit [DecidableEq α] in
theorem exists_setoid_blocks {P : Subgroup (Perm α)} (hP : IsPGroup 2 P) {S : Set α} (i : ℕ)
    (hS : ∀ x ∈ S, ∀ g ∈ P, g x ∈ S) (hsize : ∀ x ∈ S, 2 ^ i ≤ Nat.card (orbit P x)) :
    ∃ t : Setoid α, (∀ g ∈ P, ∀ x y, t.r (g x) (g y) ↔ t.r x y) ∧
      (∀ x y, t.r x y → y ∈ orbit P x) ∧
      (∀ x ∈ S, Nat.card {y // t.r x y} = 2 ^ i) ∧
      (∀ x, x ∉ S → ∀ y, t.r x y → y = x) := by
  choose T h1 h2 h3 h4 h5 using exists_orbit_setoid hP i hsize
  have hmem : ∀ x y, (T (orbit P x)).r x y → y ∈ orbit P x := fun x y h =>
    (h2 _ x y h).1 (mem_orbit_self x)
  have horb : ∀ x y, (T (orbit P x)).r x y → orbit P y = orbit P x := fun x y h =>
    orbit_eq_iff.2 (hmem x y h)
  refine ⟨⟨fun x y => (T (orbit P x)).r x y, ⟨fun x => Setoid.refl' _ x, ?_, ?_⟩⟩, ?_, hmem, ?_, ?_⟩
  · intro x y h
    show (T (orbit P y)).r y x
    rw [horb x y h]
    exact Setoid.symm' _ h
  · intro x y z hxy hyz
    rw [horb x y hxy] at hyz
    exact Setoid.trans' _ hxy hyz
  · intro g hg x y
    have : orbit P (g x) = orbit P x := orbit_smul (⟨g, hg⟩ : P) x
    show (T (orbit P (g x))).r (g x) (g y) ↔ (T (orbit P x)).r x y
    rw [this]
    exact h1 _ g hg x y
  · exact fun x hx => h4 (orbit P x) x hx rfl x (mem_orbit_self x)
  · intro x hx y h
    refine h5 (orbit P x) (fun r hr hr' => hx ?_) x y h
    obtain ⟨p, hp, hpr⟩ := mem_orbit_iff_exists.1 (hr' ▸ mem_orbit_self x)
    exact hpr ▸ hS r hr p hp

end CFSG.GroupTheory.AltCore
