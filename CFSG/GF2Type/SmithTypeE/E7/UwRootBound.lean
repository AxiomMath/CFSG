module

public import Mathlib.Data.Finset.Card

public section

namespace CFSG.GF2Type.SmithTypeE.E7

namespace UwRootSearch

abbrev V : Type := Bool × Fin 6 × Fin 6

@[expose] def adj : V → V → Bool
  | (false, i, j), (false, k, l) => (j == k) || (l == i)
  | (false, i, j), (true, k, l) => (j == k && l != i) || (j == l && k != i)
  | (true, k, l), (false, i, j) => (j == k && l != i) || (j == l && k != i)
  | (true, _, _), (true, _, _) => false

@[expose] def bnd : Nat → List V → Nat → Bool
  | 0, c, k => decide (c.length ≤ k)
  | fuel + 1, c, k =>
    if c.length ≤ k then true else
    match c with
    | [] => true
    | v :: rest => bnd fuel rest k &&
        (match k with | 0 => false | k' + 1 => bnd fuel (rest.filter fun w => !adj v w) k')

@[expose] def verts : List V :=
  ((List.finRange 6).flatMap fun i => (List.finRange 6).filterMap fun j =>
    if i < j then some (false, i, j) else none) ++
  ((List.finRange 6).flatMap fun i => (List.finRange 6).filterMap fun j =>
    if i < j then some (true, i, j) else none)

theorem bnd_verts : bnd 40 verts 15 = true := by decide +kernel

theorem bnd_sound : ∀ (fuel : Nat) (c : List V) (k : Nat), bnd fuel c k = true →
    ∀ S : Finset V, (∀ x ∈ S, x ∈ c) → (∀ x ∈ S, ∀ y ∈ S, adj x y = false) → S.card ≤ k := by
  intro fuel
  induction fuel with
  | zero =>
    intro c k h S hS _
    simp only [bnd, decide_eq_true_eq] at h
    calc S.card ≤ c.toFinset.card :=
          Finset.card_le_card (fun x hx => List.mem_toFinset.2 (hS x hx))
      _ ≤ c.length := List.toFinset_card_le c
      _ ≤ k := h
  | succ fuel ih =>
    intro c k h S hS hind
    by_cases hlen : c.length ≤ k
    · calc S.card ≤ c.toFinset.card :=
            Finset.card_le_card (fun x hx => List.mem_toFinset.2 (hS x hx))
        _ ≤ c.length := List.toFinset_card_le c
        _ ≤ k := hlen
    · cases c with
      | nil => exact absurd (Nat.zero_le k) hlen
      | cons v rest =>
        simp only [bnd, hlen, if_false, Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        by_cases hv : v ∈ S
        · cases k with
          | zero => exact absurd h2 (by simp)
          | succ k' =>
            have h3 := ih _ _ h2 (S.erase v) ?_ ?_
            · have := Finset.card_erase_add_one hv
              omega
            · intro x hx
              have hxS := Finset.mem_of_mem_erase hx
              have hxv := Finset.ne_of_mem_erase hx
              have hxc := hS x hxS
              rw [List.mem_cons] at hxc
              rw [List.mem_filter]
              refine ⟨hxc.resolve_left hxv, ?_⟩
              rw [hind v hv x hxS]
              rfl
            · intro x hx y hy
              exact hind x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)
        · refine ih rest k h1 S (fun x hx => ?_) hind
          have hxc := hS x hx
          rw [List.mem_cons] at hxc
          rcases hxc with rfl | hxc
          · exact absurd hx hv
          · exact hxc

end UwRootSearch

open UwRootSearch

theorem root_bound (SA SN : Finset (Fin 6 × Fin 6))
    (hAA : ∀ p ∈ SA, ∀ q ∈ SA, p.2 = q.1 → False)
    (hAN : ∀ p ∈ SA, ∀ q ∈ SN,
      ((p.2 = q.1 ∧ q.2 ≠ p.1) ∨ (p.2 = q.2 ∧ q.1 ≠ p.1)) → False)
    (hA : ∀ p ∈ SA, p.1 < p.2) (hN : ∀ p ∈ SN, p.1 < p.2) :
    SA.card + SN.card ≤ 15 := by
  classical
  let S : Finset V := SA.image (fun p => (false, p)) ∪ SN.image (fun p => (true, p))
  have hcard : S.card = SA.card + SN.card := by
    rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun p q h => by
        simpa using h), Finset.card_image_of_injective _ (fun p q h => by simpa using h)]
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨q, -, hq⟩ := Finset.mem_image.1 hx'
    simp at hq
  have hmem : ∀ x ∈ S, x ∈ verts := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      have := hA p hp
      simp only [verts, List.mem_append, List.mem_flatMap, List.mem_filterMap, List.mem_finRange,
        true_and]
      exact Or.inl ⟨p.1, p.2, by simp [this]⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      have := hN p hp
      simp only [verts, List.mem_append, List.mem_flatMap, List.mem_filterMap, List.mem_finRange,
        true_and]
      exact Or.inr ⟨p.1, p.2, by simp [this]⟩
  have hind : ∀ x ∈ S, ∀ y ∈ S, adj x y = false := by
    intro x hx y hy
    rcases Finset.mem_union.1 hx with hx | hx <;> rcases Finset.mem_union.1 hy with hy | hy
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      have h1 : p.2 ≠ q.1 := fun h => hAA p hp q hq h
      have h2 : q.2 ≠ p.1 := fun h => hAA q hq p hp h
      simp [adj, h1, h2]
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      have h := fun hh => hAN p hp q hq hh
      simp only [adj]
      by_contra hne
      simp at hne
      exact h (by tauto)
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      have h := fun hh => hAN q hq p hp hh
      simp only [adj]
      by_contra hne
      simp at hne
      exact h (by tauto)
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      simp [adj]
  have := bnd_sound 40 verts 15 bnd_verts S hmem hind
  rw [hcard] at this
  exact this

end CFSG.GF2Type.SmithTypeE.E7
