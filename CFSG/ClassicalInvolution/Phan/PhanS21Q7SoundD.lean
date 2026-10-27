module

public import CFSG.ClassicalInvolution.Phan.PhanS19Q7Inputs
public import Mathlib.Logic.Relation

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

@[expose] def AdjIn {α : Type} (adj : α → α → Bool) (L : List α) (x y : α) : Prop :=
  x ∈ L ∧ y ∈ L ∧ adj x y = true

theorem bfsAux_sound {α : Type} (adj : α → α → Bool) (L : List α) (r : α) :
    ∀ (fuel : Nat) (frontier rest : List α), (∀ f ∈ frontier, f ∈ L) →
      (∀ f ∈ frontier, Relation.ReflTransGen (AdjIn adj L) r f) → (∀ u ∈ rest, u ∈ L) →
      bfsAux adj fuel frontier rest = true →
        ∀ u ∈ rest, Relation.ReflTransGen (AdjIn adj L) r u := by
  intro fuel
  induction fuel with
  | zero =>
    intro frontier rest _ _ _ h u hu
    simp only [bfsAux, List.isEmpty_iff] at h
    simp [h] at hu
  | succ fuel ih =>
    intro frontier rest hFL hfront hL h u hu
    simp only [bfsAux, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      List.isEmpty_iff] at h
    rcases h with h | ⟨_, hrec⟩
    · simp [h] at hu
    · rw [List.partition_eq_filter_filter] at hrec
      have hnext : ∀ v ∈ List.filter (fun u => frontier.any fun f => adj f u) rest,
          Relation.ReflTransGen (AdjIn adj L) r v := by
        intro v hv
        rw [List.mem_filter, List.any_eq_true] at hv
        obtain ⟨hvr, f, hf, hfv⟩ := hv
        exact (hfront f hf).tail ⟨hFL f hf, hL v hvr, hfv⟩
      have hrest := ih _ _ (fun v hv => hL v (List.mem_filter.1 hv).1) hnext
        (fun v hv => hL v (List.mem_filter.1 hv).1) hrec
      rcases (List.mem_partition (p := fun u => frontier.any fun f => adj f u)).1 hu with
        hu1 | hu2
      · rw [List.partition_eq_filter_filter] at hu1
        exact hnext u hu1
      · rw [List.partition_eq_filter_filter] at hu2
        exact hrest u hu2

theorem reflTransGen_symm {α : Type} {r : α → α → Prop} (hr : ∀ x y, r x y → r y x) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hr _ _ hbc) ih

theorem bfsOk_sound {α : Type} (adj : α → α → Bool)
    (hsymm : ∀ x y, adj x y = true → adj y x = true) {L : List α} (h : bfsOk adj L = true) :
    ∀ p ∈ L, ∀ q ∈ L, Relation.ReflTransGen (AdjIn adj L) p q := by
  cases L with
  | nil =>
    intro p hp
    simp at hp
  | cons r rest =>
    have h' : bfsAux adj 12 [r] rest = true := h
    have hroot : ∀ u ∈ r :: rest, Relation.ReflTransGen (AdjIn adj (r :: rest)) r u := by
      intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · exact Relation.ReflTransGen.refl
      · refine bfsAux_sound adj (r :: rest) r 12 [r] rest ?_ ?_ ?_ h' u hu
        · intro f hf
          simp only [List.mem_singleton] at hf
          subst hf
          exact List.mem_cons_self
        · intro f hf
          simp only [List.mem_singleton] at hf
          subst hf
          exact Relation.ReflTransGen.refl
        · exact fun v hv => List.mem_cons_of_mem _ hv
    have hsym : ∀ x y, AdjIn adj (r :: rest) x y → AdjIn adj (r :: rest) y x := fun x y hxy =>
      ⟨hxy.2.1, hxy.1, hsymm x y hxy.2.2⟩
    intro p hp q hq
    exact (reflTransGen_symm hsym (hroot p hp)).trans (hroot q hq)

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
