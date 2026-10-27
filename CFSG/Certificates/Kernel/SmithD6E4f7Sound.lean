module

public import Certificates.Data.Kernel.SmithD6.E4f7K

public section

namespace CFSG.KD.SmithD6E4

open CFSG.KD.SmithD6

theorem e4MemGo_cons (x : Nat) (p : Nat × List Nat) (W : List (Nat × List Nat)) :
    e4MemGo x (p :: W) = bIf(Nat.beq p.1 x, true, e4MemGo x W) := rfl

theorem e4MemGo_sound {x : Nat} {W : List (Nat × List Nat)} (h : e4MemGo x W = true) :
    ∃ w, (x, w) ∈ W := by
  induction W with
  | nil => exact absurd h Bool.false_ne_true
  | cons p W ih =>
    rw [e4MemGo_cons] at h
    cases hp : Nat.beq p.1 x
    · rw [hp] at h
      obtain ⟨w, hw⟩ := ih h
      exact ⟨w, List.mem_cons_of_mem _ hw⟩
    · refine ⟨p.2, ?_⟩
      rw [← Nat.eq_of_beq_eq_true hp]
      exact List.mem_cons_self

theorem e4ListGo_cons (W : List (Nat × List Nat)) (y : Nat) (l : List Nat) :
    e4ListGo W (y :: l) =
      bAnd(bIf(Nat.beq (Nat.land y e4Out) 0, e4MemGo y W, true), e4ListGo W l) := rfl

theorem e4ListGo_sound {W : List (Nat × List Nat)} {l : List Nat} (h : e4ListGo W l = true) :
    ∀ x ∈ l, x &&& e4Out = 0 → ∃ w, (x, w) ∈ W := by
  induction l with
  | nil =>
    intro x hx
    exact absurd hx List.not_mem_nil
  | cons y l ih =>
    rw [e4ListGo_cons] at h
    intro x hx hm
    cases hy : bIf(Nat.beq (Nat.land y e4Out) 0, e4MemGo y W, true)
    · rw [hy] at h
      exact absurd h Bool.false_ne_true
    · rw [hy] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · have hb : Nat.beq (Nat.land x e4Out) 0 = true := Nat.beq_eq_true_eq _ _ ▸ hm
        rw [hb] at hy
        exact e4MemGo_sound hy
      · exact ih h x hx hm

theorem e4Chunks_sound : ∀ cs : List (List Nat), e4ChunksGo cs = true →
    ∀ x ∈ cs.flatten, x &&& e4Out = 0 → ∃ w, (x, w) ∈ JE.e4W
  | [], _ => by simp
  | ch :: cs, h => by
    intro x hx hm
    have e : e4ChunksGo (ch :: cs) = bAnd(e4ListGo JE.e4W ch, e4ChunksGo cs) := rfl
    rw [e] at h
    cases hc : e4ListGo JE.e4W ch
    · rw [hc] at h
      exact absurd h Bool.false_ne_true
    · rw [hc] at h
      rw [List.flatten_cons] at hx
      rcases List.mem_append.1 hx with hx | hx
      · exact e4ListGo_sound hc x hx hm
      · exact e4Chunks_sound cs h x hx hm

theorem e4AllOK_sound (h : e4AllOK = true) :
    ∀ x ∈ J.wtC.flatten, x &&& e4Out = 0 → ∃ w, (x, w) ∈ JE.e4W :=
  e4Chunks_sound J.wtC h

theorem e4WordsOK_sound {r : Nat} {W : List (Nat × List Nat)} (h : e4WordsOK r W = true) :
    ∀ p ∈ W, (∀ g ∈ p.2, g < 4) ∧ e4Ap p.2 r = p.1 := by
  intro p hp
  unfold e4WordsOK at h
  have h' := List.all_eq_true.1 h p hp
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
  exact h'

end CFSG.KD.SmithD6E4

end
