module

public import Certificates.Data.Kernel.SporLatOrb
public import Aesop.BuiltinRules
public import Batteries.Data.List.Lemmas
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto

public section

namespace CFSG.KC.SLOrb

theorem eqL_iff : ∀ a b : List Nat, eqL a b = true ↔ a = b
  | [], [] => by simp [eqL]
  | [], _ :: _ => by simp [eqL]
  | _ :: _, [] => by simp [eqL]
  | x :: as, y :: bs => by
    simp only [eqL, Bool.and_eq_true, Nat.beq_eq, eqL_iff as bs, List.cons.injEq]

theorem lexLt_irrefl : ∀ a : List Nat, lexLt a a = false
  | [] => rfl
  | x :: as => by
    simp only [lexLt, lexLt_irrefl as, Bool.and_false, Bool.or_false]
    exact Bool.eq_false_iff.2 fun h => Nat.lt_irrefl x (cast Nat.blt_eq h)

theorem lexLt_trans : ∀ a b c : List Nat, lexLt a b = true → lexLt b c = true → lexLt a c = true
  | [], [], _, h, _ => by simp [lexLt] at h
  | [], _ :: _, [], _, h => by simp [lexLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [lexLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLt] at h
  | x :: as, y :: bs, z :: cs, h1, h2 => by
    simp only [lexLt, Bool.or_eq_true, Nat.blt_eq, Bool.and_eq_true, Nat.beq_eq] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact Or.inl (by omega)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr ⟨rfl, lexLt_trans as bs cs h1 h2⟩

theorem mem_mergeU (x : List Nat) : ∀ (f : Nat) (A B : List (List Nat)),
    x ∈ mergeU f A B ↔ x ∈ A ∨ x ∈ B
  | 0, A, B => by simp [mergeU]
  | _ + 1, [], B => by simp [mergeU]
  | _ + 1, _ :: _, [] => by simp [mergeU]
  | f + 1, a :: A, b :: B => by
    unfold mergeU
    by_cases h1 : eqL a b = true
    · rw [if_pos h1, List.mem_cons, mem_mergeU x f A B]
      have e := (eqL_iff a b).1 h1
      subst e
      simp only [List.mem_cons]
      tauto
    · rw [if_neg h1]
      by_cases h2 : lexLt a b = true
      · rw [if_pos h2, List.mem_cons, mem_mergeU x f A (b :: B)]
        simp only [List.mem_cons]
        tauto
      · rw [if_neg h2, List.mem_cons, mem_mergeU x f (a :: A) B]
        simp only [List.mem_cons]
        tauto

theorem mem_mergePairs (x : List Nat) : ∀ R : List (List (List Nat)),
    x ∈ (mergePairs R).flatten ↔ x ∈ R.flatten
  | [] => by simp [mergePairs]
  | [A] => by simp [mergePairs]
  | A :: B :: R => by
    simp only [mergePairs, List.flatten_cons, List.mem_append, mem_mergeU, mem_mergePairs x R]
    tauto

theorem mem_mergeAll (x : List Nat) : ∀ (f : Nat) (R : List (List (List Nat))),
    x ∈ mergeAll f R ↔ x ∈ R.flatten
  | _, [] => by simp [mergeAll]
  | _, [A] => by simp [mergeAll]
  | 0, A :: B :: R => Iff.rfl
  | f + 1, A :: B :: R => by
    change x ∈ mergeAll f (mergePairs (A :: B :: R)) ↔ _
    rw [mem_mergeAll x f, mem_mergePairs]

theorem mem_msortU {x : List Nat} {A : List (List Nat)} : x ∈ msortU A ↔ x ∈ A := by
  rw [msortU, mem_mergeAll]
  simp

theorem subS_sound : ∀ (f : Nat) (A B : List (List Nat)), subS f A B = true → ∀ x ∈ A, x ∈ B
  | _, [], _, _, x, hx => by simp at hx
  | _, _ :: _, [], h, _, _ => by simp [subS] at h
  | 0, _ :: _, _ :: _, h, _, _ => by simp [subS] at h
  | f + 1, a :: A, b :: B, h, x, hx => by
    unfold subS at h
    by_cases h1 : eqL a b = true
    · rw [if_pos h1] at h
      have e := (eqL_iff a b).1 h1
      subst e
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (subS_sound f A B h x hx)
    · rw [if_neg h1] at h
      by_cases h2 : lexLt b a = true
      · rw [if_pos h2] at h
        exact List.mem_cons_of_mem _ (subS_sound f (a :: A) B h x hx)
      · rw [if_neg h2] at h
        exact absurd h (by simp)

theorem subL_sound {A B : List (List Nat)} (h : subL A B = true) : ∀ x ∈ A, x ∈ B :=
  subS_sound _ A B h

theorem sortedB_chain : ∀ A : List (List Nat), sortedB A = true →
    List.IsChain (fun a b => lexLt a b = true) A
  | [], _ => List.IsChain.nil
  | [_], _ => List.IsChain.singleton _
  | a :: b :: R, h => by
    simp only [sortedB, Bool.and_eq_true] at h
    exact List.IsChain.cons_cons h.1 (sortedB_chain (b :: R) h.2)

theorem sortedB_nodup {A : List (List Nat)} (h : sortedB A = true) : A.Nodup := by
  have : Trans (fun a b => lexLt a b = true) (fun a b => lexLt a b = true)
      (fun a b => lexLt a b = true) := ⟨fun h1 h2 => lexLt_trans _ _ _ h1 h2⟩
  have hp : A.Pairwise (fun a b => lexLt a b = true) :=
    List.isChain_iff_pairwise.1 (sortedB_chain A h)
  refine hp.imp fun {a b} hab e => ?_
  subst e
  rw [lexLt_irrefl] at hab
  exact absurd hab (by simp)

variable (actF : Nat → List Nat → List Nat) (m : Nat) (Δ : List Nat)

inductive Reach : List Nat → Prop
  | base : Reach Δ
  | step {x : List Nat} {l : Nat} : Reach x → l < m → Reach (actF l x)

theorem mem_imgs {y : List Nat} {A : List (List Nat)} :
    y ∈ imgs actF m A ↔ ∃ x ∈ A, ∃ l < m, y = actF l x := by
  unfold imgs
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨x, hx, l, hl, rfl⟩
    exact ⟨x, hx, l, hl, rfl⟩
  · rintro ⟨x, hx, l, hl, rfl⟩
    exact ⟨x, hx, l, hl, rfl⟩

theorem chainOK_reach : ∀ (A : List (List Nat)) (R : List (List (List Nat))),
    chainOK actF m (A :: R) = true → (∀ x ∈ A, Reach actF m Δ x) →
      ∀ B ∈ A :: R, ∀ x ∈ B, Reach actF m Δ x
  | A, [], _, hA, B, hB, x, hx => by
    rw [List.mem_singleton] at hB
    subst hB
    exact hA x hx
  | A, C :: R, h, hA, B, hB, x, hx => by
    simp only [chainOK, Bool.and_eq_true] at h
    have hC : ∀ y ∈ C, Reach actF m Δ y := by
      intro y hy
      obtain ⟨z, hz, l, hl, rfl⟩ := (mem_imgs actF m).1 (mem_msortU.1 (subL_sound h.1 y hy))
      exact Reach.step (hA z hz) hl
    rcases List.mem_cons.1 hB with rfl | hB
    · exact hA x hx
    · exact chainOK_reach C R h.2 hC B hB x hx

theorem orbChk_sound {s : Nat} (h : orbChk actF m Δ s = true) :
    ∃ O : List (List Nat), O.Nodup ∧ O.length = s ∧ Δ ∈ O ∧
      (∀ x ∈ O, ∀ l < m, actF l x ∈ O) ∧ ∀ x ∈ O, Reach actF m Δ x := by
  unfold orbChk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨_, sortedB_nodup h3, h4, subL_sound h5 Δ List.mem_cons_self, ?_, ?_⟩
  · intro x hx l hl
    exact subL_sound h6 _ (mem_msortU.2 ((mem_imgs actF m).2 ⟨x, hx, l, hl, rfl⟩))
  · intro x hx
    obtain ⟨B, hB, hxB⟩ := List.mem_flatten.1 (mem_msortU.1 hx)
    revert h1 h2 hB
    cases layers actF m (s + 1) [Δ] [Δ] with
    | nil => intro h1; exact absurd h1 (by simp)
    | cons F R =>
      intro h1 h2 hB
      refine chainOK_reach actF m Δ F R h2 (fun y hy => ?_) B hB x hxB
      have := subL_sound h1 y hy
      rw [List.mem_singleton] at this
      rw [this]
      exact Reach.base

end CFSG.KC.SLOrb

end
