module

public import Certificates.Data.Kernel.SporSch.RuDist
public import CFSG.Certificates.Kernel.SporSch.RuImgSound
public import Certificates.Data.GMS78RuB1Check

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.RuSchreier.RuB1

theorem distNL_cons (x : Nat) (xs : List Nat) :
    distNL (x :: xs) = if x ∈ xs then distNL xs else distNL xs + 1 := by
  change Bool.rec (motive := fun _ => Nat) (Nat.succ (distNL xs)) (distNL xs) (memNL x xs) = _
  by_cases h : x ∈ xs
  · rw [memNL_iff.2 h, ite_eq_left h]
  · have : memNL x xs = false := by
      cases e : memNL x xs
      · rfl
      · exact absurd (memNL_iff.1 e) h
    rw [this, ite_eq_right h]

theorem pickBy_keys {α : Type} {r : α → α → Bool} {key : α → Nat} :
    ∀ {l : List α}, (∀ p ∈ l, ∀ p' ∈ l, r p p' = Nat.beq (key p) (key p')) →
      ∀ k, k ∈ (pickBy r l).map key ↔ k ∈ l.map key
  | [], _, k => by simp [pickBy]
  | a :: l, h, k => by
    have hl : ∀ p ∈ l, ∀ p' ∈ l, r p p' = Nat.beq (key p) (key p') :=
      fun p hp p' hp' => h p (List.mem_cons_of_mem _ hp) p' (List.mem_cons_of_mem _ hp')
    have ih := pickBy_keys hl
    have hsub : ∀ q ∈ pickBy r l, q ∈ l := pickBy_sub
    unfold pickBy
    dsimp only
    by_cases hp : (pickBy r l).any (r a) = true
    · rw [ite_eq_left hp]
      obtain ⟨q, hq, hrq⟩ := List.any_eq_true.1 hp
      rw [h a List.mem_cons_self q (List.mem_cons_of_mem _ (hsub q hq))] at hrq
      have e := Nat.eq_of_beq_eq_true hrq
      simp only [List.map_cons, List.mem_cons]
      rw [ih]
      constructor
      · exact Or.inr
      · rintro (rfl | hk)
        · rw [e, ← ih]
          exact List.mem_map_of_mem hq
        · exact hk
    · rw [ite_eq_right hp]
      simp only [List.map_cons, List.mem_cons]
      rw [ih]
where
  pickBy_sub {α : Type} {r : α → α → Bool} : ∀ {l : List α}, ∀ q ∈ pickBy r l, q ∈ l
    | [], q, hq => by simp [pickBy] at hq
    | a :: l, q, hq => by
      unfold pickBy at hq
      dsimp only at hq
      by_cases hp : (pickBy r l).any (r a) = true
      · rw [ite_eq_left hp] at hq
        exact List.mem_cons_of_mem _ (pickBy_sub q hq)
      · rw [ite_eq_right hp] at hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (pickBy_sub q hq)

theorem pickBy_length {α : Type} {r : α → α → Bool} {key : α → Nat} :
    ∀ {l : List α}, (∀ p ∈ l, ∀ p' ∈ l, r p p' = Nat.beq (key p) (key p')) →
      (pickBy r l).length = distNL (l.map key)
  | [], _ => rfl
  | a :: l, h => by
    have hl : ∀ p ∈ l, ∀ p' ∈ l, r p p' = Nat.beq (key p) (key p') :=
      fun p hp p' hp' => h p (List.mem_cons_of_mem _ hp) p' (List.mem_cons_of_mem _ hp')
    rw [List.map_cons, distNL_cons]
    unfold pickBy
    dsimp only
    have hiff : (pickBy r l).any (r a) = true ↔ key a ∈ l.map key := by
      rw [List.any_eq_true, ← pickBy_keys hl]
      constructor
      · rintro ⟨q, hq, hrq⟩
        rw [h a List.mem_cons_self q (List.mem_cons_of_mem _ (pickBy_keys.pickBy_sub q hq))]
          at hrq
        rw [Nat.eq_of_beq_eq_true hrq]
        exact List.mem_map_of_mem hq
      · intro hk
        obtain ⟨q, hq, e⟩ := List.mem_map.1 hk
        refine ⟨q, hq, ?_⟩
        rw [h a List.mem_cons_self q (List.mem_cons_of_mem _ (pickBy_keys.pickBy_sub q hq)), e]
        exact Nat.beq_refl _
    by_cases hk : key a ∈ l.map key
    · rw [ite_eq_left (hiff.2 hk), ite_eq_left hk]
      exact pickBy_length hl
    · rw [ite_eq_right (fun e => hk (hiff.1 e)), ite_eq_right hk, List.length_cons,
        pickBy_length hl]

end CFSG.KS.SporSch

end
