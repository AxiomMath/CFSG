module

public import Certificates.Data.Kernel.Misc.YamakiRepF
public import CFSG.Certificates.Kernel.Misc.PermClosSound

public section

namespace CFSG.KC.YamakiRepF

open CFSG.KD.YamakiRepF CFSG.KD.YamakiRep CFSG.KD.BfsK CFSG.KC.Loop

variable {R : ℕ → ℕ} {st : ℕ → ℕ → ℕ} {o n : ℕ}

theorem strictY_eq (y : ℕ) (k : ℕ → Bool) : strictY y k = k y := by
  cases y <;> rfl

theorem recAndY_iff (f : ℕ → Bool) : ∀ m : ℕ,
    Nat.rec (motive := fun _ => Bool) true (fun i acc => bAnd(f i, acc)) m = true ↔
      ∀ i < m, f i = true
  | 0 => by simp
  | m + 1 => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true (fun i acc => bAnd(f i, acc)) m) (f m) = true ↔ _
    cases e : f m
    · constructor
      · intro h
        exact (Bool.false_ne_true h).elim
      · intro h
        exact absurd (h m (by omega)) (by rw [e]; exact Bool.false_ne_true)
    · change Nat.rec (motive := fun _ => Bool) true (fun i acc => bAnd(f i, acc)) m = true ↔ _
      rw [recAndY_iff f m]
      constructor
      · intro h i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h i hi
        · exact e
      · intro h i hi
        exact h i (by omega)

theorem allBelow_two {f : ℕ → Bool} (h0 : f 0 = true) (h1 : f 1 = true) :
    allBelow 2 1 f = true := by
  unfold allBelow
  refine (recAndY_iff _ 1).2 fun h' _ => (recAndY_iff (fun l => (fun i =>
    bIf(Nat.blt i 2, f i, true)) (Nat.add (Nat.shiftLeft h' 6) l)) 64).2 fun l _ => ?_
  dsimp only
  by_cases hb : Nat.blt (Nat.add (Nat.shiftLeft h' 6) l) 2 = true
  · rw [hb]
    have hi := Nat.blt_eq.mp hb
    rcases (by omega : Nat.add (Nat.shiftLeft h' 6) l = 0 ∨ Nat.add (Nat.shiftLeft h' 6) l = 1)
      with e | e
    · rw [e]
      exact h0
    · rw [e]
      exact h1
  · rw [Bool.eq_false_iff.2 hb]

theorem stepAt_of_stepF {t s i : ℕ} (hd : Nat.div i 2 = t) (hm : Nat.mod i 2 = s)
    (h : stepF R st o n t s (recX R o t) (recC R o 2 i) (recPOS R o 2 i)
      (recC R o 2 (Nat.succ i)) = true) :
    stepAt st (recX R o) (recF R o 0) (recF R o 1) (recC R o 2) (recPOS R o 2) n 2 i = true := by
  unfold stepAt
  rw [hd, hm]
  exact h

theorem recF_at {i t f s : ℕ} (hd : Nat.div i 2 = t) (hm : Nat.mod i 2 = s) :
    recF R o (Nat.add f s) t = fld (R (Nat.add o t)) (Nat.add f s) ∧
      recC R o 2 i = fld (R (Nat.add o t)) (Nat.add 4 s) ∧
      recPOS R o 2 i = fld (R (Nat.add o t)) (Nat.add 6 s) := by
  refine ⟨rfl, ?_, ?_⟩
  · unfold recC
    rw [hd, hm]
    rfl
  · unfold recPOS
    rw [hd, hm]
    rfl

theorem rowK_of_rowF {t : ℕ} (h : rowF R st o n t = true) : rowK R st o n 2 t = true := by
  unfold rowF rowB at h
  simp only [strictY_eq] at h
  obtain ⟨⟨⟨hb, h0⟩, h1⟩, hs⟩ := (Bool.and_eq_true_iff.1 h).imp_left fun h =>
    (Bool.and_eq_true_iff.1 h).imp_left fun h => Bool.and_eq_true_iff.1 h
  have d0 : Nat.div (Nat.add (Nat.mul t 2) 0) 2 = t := by
    change (t * 2 + 0) / 2 = t
    omega
  have m0 : Nat.mod (Nat.add (Nat.mul t 2) 0) 2 = 0 := by
    change (t * 2 + 0) % 2 = 0
    omega
  have d0' : Nat.div (Nat.succ (Nat.add (Nat.mul t 2) 0)) 2 = t := by
    change (t * 2 + 0 + 1) / 2 = t
    omega
  have m0' : Nat.mod (Nat.succ (Nat.add (Nat.mul t 2) 0)) 2 = 1 := by
    change (t * 2 + 0 + 1) % 2 = 1
    omega
  have d1 : Nat.div (Nat.add (Nat.mul t 2) 1) 2 = t := by
    change (t * 2 + 1) / 2 = t
    omega
  have m1 : Nat.mod (Nat.add (Nat.mul t 2) 1) 2 = 1 := by
    change (t * 2 + 1) % 2 = 1
    omega
  have d1' : Nat.div (Nat.succ (Nat.add (Nat.mul t 2) 1)) 2 = Nat.succ t := by
    change (t * 2 + 1 + 1) / 2 = t + 1
    omega
  have m1' : Nat.mod (Nat.succ (Nat.add (Nat.mul t 2) 1)) 2 = 0 := by
    change (t * 2 + 1 + 1) % 2 = 0
    omega
  unfold rowK
  rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff]
  refine ⟨⟨hb, allBelow_two ?_ ?_⟩, hs⟩
  · refine stepAt_of_stepF d0 m0 ?_
    rw [(recF_at (f := 0) d0 m0).2.1, (recF_at (f := 0) d0 m0).2.2, (recF_at (f := 0) d0' m0').2.1]
    exact h0
  · refine stepAt_of_stepF d1 m1 ?_
    rw [(recF_at (f := 0) d1 m1).2.1, (recF_at (f := 0) d1 m1).2.2, (recF_at (f := 0) d1' m1').2.1]
    exact h1

theorem chunkK_of_chunkF {L q : ℕ} (h : chunkF R st o n L q = true) :
    chunkK R st o n 2 L q = true := by
  unfold chunkF at h
  unfold chunkK
  rw [CFSG.KC.Misc.Clos.allR_iff] at h ⊢
  intro t h1 h2
  have e := h t h1 h2
  cases hb : Nat.blt t n
  · rfl
  · rw [hb, cond_true] at e
    rw [cond_true]
    exact rowK_of_rowF e

end CFSG.KC.YamakiRepF

end
