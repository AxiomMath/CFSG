module

public import CFSG.Certificates.Kernel.Th.S.TsS
public import CFSG.Certificates.Kernel.Th.S.DceS
import CFSG.Certificates.Kernel.DceLoops
public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Loop

private theorem plStrictN (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

private theorem plItems_succ (f : ℕ → Bool) (C S : ℕ) :
    TsS.items f (C + 1) S = Bool.rec (motive := fun _ => ℕ) 0
      (TsS.items f C (S + 1)) (andB (Nat.blt 0 S) (f (S - 1))) := rfl

private theorem plItems_zero_state (f : ℕ → Bool) (C : ℕ) : TsS.items f C 0 = 0 := by
  cases C <;> rfl

private theorem plItems_spec (f : ℕ → Bool) : ∀ (C S : ℕ), TsS.items f C S ≠ 0 →
    TsS.items f C S = S + C ∧ 0 < S ∧ ∀ k < C, f (S - 1 + k) = true := by
  intro C
  induction C with
  | zero =>
    intro S h
    have e : TsS.items f 0 S = S := rfl
    rw [e] at h ⊢
    exact ⟨rfl, Nat.pos_of_ne_zero h, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ C ih =>
    intro S h
    rw [plItems_succ] at h ⊢
    cases hb : andB (Nat.blt 0 S) (f (S - 1))
    · rw [hb] at h
      exact absurd rfl h
    · have et : Bool.rec (motive := fun _ => ℕ) 0 (TsS.items f C (S + 1)) true =
          TsS.items f C (S + 1) := rfl
      rw [hb, et] at h
      rw [et]
      have hb' : Nat.blt 0 S = true ∧ f (S - 1) = true := by
        revert hb
        cases Nat.blt 0 S <;> simp [andB]
      obtain ⟨hlt, hf⟩ := hb'
      have hS : 0 < S := by simpa using hlt
      obtain ⟨e1, -, hk⟩ := ih (S + 1) h
      refine ⟨by rw [e1]; omega, hS, fun k hk' => ?_⟩
      rcases k with _ | k
      · simpa using hf
      · have := hk k (by omega)
        have e2 : S + 1 - 1 + k = S - 1 + (k + 1) := by omega
        rw [e2] at this
        exact this

private theorem plRunItems_zero (f : ℕ → Bool) (cs : List ℕ) : TsS.runItems f cs 0 = 0 := by
  induction cs with
  | nil => rfl
  | cons C cs ih =>
    have e : TsS.runItems f (C :: cs) 0 = TsS.runItems f cs (TsS.items f C 0) := by
      show strictN _ _ = _
      rw [plStrictN]
      rfl
    rw [e, plItems_zero_state]
    exact ih

theorem runItems_spec {f : ℕ → Bool} (cs : List ℕ) {S S' : ℕ} (hS : 0 < S)
    (h : CFSG.KC.Th.TsS.runItems f cs S = S') (h0 : S' ≠ 0) :
    S' = S + cs.sum ∧ ∀ i, S - 1 ≤ i → i < S' - 1 → f i = true := by
  subst h
  induction cs generalizing S with
  | nil =>
    have e : TsS.runItems f [] S = S := rfl
    rw [e]
    exact ⟨by simp, fun i hi hi' => by omega⟩
  | cons C cs ih =>
    have e : TsS.runItems f (C :: cs) S = TsS.runItems f cs (TsS.items f C S) := by
      show strictN _ _ = _
      rw [plStrictN]
      rfl
    rw [e] at h0 ⊢
    have h1 : TsS.items f C S ≠ 0 := by
      intro h1
      rw [h1, plRunItems_zero] at h0
      exact h0 rfl
    obtain ⟨hE, -, hf⟩ := plItems_spec f C S h1
    obtain ⟨hs, hfi⟩ := ih (S := TsS.items f C S) (by omega) h0
    refine ⟨by rw [hs, hE, List.sum_cons]; omega, fun i hi hi' => ?_⟩
    by_cases hlt : i < S + C - 1
    · have := hf (i - (S - 1)) (by omega)
      have e2 : S - 1 + (i - (S - 1)) = i := by omega
      rw [e2] at this
      exact this
    · exact hfi i (by omega) (by omega)

private theorem plRunSorted_eq (get : ℕ → ℕ) (qb m : ℕ) (Cs : List ℕ) (S : ℕ) :
    CFSG.KC.Th.DceS.runSorted get qb m Cs S = CFSG.Certificates.DceLoop.sortRun get qb m Cs S :=
  rfl

theorem runSorted_inj {get : ℕ → ℕ} {qb m : ℕ} {cs : List ℕ} {sf : ℕ}
    (hrun : CFSG.KC.Th.DceS.runSorted get qb m cs 1 = sf)
    (hcount : CFSG.KC.Th.DceS.sortedCount sf = m) (hm : 0 < m) (hm' : m + 2 < 2 ^ 20) :
    ∀ i < m, ∀ j < m, i < j → get i ≠ get j := by
  clear hm hm'
  obtain ⟨-, hinj⟩ := CFSG.Certificates.DceLoop.sortRun_spec (plRunSorted_eq _ _ _ _ _ ▸ hrun)
    hcount
  intro i hi j hj hij heq
  have := hinj i hi j hj heq
  omega

end CFSG.KC.Th.Spec

end
