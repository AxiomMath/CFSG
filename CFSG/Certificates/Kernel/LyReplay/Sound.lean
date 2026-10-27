module

public import Certificates.Data.Kernel.LyReplay.Defs

public section

namespace CFSG.KC.LyReplay

open CFSG.Sporadic.Recognition.LyonsSims.LyFinal

theorem letterOfChar_charOfCode (n : Nat) :
    letterOfChar (charOfCode n) = some (letterOfCode n) := by
  unfold charOfCode letterOfCode
  have h : n % 12 < 12 := Nat.mod_lt _ (by decide)
  generalize n % 12 = r at h ⊢
  interval_cases r <;> rfl

theorem parseWord_strOf (w : List Nat) : parseWord (strOf w) = wordOf w := by
  unfold parseWord strOf wordOf
  rw [String.toList_ofList]
  induction w with
  | nil => rfl
  | cons n w ih => simp [letterOfChar_charOfCode, ih]

theorem dist2Replay_of_replayW (cells : List (List (Fin 6 × Bool))) :
    ∀ (ss : List (Nat × Nat × List Nat × List Nat)) (cur : List (Fin 6 × Bool)),
      (∀ s ∈ ss, kindOf s.2.1 = .B → wordOf s.2.2.1 ++ derivInv (wordOf s.2.2.2) ∈ cells) →
      replayW dist2KRules dist2ERules dist2TRules cur ss = true →
      dist2Replay cells cur (ss.map stepOf) = true
  | [], cur, _, h => by simpa [replayW, dist2Replay] using h
  | s :: ss, cur, hB, h => by
    rw [replayW, Bool.and_eq_true] at h
    obtain ⟨hs, hr⟩ := h
    have hok : dist2StepOK cells (stepOf s) = true := by
      unfold dist2StepOK stepOf
      simp only [parseWord_strOf]
      unfold stepOKW at hs
      cases hk : kindOf s.2.1 with
      | B =>
        exact List.any_eq_true.2 ⟨_, hB s List.mem_cons_self hk, beq_self_eq_true _⟩
      | K => rw [hk] at hs; exact hs
      | E => rw [hk] at hs; exact hs
      | T => rw [hk] at hs; exact hs
    rw [List.map_cons, dist2Replay, Bool.and_eq_true]
    refine ⟨hok, ?_⟩
    have e1 : (stepOf s).pos = s.1 := rfl
    have e2 : parseWord (stepOf s).old = wordOf s.2.2.1 := parseWord_strOf _
    have e3 : parseWord (stepOf s).new = wordOf s.2.2.2 := parseWord_strOf _
    rw [e1, e2, e3]
    cases hc : replaceAt cur s.1 (wordOf s.2.2.1) (wordOf s.2.2.2) with
    | none => rw [hc] at hr; exact absurd hr Bool.false_ne_true
    | some cur' =>
      rw [hc] at hr
      exact dist2Replay_of_replayW cells ss cur'
        (fun t ht => hB t (List.mem_cons_of_mem _ ht)) hr

end CFSG.KC.LyReplay

end
