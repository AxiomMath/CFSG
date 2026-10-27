module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native

variable {n : ℕ}

theorem regIndex_foldl (ps : List ℕ) (regs : Array (Array ℕ)) : ∀ s,
    (∀ m k, ((List.range s).foldl (fun m k => m.insert (keyA n ps regs[k]!) k)
        (∅ : Std.HashMap ℕ ℕ))[m]? = some k → k < s ∧ keyA n ps regs[k]! = m) ∧
      ∀ j < s, (((List.range s).foldl (fun m k => m.insert (keyA n ps regs[k]!) k)
        (∅ : Std.HashMap ℕ ℕ))[keyA n ps regs[j]!]?).isSome = true
  | 0 => by
    refine ⟨fun m k h => ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    rw [List.range_zero, List.foldl_nil, Std.HashMap.getElem?_empty] at h
    exact absurd h (by simp)
  | s + 1 => by
    obtain ⟨ih1, ih2⟩ := regIndex_foldl ps regs s
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range s).foldl (fun m k => m.insert (keyA n ps regs[k]!) k)
      (∅ : Std.HashMap ℕ ℕ) = M at ih1 ih2
    refine ⟨fun m k h => ?_, fun j hj => ?_⟩
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · next e =>
        rw [beq_iff_eq] at e
        cases h
        exact ⟨Nat.lt_succ_self s, e⟩
      · obtain ⟨hk, e⟩ := ih1 m k h
        exact ⟨by omega, e⟩
    · rw [Std.HashMap.getElem?_insert]
      split
      · rfl
      · exact ih2 j (by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact hj
          · next e => exact absurd (beq_self_eq_true _) e)

theorem regIndex_spec (ps : List ℕ) (regs : Array (Array ℕ)) :
    (∀ m k, (regIndex n ps regs)[m]? = some k → k < regs.size ∧ keyA n ps regs[k]! = m) ∧
      ∀ j < regs.size, ((regIndex n ps regs)[keyA n ps regs[j]!]?).isSome = true :=
  regIndex_foldl ps regs regs.size

theorem inRegs_regIndex {ps : List ℕ} {regs : Array (Array ℕ)} {a : Array ℕ}
    (hex : ∃ j < regs.size, keyA n ps regs[j]! = keyA n ps a)
    (hall : ∀ j < regs.size, keyA n ps regs[j]! = keyA n ps a → eqA n a regs[j]! = true) :
    inRegs n ps regs (regIndex n ps regs) a = true := by
  obtain ⟨h1, h2⟩ := regIndex_spec (n := n) ps regs
  obtain ⟨j, hj, ej⟩ := hex
  have hs := h2 j hj
  rw [ej] at hs
  unfold inRegs
  rw [Std.HashMap.get?_eq_getElem?]
  cases e : (regIndex n ps regs)[keyA n ps a]? with
  | none => rw [e] at hs; exact absurd hs (by simp)
  | some k =>
    obtain ⟨hk, ek⟩ := h1 _ _ e
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hk, hall k hk ek⟩

theorem inRegs_regIndex_of_inj {ps : List ℕ} {regs : Array (Array ℕ)} {a : Array ℕ}
    (hinj : ∀ i < regs.size, ∀ j < regs.size, keyA n ps regs[i]! = keyA n ps regs[j]! → i = j)
    {k : ℕ} (hk : k < regs.size) (hkey : keyA n ps regs[k]! = keyA n ps a)
    (he : eqA n a regs[k]! = true) : inRegs n ps regs (regIndex n ps regs) a = true :=
  inRegs_regIndex ⟨k, hk, hkey⟩ fun j hj e => by
    rw [hinj j hj k hk (e.trans hkey.symm)]
    exact he

end CFSG.ComponentClassification.RankTwoSporadic.Cert

end
