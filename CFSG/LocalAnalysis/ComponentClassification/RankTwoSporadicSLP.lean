module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def slpStep (n : ℕ) (regs : Array (Array ℕ)) (ij : ℕ × ℕ) : Array (Array ℕ) :=
  regs.push (compA n regs[ij.1]! regs[ij.2]!)

@[expose] def slpRegs (n : ℕ) (gens : Array (Array ℕ)) (prog : List (ℕ × ℕ)) :
    Array (Array ℕ) :=
  prog.foldl (slpStep n) (gens ++ gens.map (invCand n))

@[expose] def slpIdxOK : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | k, ij :: l => decide (ij.1 < k) && decide (ij.2 < k) && slpIdxOK (k + 1) l

@[expose] def slpOK (n : ℕ) (gens : Array (Array ℕ)) (prog : List (ℕ × ℕ)) : Bool :=
  (allLt gens.size fun k => validA n gens[k]!) && slpIdxOK (2 * gens.size) prog

@[expose] def regIndex (n : ℕ) (ps : List ℕ) (regs : Array (Array ℕ)) : Std.HashMap ℕ ℕ :=
  (List.range regs.size).foldl (fun m k => m.insert (keyA n ps regs[k]!) k) ∅

@[expose] def inRegs (n : ℕ) (ps : List ℕ) (regs : Array (Array ℕ)) (idx : Std.HashMap ℕ ℕ)
    (a : Array ℕ) : Bool :=
  match idx.get? (keyA n ps a) with
  | some k => decide (k < regs.size) && eqA n a regs[k]!
  | none => false

@[expose] def decodePairs (s : String) : List (ℕ × ℕ) :=
  let t := decodeNats s
  (List.range (t.size / 2)).map fun k => (t[2 * k]!, t[2 * k + 1]!)

section Soundness

variable {n : ℕ}

theorem getElem!_push_of_lt {α : Type*} [Inhabited α] {a : Array α} {x : α} {k : ℕ}
    (hk : k < a.size) : (a.push x)[k]! = a[k]! := by
  rw [getElem!_pos (a.push x) k (by rw [Array.size_push]; omega), getElem!_pos a k hk,
    Array.getElem_push_lt hk]

theorem getElem!_push_size {α : Type*} [Inhabited α] {a : Array α} {x : α} :
    (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by rw [Array.size_push]; omega), Array.getElem_push_eq]

theorem rep_foldl_slpStep {H : Subgroup (Equiv.Perm (Fin n))} :
    ∀ (prog : List (ℕ × ℕ)) (regs : Array (Array ℕ)), slpIdxOK regs.size prog = true →
      (∀ k < regs.size, ∃ g ∈ H, Rep n regs[k]! g) →
      ∀ k < (prog.foldl (slpStep n) regs).size,
        ∃ g ∈ H, Rep n (prog.foldl (slpStep n) regs)[k]! g
  | [], regs, _, h => h
  | ij :: l, regs, hok, h => by
    simp only [slpIdxOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hi, hj⟩, hl⟩ := hok
    refine rep_foldl_slpStep l (slpStep n regs ij) (by simpa [slpStep] using hl) ?_
    intro k hk
    simp only [slpStep, Array.size_push] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [slpStep, getElem!_push_of_lt hk]
      exact h k hk
    · obtain ⟨g₁, hg₁, hr₁⟩ := h _ hi
      obtain ⟨g₂, hg₂, hr₂⟩ := h _ hj
      refine ⟨g₁ * g₂, H.mul_mem hg₁ hg₂, ?_⟩
      rw [slpStep, getElem!_push_size]
      exact rep_compA hr₁ hr₂

theorem rep_slpRegs {gens : Array (Array ℕ)} {prog : List (ℕ × ℕ)}
    (h : slpOK n gens prog = true) :
    ∀ k < (slpRegs n gens prog).size,
      ∃ g ∈ closure (permsA n gens), Rep n (slpRegs n gens prog)[k]! g := by
  simp only [slpOK, Bool.and_eq_true] at h
  obtain ⟨hv, hp⟩ := h
  have hval : ∀ k < gens.size, validA n gens[k]! = true := fun k hk => allLt_spec hv hk
  apply rep_foldl_slpStep
  · simpa [two_mul] using hp
  · intro k hk
    simp only [Array.size_append, Array.size_map] at hk
    by_cases hk' : k < gens.size
    · have he : (gens ++ gens.map (invCand n))[k]! = gens[k]! := by
        rw [getElem!_pos _ k (by simp; omega), getElem!_pos gens k hk',
          Array.getElem_append_left hk']
      rw [he]
      exact ⟨_, subset_closure (mem_permsA hk'), rep_of_validA (hval k hk')⟩
    · have hk2 : k - gens.size < gens.size := by omega
      have he : (gens ++ gens.map (invCand n))[k]! = invCand n gens[k - gens.size]! := by
        rw [getElem!_pos _ k (by simp; omega), getElem!_pos gens (k - gens.size) hk2,
          Array.getElem_append_right (by omega)]
        simp
      rw [he]
      exact ⟨_, inv_mem (subset_closure (mem_permsA hk2)), rep_inv_of_validA (hval _ hk2)⟩

theorem mem_of_inRegs {ps : List ℕ} {regs : Array (Array ℕ)} {idx : Std.HashMap ℕ ℕ}
    {a : Array ℕ} (h : inRegs n ps regs idx a = true) :
    ∃ k < regs.size, eqA n a regs[k]! = true := by
  unfold inRegs at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨_, h.1, h.2⟩
  · exact absurd h (by decide)

theorem mem_closure_of_inRegs {gens : Array (Array ℕ)} {prog : List (ℕ × ℕ)} {ps : List ℕ}
    {idx : Std.HashMap ℕ ℕ} (hslp : slpOK n gens prog = true) {a : Array ℕ}
    (hv : validA n a = true) (h : inRegs n ps (slpRegs n gens prog) idx a = true) :
    permOfArr n a ∈ closure (permsA n gens) := by
  obtain ⟨k, hk, he⟩ := mem_of_inRegs h
  obtain ⟨g, hg, hr⟩ := rep_slpRegs hslp k hk
  rw [eq_of_eqA (rep_of_validA hv) hr he]
  exact hg

end Soundness

end CFSG.ComponentClassification.RankTwoSporadic.Cert
