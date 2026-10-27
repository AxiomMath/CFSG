module

public import CFSG.Certificates.Kernel.O8EnumDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitNative

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.N3Split CFSG.KLie.CT

private theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

private theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero =>
    constructor
    · intro _ i hi
      omega
    · intro _
      rfl
  | succ n ih =>
    have e : allN (n + 1) f = andB (f n) (allN n f) := rfl
    have e2 : ∀ a b : Bool, andB a b = (a && b) := by intro a b; cases a <;> rfl
    rw [e, e2, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (by omega), fun i hi => h i (by omega)⟩

private theorem nbeq_eq (a b : ℕ) : (a == b) = decide (a = b) := by
  rw [Bool.eq_iff_iff]
  simp

private theorem card_filter_range (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.range n).filter p).card = ((List.range n).filter fun i => decide (p i)).length := by
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]

theorem decE_toList_proved (D : Nat → Nat) (m : Nat) :
    (decE D m).keys.toList = (List.range m).map (enKey D) := by
  apply List.ext_getElem
  · simp [decE]
  · intro i h1 h2
    simp [decE]

theorem contains_decE_eq_proved (D : Nat → Nat) (m k : Nat) :
    (decE D m).keys.contains k = !enNotMemK D m k := by
  apply Bool.eq_iff_iff.2
  rw [Array.contains_iff_mem, ← Array.mem_toList_iff, decE_toList_proved, List.mem_map,
    Bool.not_eq_true', enNotMemK]
  constructor
  · rintro ⟨i, hi, rfl⟩
    apply Bool.eq_false_iff.2
    intro h
    have := allN_iff.1 h i (List.mem_range.1 hi)
    simp [notB_eq] at this
  · intro h
    by_contra hne
    apply Bool.eq_false_iff.1 h
    apply allN_iff.2
    intro i hi
    rw [notB_eq, Bool.not_eq_true']
    apply Bool.eq_false_iff.2
    intro he
    exact hne ⟨i, List.mem_range.2 hi, Nat.eq_of_beq_eq_true he⟩

theorem contains_decE_proved {D : Nat → Nat} {m k : Nat} (h : enNotMemK D m k = true) :
    (decE D m).keys.contains k = false := by
  rw [contains_decE_eq_proved, h]
  rfl

theorem commCount_eq_proved (E : Enum) (s : ℕ) : commCount E s =
    ((List.range E.keys.size).filter fun i =>
      mulK (E.keys.getD i 0) s == mulK s (E.keys.getD i 0)).length := by
  rw [commCount, card_filter_range]
  simp only [nbeq_eq]

theorem kerOn_eq_proved (E : Enum) (s : ℕ) (vs : List ℕ) : kerOn E s vs =
    ((List.range E.keys.size).filter fun i =>
      mulK (E.keys.getD i 0) s == mulK s (E.keys.getD i 0) &&
        fixesOn vs (E.keys.getD i 0)).length := by
  rw [kerOn, card_filter_range]
  simp only [nbeq_eq, Bool.decide_and, Bool.decide_eq_true]

theorem candB_false_of_zfix_proved {E : Enum} {s : ℕ} {vs : List ℕ} (hlen : 3 ≤ vs.length)
    (hnd : vs.Nodup) (hfix : vs.all (fun v => decide (v < 4096) && mulVecK s v == v) = true)
    (hall : ((List.range E.keys.size).all fun i =>
      !(mulK (E.keys.getD i 0) s == mulK s (E.keys.getD i 0)) ||
        vs.all fun v => mulVecK (E.keys.getD i 0) v == v) = true) :
    candB E s = false := by
  have hsub : vs ⊆ (fixVecs s).filter fun v =>
      (E.keys.toList.filter fun c => mulK c s == mulK s c).all fun c => mulVecK c v == v := by
    intro v hv
    have hv1 := List.all_eq_true.1 hfix v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv1
    rw [List.mem_filter]
    refine ⟨mem_fixVecs.2 hv1, ?_⟩
    rw [List.all_eq_true]
    intro c hc
    rw [List.mem_filter] at hc
    obtain ⟨hc1, hc2⟩ := hc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc1
    have hi' : i < E.keys.size := by simpa using hi
    have h := List.all_eq_true.1 hall i (List.mem_range.2 hi')
    have hg : E.keys.getD i 0 = E.keys.toList[i] := by
      simp [Array.getD_eq_getD_getElem?, hi']
    rw [hg] at h
    rw [hc2] at h
    simp only [Bool.not_true, Bool.false_or] at h
    exact List.all_eq_true.1 h v hv
  have hle : vs.length ≤ zfixCount E s := (hnd.subperm hsub).length_le
  have h3 : ¬ zfixCount E s ≤ 2 := by omega
  simp [candB, h3]

end CFSG.KC.O8

end
