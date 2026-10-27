module

public import Certificates.Data.Kernel.WeylE8.Cent
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCentData
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.LocalCompE8Sound

public section

namespace CFSG.KLC.E8

open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl

theorem bit_eq (x k : Nat) : (x >>> k &&& 1) = if x.testBit k then 1 else 0 := by
  rw [Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (x >>> k) with h | h <;>
    simp [Nat.testBit, Nat.and_one_is_mod, Nat.one_and_eq_mod_two, h]

theorem sumN_eq (n : Nat) (f : Nat → Nat) : sumN n f = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact Nat.add_comm _ _

theorem two_le_pop8 {x k l : Nat} (hk : k < 8) (hl : l < 8) (hkl : k ≠ l) (h1 : x.testBit k = true)
    (h2 : x.testBit l = true) : 2 ≤ pop8 x := by
  have e : ∀ j, Nat.land (Nat.shiftRight x j) 1 = if x.testBit j then 1 else 0 := fun j => bit_eq x j
  rw [pop8, sumN_eq]
  simp only [e]
  have hsub : ({k, l} : Finset Nat) ⊆ Finset.range 8 := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> simpa using ‹_›
  calc 2 = ∑ j ∈ ({k, l} : Finset Nat), (if x.testBit j then 1 else 0) := by
        rw [Finset.sum_pair hkl, h1, h2]; rfl
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bIf_eq (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = (if c then t else e) := by
  cases c <;> rfl

theorem pair2K_spec (h : pair2K = true) : ∀ a < 256, pop8 a = 2 → ∀ b < 256, pop8 b = 2 →
    pop8 (a ^^^ b) = 2 → pop8 (a &&& b) ≤ 1 := by
  intro a ha hpa b hb hpb hpab
  have hpab' : pop8 (Nat.xor a b) = 2 := hpab
  have k := CFSG.KS.allN_spec h a ha
  simp only [bIf_eq, Nat.beq_eq, hpa, if_true] at k
  have k2 := CFSG.KS.allN_spec k b hb
  simp only [bIf_eq, bAnd_eq, Nat.beq_eq, hpb, hpab', Bool.and_self, if_true, decide_true,
    Nat.ble_eq] at k2
  exact k2

theorem triple_spec (h : tripleK = true) : ∀ a < 256, pop8 a = 2 → ∀ b < 256, pop8 b = 2 →
    pop8 (a ^^^ b) = 2 → ∀ c < 256, pop8 c = 2 → pop8 (a ^^^ c) = 2 → pop8 (b ^^^ c) = 2 →
    c ≠ a ^^^ b → 0 < a &&& (b &&& c) := by
  intro a ha hpa b hb hpb hpab c hc hpc hpac hpbc hne
  have hpab' : pop8 (Nat.xor a b) = 2 := hpab
  have hpac' : pop8 (Nat.xor a c) = 2 := hpac
  have hpbc' : pop8 (Nat.xor b c) = 2 := hpbc
  have hne' : Nat.beq c (Nat.xor a b) = false :=
    Bool.eq_false_iff.2 (fun e => hne (Nat.eq_of_beq_eq_true e))
  have hn : notB' false = true := rfl
  have k := CFSG.KS.allN_spec h a ha
  simp only [bIf_eq, Nat.beq_eq, hpa, if_true] at k
  have k2 := CFSG.KS.allN_spec k b hb
  simp only [bIf_eq, bAnd_eq, Nat.beq_eq, hpb, hpab', Bool.and_self, if_true, decide_true] at k2
  have k3 := CFSG.KS.allN_spec k2 c hc
  simp only [bIf_eq, bAnd_eq, hpc, hpac', hpbc', hne', hn, Nat.beq_eq, Bool.and_self, if_true,
    decide_true, Bool.true_and, Nat.blt_eq] at k3
  exact k3

theorem exists_common_bit {a b c : Nat} (ha : a < 256) (h : 0 < a &&& (b &&& c)) :
    ∃ k < 8, a.testBit k = true ∧ b.testBit k = true ∧ c.testBit k = true := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (Nat.pos_iff_ne_zero.1 h)
  simp only [Nat.testBit_and, Bool.and_eq_true] at hi
  refine ⟨i, ?_, hi.1, hi.2.1, hi.2.2⟩
  by_contra hge
  have : a < 2 ^ i := Nat.lt_of_lt_of_le ha (by
    have : 8 ≤ i := by omega
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) this)
  rw [Nat.testBit_eq_false_of_lt this] at hi
  exact Bool.false_ne_true hi.1

theorem tripleK_sound (h : tripleK = true) : tripleCheck = true := by
  have hs := triple_spec h
  simp only [tripleCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_imp, beq_iff_eq, List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_eq_false_iff_ne, bne_eq_false_iff_eq]
  intro a ha
  by_cases hpa : framePop a = 2
  · right
    intro b hb
    by_cases hpb : framePop b = 2 ∧ framePop (a ^^^ b) = 2
    · right
      intro c hc
      by_cases hpc : framePop c = 2 ∧ framePop (a ^^^ c) = 2 ∧ framePop (b ^^^ c) = 2 ∧ c ≠ a ^^^ b
      · right
        simp only [← pop8_eq] at hpa hpb hpc
        obtain ⟨k, hk, h1, h2, h3⟩ := exists_common_bit ha
          (hs a ha hpa b hb hpb.1 hpb.2 c hc hpc.1 hpc.2.1 hpc.2.2.1 hpc.2.2.2)
        exact ⟨k, hk, ⟨h1, h2⟩, h3⟩
      · left
        intro h1
        by_contra hne
        exact hpc ⟨h1.1.1, h1.1.2, h1.2, hne⟩
    · left
      intro h1
      exact fun h2 => hpb ⟨h1, h2⟩
  · exact Or.inl hpa

theorem pair2K_sound (h : pair2K = true) : pairCheck2 = true := by
  have hs := pair2K_spec h
  simp only [pairCheck2, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_imp, beq_iff_eq, Bool.and_eq_true, beq_eq_false_iff_ne, ne_eq]
  intro a ha
  by_cases hpa : framePop a = 2
  · right
    intro b hb
    by_cases hpb : framePop b = 2 ∧ framePop (a ^^^ b) = 2
    · right
      intro k hk l hl
      by_cases hkl : k = l
      · exact Or.inr hkl
      · left
        intro habl
        obtain ⟨⟨hak, hbk⟩, hal⟩ := habl
        cases hbl : b.testBit l
        · rfl
        exfalso
        have hle := hs a ha (by rw [pop8_eq]; exact hpa) b hb (by rw [pop8_eq]; exact hpb.1)
          (by rw [pop8_eq]; exact hpb.2)
        have h2 := two_le_pop8 (x := a &&& b) hk hl hkl (by simp [Nat.testBit_and, hak, hbk])
          (by simp [Nat.testBit_and, hal, hbl])
        omega
    · left
      intro h1
      exact fun h2 => hpb ⟨h1, h2⟩
  · exact Or.inl hpa

end CFSG.KLC.E8

end
