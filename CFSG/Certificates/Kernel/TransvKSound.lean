module

public import Certificates.Data.Kernel.TransvK

public section

namespace CFSG.KC.TransvK

open CFSG.EvenSporadicStandard.ThStd.LocalDataTh

theorem bitZ_eq_iff (a b i : ℕ) : bitZ a i = bitZ b i ↔ a.testBit i = b.testBit i := by
  unfold bitZ
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem codeVec_eq_iff {a b : ℕ} (ha : a < 16) (hb : b < 16) :
    codeVec 4 a = codeVec 4 b ↔ a = b := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 4
    · exact (bitZ_eq_iff a b i).mp (congrFun h ⟨i, hi⟩)
    · have h16 : (16 : ℕ) ≤ 2 ^ i := by
        have h4 : (2 : ℕ) ^ 4 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
        exact h4
      rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]
  · rintro rfl
    rfl

theorem applyCols_eq (a b c d v : ℕ) : applyCols 4 [a, b, c, d] v = appK a b c d v := rfl

theorem xor16 {x y : ℕ} (hx : x < 16) (hy : y < 16) : x ^^^ y < 16 :=
  Nat.xor_lt_two_pow (n := 4) hx hy

theorem appK_lt {a b c d : ℕ} (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) (v : ℕ) :
    appK a b c d v < 16 := by
  have key : ∀ (p : Prop) [Decidable p] (x y : ℕ), x < 16 → y < 16 → (if p then x else y) < 16 :=
    fun p _ x y hx hy => by split <;> assumption
  have h0 : (0 : ℕ) < 16 := by decide
  have h0' := key (v.testBit 0 = true) _ _ (xor16 h0 ha) h0
  have h1' := key (v.testBit 1 = true) _ _ (xor16 h0' hb) h0'
  have h2' := key (v.testBit 2 = true) _ _ (xor16 h1' hc) h1'
  exact key (v.testBit 3 = true) _ _ (xor16 h2' hd) h2'

theorem fixedCount_eq {a b c d : ℕ} (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) :
    fixedCount [a, b, c, d] = fixedCountK a b c d := by
  unfold fixedCount fixedCountK
  congr 1
  apply List.filter_congr
  intro v hv
  have hv' := List.mem_range.mp hv
  rw [applyCols_eq, Bool.eq_iff_iff, decide_eq_true_iff, Nat.beq_eq,
    codeVec_eq_iff (appK_lt ha hb hc hd v) hv']

theorem TFacts_of (h : ∀ a, a < 16 → TFactsA a = true) : TFacts = true := by
  unfold TFacts
  rw [List.all_eq_true]
  intro cs hcs
  unfold allMat4 at hcs
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hcs
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := hcs
  have hA := h a ha
  unfold TFactsA at hA
  simp only [List.all_eq_true, List.mem_range] at hA
  have hl := hA b hb c hc d hd
  unfold tLeafK at hl
  rw [fixedCount_eq ha hb hc hd]
  exact hl

end CFSG.KC.TransvK
