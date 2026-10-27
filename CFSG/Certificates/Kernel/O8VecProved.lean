module

public import Certificates.Data.Kernel.O8.EnumK
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitFix

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.N3Split

private theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

private theorem testBit_orN (f : ℕ → ℕ) (p : ℕ) : ∀ n,
    (orN n f).testBit p = (List.range n).any fun i => (f i).testBit p
  | 0 => by
    have e : orN 0 f = 0 := rfl
    rw [e]
    simp
  | n + 1 => by
    have e : orN (n + 1) f = f n ||| orN n f := rfl
    rw [e, Nat.testBit_or, testBit_orN f p n, List.range_succ, List.any_append]
    simp [Bool.or_comm]

private theorem sumN_succ (n : ℕ) (f : ℕ → ℕ) : sumN (n + 1) f = f n + sumN n f := rfl

private theorem popc_mod_two (X : ℕ) : ∀ w,
    popc w X % 2 = (xorFold w fun j => X.testBit j).toNat
  | 0 => by simp [popc, sumN, xorFold]
  | w + 1 => by
    have e : popc (w + 1) X = ((X >>> w) &&& 1) + popc w X := sumN_succ w _
    rw [e, xorFold_succ, Nat.add_mod, popc_mod_two X w, Nat.and_one_is_mod]
    have hb : X.testBit w = decide ((X >>> w) % 2 = 1) := by
      rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
    rw [hb]
    generalize xorFold w (fun j => X.testBit j) = b
    rcases Nat.mod_two_eq_zero_or_one (X >>> w) with h | h <;> cases b <;> simp [h]

private theorem testBit_toNat2 (b : Bool) (m : ℕ) : b.toNat.testBit m = (b && decide (m = 0)) := by
  cases b
  · simp
  · cases m <;> simp [Nat.testBit_succ]

private theorem testBit_rowsOf'(a i r : ℕ) (hi : i < 12) :
    ((rowsOf a).getD i 0).testBit r = (decide (r < 12) && a.testBit (12 * i + r)) := by
  have e : (rowsOf a).getD i 0 = (a >>> (12 * i)) % 2 ^ 12 := by
    simp [rowsOf, Array.getD_eq_getD_getElem?, hi]
  rw [e, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

private theorem testBit_row12' (b l r : ℕ) :
    (row12 b l).testBit r = (decide (r < 12) && b.testBit (12 * l + r)) := by
  unfold row12 fget
  have e : maskN 12 = 2 ^ 12 - 1 := by decide
  change ((b >>> (l * 12)) &&& maskN 12).testBit r = _
  rw [e, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, mul_comm l]
  cases decide (r < 12) <;> simp

private theorem xorFold_congr' {k : ℕ} {f g : ℕ → Bool} (h : ∀ l < k, f l = g l) :
    xorFold k f = xorFold k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [xorFold_succ, xorFold_succ, ih (fun l hl => h l (by omega)), h k (by omega)]

theorem mulVecK_eq_proved (k v : ℕ) : mulVecK k v = mulVec12K k v := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [mulVecK, bmulVec, testBit_bitsOf]
  unfold mulVec12K
  rw [strictN_eq, strictN_eq, testBit_orN]
  have key : ∀ i, (((popc 12 ((row12 k i).land v)).mod 2).shiftLeft i).testBit p =
      (decide (i = p) && xorFold 12 fun j => (row12 k i).testBit j && v.testBit j) := by
    intro i
    change ((popc 12 (row12 k i &&& v) % 2) <<< i).testBit p = _
    rw [Nat.testBit_shiftLeft, popc_mod_two, testBit_toNat2]
    simp only [Nat.testBit_and]
    generalize xorFold 12 (fun j => (row12 k i).testBit j && v.testBit j) = b
    by_cases h : i = p
    · subst h
      cases b <;> simp
    · cases b
      · simp
      · simp [h]
        omega
  simp only [key]
  by_cases hp : p < 12
  · have hany : ((List.range 12).any fun i =>
        decide (i = p) && xorFold 12 fun j => (row12 k i).testBit j && v.testBit j) =
        xorFold 12 fun j => (row12 k p).testBit j && v.testBit j := by
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨i, _, rfl, h⟩
        exact h
      · intro h
        exact ⟨p, hp, rfl, h⟩
    rw [hany]
    simp only [hp, decide_true, Bool.true_and]
    apply xorFold_congr'
    intro j hj
    rw [testBit_rowsOf' k p j hp, testBit_row12']
  · have hany : ((List.range 12).any fun i =>
        decide (i = p) && xorFold 12 fun j => (row12 k i).testBit j && v.testBit j) = false := by
      apply Bool.eq_false_iff.2
      intro h
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨i, hi, h1, _⟩ := h
      omega
    rw [hany]
    simp [hp]

private theorem card_filter_range' (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.range n).filter p).card = ((List.range n).filter fun i => decide (p i)).length := by
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]

private theorem length_filter_sumN (q : ℕ → Bool) : ∀ n,
    ((List.range n).filter q).length = sumN n fun v => Bool.rec (motive := fun _ => ℕ) 0 1 (q v)
  | 0 => rfl
  | n + 1 => by
    rw [sumN_succ, ← length_filter_sumN q n, List.range_succ, List.filter_append,
      List.length_append]
    cases h : q n <;> simp [h, Nat.add_comm]

theorem fixCount_eq_proved (k : ℕ) :
    fixCount k = sumN 4096 fun v => nIf(Nat.beq (mulVec12K k v) v, 1, 0) := by
  rw [fixCount, card_filter_range', length_filter_sumN]
  congr 1
  funext v
  rw [mulVecK_eq_proved]
  cases h : Nat.beq (mulVec12K k v) v
  · have : mulVec12K k v ≠ v := fun he => by simp [he] at h
    simp [this]
  · have : mulVec12K k v = v := Nat.eq_of_beq_eq_true h
    simp [this]

theorem fixVecs_eq_proved (k : ℕ) :
    fixVecs k = (List.range 4096).filter fun v => mulVec12K k v == v := by
  unfold fixVecs
  apply List.filter_congr
  intro v hv
  have hv' : v < 2 ^ 12 := by
    have := List.mem_range.1 hv
    norm_num
    omega
  rw [imgTab_getD k 12 v hv', mulVecK_eq_proved]

end CFSG.KC.O8

end
