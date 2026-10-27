module

public import Certificates.Data.Kernel.Cert690.Base
public import CFSG.LargeExtraspecial.O62Code

public section

namespace CFSG.KC.C690

open CFSG.LargeExtraspecial.O62

theorem eq_of_testBit_lt' {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : ∀ k < n, a.testBit k = b.testBit k) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < n
  · exact h k hk
  · have hle : 2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hk)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hle)]

theorem oneF_eq : oneF = Code.one := by decide

theorem mul_rep6 (c : ℕ) : c * rep6 = Code.pack c c c c c c := by
  unfold Code.pack rep6
  ring

@[expose] def bit01 (z k : ℕ) : ℕ := if z.testBit k then 1 else 0

theorem bit01_lt (z k : ℕ) : bit01 z k < 64 := by unfold bit01; split <;> omega

theorem testBit_bit01 (z k : ℕ) {i : ℕ} (hi : i < 6) :
    (63 * bit01 z k).testBit i = z.testBit k := by
  unfold bit01
  split
  · rename_i h
    rw [h, mul_one]
    interval_cases i <;> decide
  · rename_i h
    simp only [Bool.not_eq_true] at h
    rw [h, mul_zero, Nat.zero_testBit]

theorem testBit_six (c : ℕ) (hc : c < 64) {j : ℕ} (hj : 6 ≤ j) : c.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj))

theorem testBit_pack6 {c₀ c₁ c₂ c₃ c₄ c₅ : ℕ} (h₀ : c₀ < 64) (h₁ : c₁ < 64) (h₂ : c₂ < 64)
    (h₃ : c₃ < 64) (h₄ : c₄ < 64) {j i : ℕ} (hj : j < 6) (hi : i < 6) :
    (Code.pack c₀ c₁ c₂ c₃ c₄ c₅).testBit (6 * j + i) =
      (![c₀, c₁, c₂, c₃, c₄, c₅] ⟨j, hj⟩).testBit i :=
  Code.testBit_pack h₀ h₁ h₂ h₃ h₄ ⟨j, hj⟩ hi

theorem testBit_rep6 {j i : ℕ} (hj : j < 6) (hi : i < 6) :
    rep6.testBit (6 * j + i) = (i == 0) := by
  interval_cases j <;> interval_cases i <;> decide

theorem testBit_bit01_lo (z k : ℕ) {i : ℕ} (hi : i < 6) :
    (bit01 z k).testBit i = (i == 0 && z.testBit k) := by
  cases h : z.testBit k <;> simp only [bit01, h, Bool.false_eq_true, ↓reduceIte] <;>
    interval_cases i <;> decide

theorem land_rep6 (z : ℕ) : z &&& rep6 = Code.pack (bit01 z 0) (bit01 z 6) (bit01 z 12)
    (bit01 z 18) (bit01 z 24) (bit01 z 30) := by
  have h : ∀ k, bit01 z k < 64 := bit01_lt z
  apply eq_of_testBit_lt' (n := 36)
  · exact lt_of_le_of_lt Nat.and_le_right (by unfold rep6; norm_num)
  · exact Code.pack_lt (h _) (h _) (h _) (h _) (h _) (h _)
  · intro n hn
    obtain ⟨j, i, hj, hi, rfl⟩ : ∃ j i, j < 6 ∧ i < 6 ∧ n = 6 * j + i :=
      ⟨n / 6, n % 6, by omega, by omega, by omega⟩
    rw [Nat.testBit_and, testBit_rep6 hj hi, testBit_pack6 (h _) (h _) (h _) (h _) (h _) hj hi]
    have e : (![bit01 z 0, bit01 z 6, bit01 z 12, bit01 z 18, bit01 z 24, bit01 z 30]
        ⟨j, hj⟩) = bit01 z (6 * j) := by interval_cases j <;> rfl
    rw [e, testBit_bit01_lo _ _ hi]
    by_cases h0 : i = 0
    · subst h0
      simp
    · rw [beq_false_of_ne h0, Bool.and_false, Bool.false_and]

theorem fill_eq (z : ℕ) : (z &&& rep6) * 63 = Code.pack (63 * bit01 z 0) (63 * bit01 z 6)
    (63 * bit01 z 12) (63 * bit01 z 18) (63 * bit01 z 24) (63 * bit01 z 30) := by
  rw [land_rep6]
  unfold Code.pack
  ring

theorem mul63_lt (z k : ℕ) : 63 * bit01 z k < 64 := by
  unfold bit01; split <;> omega

theorem testBit_mtF (a b k : ℕ) {j i : ℕ} (hj : j < 6) (hi : i < 6) :
    (mtF a b k).testBit (6 * j + i) = ((Code.col a k).testBit i && b.testBit (6 * j + k)) := by
  have hc := Code.col_lt a k
  have e1 : Nat.mul (Nat.land (Nat.shiftRight a (Nat.mul 6 k)) 63) rep6 =
      Code.pack (Code.col a k) (Code.col a k) (Code.col a k) (Code.col a k) (Code.col a k)
        (Code.col a k) := mul_rep6 _
  have e2 : Nat.mul (Nat.land (Nat.shiftRight b k) rep6) 63 = _ := fill_eq (b >>> k)
  unfold mtF
  rw [show Nat.land (Nat.mul (Nat.land (Nat.shiftRight a (Nat.mul 6 k)) 63) rep6)
      (Nat.mul (Nat.land (Nat.shiftRight b k) rep6) 63) = _ &&& _ from rfl, e1, e2,
    Nat.testBit_and, testBit_pack6 hc hc hc hc hc hj hi,
    testBit_pack6 (mul63_lt _ _) (mul63_lt _ _) (mul63_lt _ _) (mul63_lt _ _) (mul63_lt _ _) hj hi]
  congr 1
  · interval_cases j <;> rfl
  · interval_cases j <;> simp [testBit_bit01 _ _ hi, Nat.testBit_shiftRight, Nat.add_comm]

theorem mtF_lt (a b k : ℕ) : mtF a b k < 2 ^ 36 := by
  unfold mtF
  rw [show Nat.land (Nat.mul (Nat.land (Nat.shiftRight a (Nat.mul 6 k)) 63) rep6)
      (Nat.mul (Nat.land (Nat.shiftRight b k) rep6) 63) =
      (Code.col a k * rep6) &&& ((b >>> k &&& rep6) * 63) from rfl, mul_rep6]
  exact lt_of_le_of_lt Nat.and_le_left (Code.pack_lt (Code.col_lt _ _) (Code.col_lt _ _)
    (Code.col_lt _ _) (Code.col_lt _ _) (Code.col_lt _ _) (Code.col_lt _ _))

theorem testBit_sel (v j c i : ℕ) : (Code.sel v j c).testBit i = (v.testBit j && c.testBit i) := by
  unfold Code.sel
  split <;> simp_all

theorem testBit_act (a v i : ℕ) :
    (Code.act a v).testBit i = ((((((v.testBit 0 && (Code.col a 0).testBit i) ^^
      (v.testBit 1 && (Code.col a 1).testBit i)) ^^ (v.testBit 2 && (Code.col a 2).testBit i)) ^^
      (v.testBit 3 && (Code.col a 3).testBit i)) ^^ (v.testBit 4 && (Code.col a 4).testBit i)) ^^
      (v.testBit 5 && (Code.col a 5).testBit i)) := by
  simp only [Code.act, Nat.testBit_xor, testBit_sel]

theorem testBit_col (b j k : ℕ) (hk : k < 6) : (Code.col b j).testBit k = b.testBit (6 * j + k) := by
  unfold Code.col
  rw [Nat.testBit_and, Nat.testBit_shiftRight, show (63 : ℕ) = 2 ^ 6 - 1 by norm_num,
    Nat.testBit_two_pow_sub_one]
  simp [hk, Nat.add_comm]

theorem mulF_eq (a b : ℕ) : mulF a b = Code.mul a b := by
  have hl : ∀ k, mtF a b k < 2 ^ 36 := mtF_lt a b
  apply eq_of_testBit_lt' (n := 36)
  · unfold mulF
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (hl _) (hl _))
      (Nat.xor_lt_two_pow (hl _) (hl _))) (Nat.xor_lt_two_pow (hl _) (hl _))
  · exact Code.mul_lt a b
  · intro n hn
    obtain ⟨j, i, hj, hi, rfl⟩ : ∃ j i, j < 6 ∧ i < 6 ∧ n = 6 * j + i :=
      ⟨n / 6, n % 6, by omega, by omega, by omega⟩
    have ha : ∀ j, Code.act a (Code.col b j) < 64 := fun j => Code.act_lt _ _
    rw [Code.mul_eq, testBit_pack6 (ha _) (ha _) (ha _) (ha _) (ha _) hj hi]
    have e : (![Code.act a (Code.col b 0), Code.act a (Code.col b 1), Code.act a (Code.col b 2),
        Code.act a (Code.col b 3), Code.act a (Code.col b 4), Code.act a (Code.col b 5)]
        ⟨j, hj⟩) = Code.act a (Code.col b j) := by interval_cases j <;> rfl
    rw [e, testBit_act]
    unfold mulF
    simp only [show ∀ x y : ℕ, Nat.xor x y = x ^^^ y from fun _ _ => rfl, Nat.testBit_xor,
      testBit_mtF a b _ hj hi, testBit_col b j _ (by norm_num : 0 < 6),
      testBit_col b j _ (by norm_num : 1 < 6), testBit_col b j _ (by norm_num : 2 < 6),
      testBit_col b j _ (by norm_num : 3 < 6), testBit_col b j _ (by norm_num : 4 < 6),
      testBit_col b j _ (by norm_num : 5 < 6)]
    cases (Code.col a 0).testBit i <;> cases (Code.col a 1).testBit i <;>
      cases (Code.col a 2).testBit i <;> cases (Code.col a 3).testBit i <;>
      cases (Code.col a 4).testBit i <;> cases (Code.col a 5).testBit i <;> simp [Bool.and_comm]

theorem mulF_vec (m : ℕ) {v : ℕ} (hv : v < 64) : mulF m v = Code.act m v := by
  rw [mulF_eq, Code.mul_eq]
  have h0 : Code.col v 0 = v := by
    unfold Code.col
    simp only [Nat.mul_zero, Nat.shiftRight_zero]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 6) hv
  have hz : ∀ j, 1 ≤ j → Code.col v j = 0 := fun j hj => by
    unfold Code.col
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (lt_of_lt_of_le hv (by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (6 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rfl
  rw [h0, hz 1 le_rfl, hz 2 (by norm_num), hz 3 (by norm_num), hz 4 (by norm_num),
    hz 5 (by norm_num)]
  have e : Code.act m 0 = 0 := by unfold Code.act Code.sel; simp
  rw [e]
  unfold Code.pack
  simp

end CFSG.KC.C690

end
