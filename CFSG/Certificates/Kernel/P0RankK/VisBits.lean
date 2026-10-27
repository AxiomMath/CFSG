module

public import Certificates.Data.Kernel.P0Vis
public import CFSG.Certificates.Kernel.LceSP.Popcount
public import CFSG.Monster.B.TwoA.Sp8.P0RankWalk
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.LceSP.Base
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KC.P0Vis

open CFSG.KC.P0Orb CFSG.Certificates.LceP CFSG.Monster.B.TwoA.Sp8.P0Rank Finset

set_option exponentiation.threshold 1024 in
theorem pcStep_eq (x w : ℕ) : pcStep x w = swarStep 1024 w x := by
  have hM : swarMask 1024 w = m1024 / (2 ^ (2 * w) - 1) * (2 ^ w - 1) := by
    unfold swarMask
    change ((1 <<< 1024) - 1) / ((1 <<< (2 * w)) - 1) * ((1 <<< w) - 1) = _
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul,
      Nat.one_mul]
    unfold m1024
    rfl
  unfold pcStep swarStep
  rw [hM]
  rfl

set_option exponentiation.threshold 1024 in
theorem pc_eq (x : ℕ) : pc x = ∑ j ∈ range 1024, x / 2 ^ j % 2 := by
  simp only [pc, pcStep_eq]
  set x1 := swarStep 1024 1 x
  set x2 := swarStep 1024 2 x1
  set x3 := swarStep 1024 4 x2
  set x4 := swarStep 1024 8 x3
  set x5 := swarStep 1024 16 x4
  set x6 := swarStep 1024 32 x5
  set x7 := swarStep 1024 64 x6
  set x8 := swarStep 1024 128 x7
  set x9 := swarStep 1024 256 x8
  have c1 : ds 2 x1 512 = ds 1 x 1024 :=
    ds_swarStep (b := 1) (b2 := 2) (m := 512) (m2 := 1024) (n := 1024) (by norm_num) rfl rfl rfl x
  have c2 : ds 4 x2 256 = ds 2 x1 512 :=
    ds_swarStep (b := 2) (b2 := 4) (m := 256) (m2 := 512) (n := 1024) (by norm_num) rfl rfl rfl x1
  have c3 : ds 8 x3 128 = ds 4 x2 256 :=
    ds_swarStep (b := 4) (b2 := 8) (m := 128) (m2 := 256) (n := 1024) (by norm_num) rfl rfl rfl x2
  have c4 : ds 16 x4 64 = ds 8 x3 128 :=
    ds_swarStep (b := 8) (b2 := 16) (m := 64) (m2 := 128) (n := 1024) (by norm_num) rfl rfl rfl x3
  have c5 : ds 32 x5 32 = ds 16 x4 64 :=
    ds_swarStep (b := 16) (b2 := 32) (m := 32) (m2 := 64) (n := 1024) (by norm_num) rfl rfl rfl x4
  have c6 : ds 64 x6 16 = ds 32 x5 32 :=
    ds_swarStep (b := 32) (b2 := 64) (m := 16) (m2 := 32) (n := 1024) (by norm_num) rfl rfl rfl x5
  have c7 : ds 128 x7 8 = ds 64 x6 16 :=
    ds_swarStep (b := 64) (b2 := 128) (m := 8) (m2 := 16) (n := 1024) (by norm_num) rfl rfl rfl x6
  have c8 : ds 256 x8 4 = ds 128 x7 8 :=
    ds_swarStep (b := 128) (b2 := 256) (m := 4) (m2 := 8) (n := 1024) (by norm_num) rfl rfl rfl x7
  have c9 : ds 512 x9 2 = ds 256 x8 4 :=
    ds_swarStep (b := 256) (b2 := 512) (m := 2) (m2 := 4) (n := 1024) (by norm_num) rfl rfl rfl x8
  have hrep := swarStep_rep (b := 512) (b2 := 1024) (m := 1) (n := 1024) (by norm_num) rfl rfl x9
  have h10 : swarStep 1024 512 x9 = ds 512 x9 2 := by
    rw [hrep, ds, sum_range_one, sum_range_succ, sum_range_one]
    simp
  rw [h10, c9, c8, c7, c6, c5, c4, c3, c2, c1, ds_one]

theorem sum_bits_eq_card (x N : ℕ) :
    ∑ j ∈ range N, x / 2 ^ j % 2 = #((range N).filter (fun j => x.testBit j = true)) := by
  rw [card_filter]
  refine sum_congr rfl fun j _ => ?_
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;> simp [h]

theorem pc_eq_card (x : ℕ) : pc x = #((range 1024).filter (fun j => x.testBit j = true)) := by
  rw [pc_eq, sum_bits_eq_card]

theorem pf_xor (a b s : ℕ) : pf (a ^^^ b) s = pf a s ^^^ pf b s := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [pf]
  change (a ^^^ b ^^^ (a ^^^ b) >>> s).testBit i = (a ^^^ a >>> s ^^^ (b ^^^ b >>> s)).testBit i
  simp only [Nat.testBit_xor, Nat.testBit_shiftRight]
  cases a.testBit i <;> cases b.testBit i <;> cases a.testBit (s + i) <;>
    cases b.testBit (s + i) <;> rfl

theorem par16_xor (a b : ℕ) : par16 (a ^^^ b) = par16 a ^^^ par16 b := by
  simp only [par16, pf_xor]
  change (_ ^^^ _) &&& 1 = (_ &&& 1) ^^^ (_ &&& 1)
  rw [Nat.and_xor_distrib_right]

theorem par16_zero : par16 0 = 0 := by decide

theorem par16_lt (x : ℕ) : par16 x < 2 := by
  change _ &&& 1 < 2
  exact Nat.and_lt_two_pow _ (by norm_num : 1 < 2 ^ 1)

theorem par16_two_pow {e : ℕ} (he : e < 16) : par16 (2 ^ e) = 1 := by
  interval_cases e <;> decide

theorem par16_land_two_pow (K : ℕ) {e : ℕ} (he : e < 16) :
    par16 (K &&& 2 ^ e) = (K.testBit e).toNat := by
  rw [Nat.and_two_pow]
  cases K.testBit e
  · simpa using par16_zero
  · simpa using par16_two_pow he

@[expose] def lc (f : ℕ → ℕ) (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => lc f x n ^^^ (if x.testBit n then f n else 0)

theorem tr_succ (f : ℕ → ℕ) (K n : ℕ) :
    tr f K (n + 1) = tr f K n ||| par16 (K &&& f n) <<< n := rfl

theorem tr_lt (f : ℕ → ℕ) (K : ℕ) : ∀ n, tr f K n < 2 ^ n
  | 0 => by simp [tr]
  | n + 1 => by
    rw [tr_succ]
    refine Nat.or_lt_two_pow (lt_of_lt_of_le (tr_lt f K n) (Nat.pow_le_pow_right (by norm_num)
      (by omega))) ?_
    rw [Nat.shiftLeft_eq, pow_succ, Nat.mul_comm (2 ^ n) 2]
    exact Nat.mul_lt_mul_of_pos_right (par16_lt _) (Nat.two_pow_pos n)

theorem tr_succ_xor (f : ℕ → ℕ) (K n : ℕ) :
    tr f K (n + 1) = tr f K n ^^^ par16 (K &&& f n) * 2 ^ n := by
  rw [tr_succ, Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_mul_two_pow]
  by_cases hi : i < n
  · simp [show ¬ n ≤ i by omega]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (tr_lt f K n) (Nat.pow_le_pow_right (by norm_num)
      (by omega : n ≤ i)))]
    simp

theorem par16_land_lc (f : ℕ → ℕ) (K x : ℕ) :
    ∀ n, n ≤ 16 → par16 (K &&& lc f x n) = par16 (tr f K n &&& x)
  | 0, _ => by simp [lc, tr]
  | n + 1, hn => by
    have ih := par16_land_lc f K x n (by omega)
    rw [lc, Nat.and_xor_distrib_left, par16_xor, ih, tr_succ_xor, Nat.and_xor_distrib_right,
      par16_xor]
    congr 1
    have hp := par16_lt (K &&& f n)
    rw [Nat.and_comm _ x, Nat.mul_comm]
    rcases (by omega : par16 (K &&& f n) = 0 ∨ par16 (K &&& f n) = 1) with h0 | h1
    · rw [h0]
      split_ifs <;> simp [h0, par16_zero]
    · rw [h1, Nat.mul_one, Nat.and_two_pow, par16_land_two_pow _ (by omega) |>.symm.trans
        (by rw [Nat.and_two_pow])]
      split_ifs with hb <;> simp [hb, h1, par16_zero, par16_two_pow (by omega : n < 16)]

private theorem lowM_bits : ∀ j < 5, ∀ i < 32,
    (lowM j).testBit i = !(i.testBit j) := by decide

private theorem lowM_lt : ∀ j < 5, lowM j < 2 ^ 32 := by decide

private theorem table_set : ∀ j < 5, ∀ x < 32, x.testBit j = true →
    2 ^ j ≤ x ∧ x - 2 ^ j = x ^^^ 2 ^ j ∧ (x - 2 ^ j).testBit j = false := by decide

private theorem table_clr : ∀ j < 5, ∀ x < 32, x.testBit j = false →
    (2 ^ j ≤ x → (x - 2 ^ j).testBit j = true) ∧ 2 ^ j + x = x ^^^ 2 ^ j := by decide

theorem testBit_swp (m : ℕ) {j x : ℕ} (hj : j < 5) (hx : x < 32) :
    (swp m j).testBit x = m.testBit (x ^^^ 2 ^ j) := by
  change ((m &&& lowM j) <<< 2 ^ j ||| ((m >>> 2 ^ j) &&& lowM j)).testBit x = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_and,
    Nat.testBit_shiftRight, lowM_bits j hj x hx]
  cases hb : x.testBit j
  · obtain ⟨h1, h2⟩ := table_clr j hj x hx hb
    rw [h2]
    by_cases hle : 2 ^ j ≤ x
    · rw [lowM_bits j hj (x - 2 ^ j) (lt_of_le_of_lt (Nat.sub_le x _) hx), h1 hle]
      simp
    · simp [hle]
  · obtain ⟨h1, h2, h3⟩ := table_set j hj x hx hb
    rw [lowM_bits j hj (x - 2 ^ j) (lt_of_le_of_lt (Nat.sub_le x _) hx), h3, ← h2]
    simp [h1]

theorem testBit_swc (m v : ℕ) {j x : ℕ} (hj : j < 5) (hx : x < 32) :
    (swc m v j).testBit x = m.testBit (x ^^^ (if v.testBit j then 2 ^ j else 0)) := by
  unfold swc
  have hv : (Nat.land (Nat.shiftRight v j) 1 == 1) = v.testBit j := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    change ((v >>> j) &&& 1 == 1) = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ j) with h | h <;> simp [h]
  change (bif (Nat.land (Nat.shiftRight v j) 1 == 1) then swp m j else m).testBit x = _
  rw [hv]
  cases v.testBit j
  · simp
  · simpa using testBit_swp m hj hx

private theorem xor_bits_v : ∀ v < 32,
    (if v.testBit 4 then 2 ^ 4 else 0) ^^^ (if v.testBit 3 then 2 ^ 3 else 0) ^^^
      (if v.testBit 2 then 2 ^ 2 else 0) ^^^ (if v.testBit 1 then 2 ^ 1 else 0) ^^^
      (if v.testBit 0 then 2 ^ 0 else 0) = v := by decide

private theorem ite_lt (b : Bool) (j : ℕ) (hj : j < 5) : (if b then 2 ^ j else 0) < 32 := by
  split_ifs
  · exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hj) (by norm_num)
  · norm_num

theorem testBit_clo (m : ℕ) {v x : ℕ} (hv : v < 32) (hx : x < 32) :
    (clo m v).testBit x = (m.testBit x || m.testBit (x ^^^ v)) := by
  unfold clo
  change (m ||| _).testBit x = _
  rw [Nat.testBit_or]
  congr 1
  have h32 : ∀ a b, a < 32 → b < 32 → a ^^^ b < 32 := fun a b ha hb =>
    Nat.xor_lt_two_pow (n := 5) ha hb
  rw [testBit_swc _ _ (by norm_num) hx, testBit_swc _ _ (by norm_num) (h32 _ _ hx (ite_lt _ 4 (by norm_num))),
    testBit_swc _ _ (by norm_num) (h32 _ _ (h32 _ _ hx (ite_lt _ 4 (by norm_num))) (ite_lt _ 3 (by norm_num))),
    testBit_swc _ _ (by norm_num) (h32 _ _ (h32 _ _ (h32 _ _ hx (ite_lt _ 4 (by norm_num)))
      (ite_lt _ 3 (by norm_num))) (ite_lt _ 2 (by norm_num))),
    testBit_swc _ _ (by norm_num) (h32 _ _ (h32 _ _ (h32 _ _ (h32 _ _ hx (ite_lt _ 4 (by norm_num)))
      (ite_lt _ 3 (by norm_num))) (ite_lt _ 2 (by norm_num))) (ite_lt _ 1 (by norm_num)))]
  have hv' := xor_bits_v v hv
  generalize (if v.testBit 4 = true then 2 ^ 4 else 0) = c4 at hv' ⊢
  generalize (if v.testBit 3 = true then 2 ^ 3 else 0) = c3 at hv' ⊢
  generalize (if v.testBit 2 = true then 2 ^ 2 else 0) = c2 at hv' ⊢
  generalize (if v.testBit 1 = true then 2 ^ 1 else 0) = c1 at hv' ⊢
  generalize (if v.testBit 0 = true then 2 ^ 0 else 0) = c0 at hv' ⊢
  rw [← hv']
  simp only [Nat.xor_assoc]

theorem ycRow_spec {YE NY m : ℕ} : ∀ (row : List ℕ) (v₀ : ℕ), ycRow YE NY m row v₀ = true →
    ∀ u (hu : u < row.length), row[u] < NY ∧ fld YE (32 * row[u]) m32 = clo m (v₀ + u)
  | [], _, _, u, hu => absurd hu (by simp)
  | j :: row, v₀, h, u, hu => by
    change (Nat.blt j NY && Nat.beq (fld YE (32 * j) m32) (clo m v₀) &&
      ycRow YE NY m row (v₀ + 1)) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    rcases u with _ | u
    · exact ⟨h.1.1, by simpa using h.1.2⟩
    · have := ycRow_spec row (v₀ + 1) h.2 u (by simpa using hu)
      simpa [Nat.add_assoc, Nat.add_comm 1 u] using this

theorem ycRows_spec {YE NY : ℕ} : ∀ (rows : List (List ℕ)) (i₀ : ℕ), ycRows YE NY i₀ rows = true →
    ∀ k (hk : k < rows.length), ∀ v < 32, ∃ j < NY,
      fld YE (32 * j) m32 = clo (fld YE (32 * (i₀ + k)) m32) v
  | [], _, _, k, hk => absurd hk (by simp)
  | row :: rows, i₀, h, k, hk => by
    simp only [ycRows, Bool.and_eq_true, Nat.beq_eq] at h
    rcases k with _ | k
    · intro v hv
      have := ycRow_spec row 0 h.1.2 v (by omega)
      exact ⟨_, this.1, by simpa using this.2⟩
    · have := ycRows_spec rows (i₀ + 1) h.2 k (by simpa using hk)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

private theorem testBit_of_dyadic {x t : ℕ} (h1 : 2 ^ t ≤ x) (h2 : x < 2 ^ (t + 1)) :
    x.testBit t = true := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h1 h2

private theorem xor_lt_dyadic {x y t : ℕ} (hx : 2 ^ t ≤ x) (hx' : x < 2 ^ (t + 1))
    (hy : 2 ^ t ≤ y) (hy' : y < 2 ^ (t + 1)) : x ^^^ y < 2 ^ t := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_xor]
  rcases Nat.eq_or_lt_of_le hi with rfl | hi
  · rw [testBit_of_dyadic hx hx', testBit_of_dyadic hy hy']
    rfl
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx' (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy' (Nat.pow_le_pow_right (by norm_num) hi))]
    rfl

theorem ycOK_cover {YE NY : ℕ} {YC : List (List ℕ)} (h : ycOK YE NY YC = true) (hNY : 0 < NY)
    {C : Finset ℕ}
    (hC : XorClosed C) (hC32 : ∀ z ∈ C, z < 32) :
    ∃ i < NY, ∀ x < 32, (fld YE (32 * i) m32).testBit x = true ↔ x ∈ C := by
  simp only [ycOK, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h0, hlen⟩, hrows⟩ := h
  have hstep := ycRows_spec YC 0 hrows
  have key : ∀ t ≤ 5, ∃ i < NY, ∀ x < 32,
      (fld YE (32 * i) m32).testBit x = true ↔ x ∈ C ∧ x < 2 ^ t := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨0, hNY, fun x _ => ?_⟩
      have h1 : (1 : ℕ).testBit x = decide (x = 0) := by
        rw [← Nat.pow_zero 2, Nat.testBit_two_pow]
        exact decide_eq_decide.mpr eq_comm
      rw [Nat.mul_zero, h0, h1, pow_zero, Nat.lt_one_iff, decide_eq_true_iff]
      constructor
      · rintro rfl
        exact ⟨hC.1, rfl⟩
      · rintro ⟨-, rfl⟩
        rfl
    | succ t ih =>
      intro ht
      obtain ⟨i, hi, hiC⟩ := ih (by omega)
      by_cases hex : ∃ v ∈ C, 2 ^ t ≤ v ∧ v < 2 ^ (t + 1)
      · obtain ⟨v, hvC, hv1, hv2⟩ := hex
        have hv32 := hC32 v hvC
        obtain ⟨j, hj, hjE⟩ := hstep i (by omega) v hv32
        rw [Nat.zero_add] at hjE
        refine ⟨j, hj, fun x hx => ?_⟩
        rw [hjE, testBit_clo _ hv32 hx, Bool.or_eq_true, hiC x hx,
          hiC _ (Nat.xor_lt_two_pow (n := 5) hx hv32)]
        constructor
        · rintro (⟨hxC, hxt⟩ | ⟨hxC, hxt⟩)
          · exact ⟨hxC, lt_of_lt_of_le hxt (Nat.pow_le_pow_right (by norm_num) (by omega))⟩
          · refine ⟨?_, ?_⟩
            · have := hC.2 _ hxC v hvC
              rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
            · have : x = (x ^^^ v) ^^^ v := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
              rw [this]
              exact Nat.xor_lt_two_pow
                (lt_of_lt_of_le hxt (Nat.pow_le_pow_right (by norm_num) (by omega))) hv2
        · rintro ⟨hxC, hxt⟩
          by_cases hxs : x < 2 ^ t
          · exact Or.inl ⟨hxC, hxs⟩
          · exact Or.inr ⟨hC.2 x hxC v hvC, xor_lt_dyadic (by omega) hxt hv1 hv2⟩
      · refine ⟨i, hi, fun x hx => ?_⟩
        rw [hiC x hx]
        constructor
        · rintro ⟨hxC, hxt⟩
          exact ⟨hxC, lt_of_lt_of_le hxt (Nat.pow_le_pow_right (by norm_num) (by omega))⟩
        · rintro ⟨hxC, hxt⟩
          refine ⟨hxC, ?_⟩
          by_contra hxs
          exact hex ⟨x, hxC, by omega, hxt⟩
  obtain ⟨i, hi, hiC⟩ := key 5 le_rfl
  refine ⟨i, hi, fun x hx => ?_⟩
  rw [hiC x hx]
  exact ⟨fun h => h.1, fun h => ⟨h, by norm_num; omega⟩⟩

end CFSG.KC.P0Vis

end
