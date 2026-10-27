
module

public import Certificates.Data.Kernel.MatConj22
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertInputs

public section

namespace CFSG.KC.MatConj

open CFSG.KLie.CT CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Co2

theorem rowOf_lt22 (x t : ℕ) : rowOf x t < 2 ^ 22 := Nat.mod_lt _ (by positivity)

theorem rowOf_zero (x : ℕ) : rowOf x 0 = x % 2 ^ 22 := by
  simp [rowOf]

theorem rowOf_succ (x t : ℕ) : rowOf x (t + 1) = rowOf (x / 2 ^ 22) t := by
  have e : 22 * (t + 1) = 22 + 22 * t := by ring
  rw [rowOf, rowOf, Nat.div_div_eq_div_mul, ← pow_add, e]

theorem rowOf_xor (x y t : ℕ) : rowOf (x ^^^ y) t = rowOf x t ^^^ rowOf y t := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [rowOf, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor]
  cases decide (i < 22) <;> simp

theorem rowOf_zero_left (t : ℕ) : rowOf 0 t = 0 := by
  simp [rowOf]

theorem eq_of_rowOf : ∀ (m x y : ℕ), x < 2 ^ (22 * m) → y < 2 ^ (22 * m) →
    (∀ t < m, rowOf x t = rowOf y t) → x = y
  | 0, x, y, hx, hy, _ => by
    simp at hx hy
    omega
  | m + 1, x, y, hx, hy, h => by
    have h0 := h 0 (Nat.succ_pos m)
    rw [rowOf_zero, rowOf_zero] at h0
    have e : 22 * (m + 1) = 22 * m + 22 := by ring
    rw [e, pow_add] at hx hy
    have hd : x / 2 ^ 22 = y / 2 ^ 22 := by
      refine eq_of_rowOf m _ _ ?_ ?_ fun t ht => ?_
      · rw [Nat.div_lt_iff_lt_mul (by positivity)]
        exact hx
      · rw [Nat.div_lt_iff_lt_mul (by positivity)]
        exact hy
      · rw [← rowOf_succ, ← rowOf_succ]
        exact h (t + 1) (by omega)
    rw [← Nat.mod_add_div x (2 ^ 22), ← Nat.mod_add_div y (2 ^ 22), h0, hd]

@[expose] noncomputable def xorN (f : ℕ → ℕ) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => acc ^^^ f b) m

theorem xorN_zero (f : ℕ → ℕ) : xorN f 0 = 0 := rfl

theorem xorN_succ (f : ℕ → ℕ) (m : ℕ) : xorN f (m + 1) = xorN f m ^^^ f m := rfl

theorem xorN_congr {f f' : ℕ → ℕ} : ∀ {m : ℕ}, (∀ b < m, f b = f' b) → xorN f m = xorN f' m
  | 0, _ => rfl
  | m + 1, h => by
    rw [xorN_succ, xorN_succ, xorN_congr fun b hb => h b (by omega), h m (by omega)]

theorem rowOf_xorN (f : ℕ → ℕ) (t : ℕ) :
    ∀ m, rowOf (xorN f m) t = xorN (fun b => rowOf (f b) t) m
  | 0 => rowOf_zero_left t
  | m + 1 => by rw [xorN_succ, xorN_succ, rowOf_xor, rowOf_xorN f t m]

theorem xorN_lt {f : ℕ → ℕ} {w : ℕ} (h : ∀ b, f b < 2 ^ w) : ∀ m, xorN f m < 2 ^ w
  | 0 => by
    rw [xorN_zero]
    positivity
  | m + 1 => by
    rw [xorN_succ]
    exact Nat.xor_lt_two_pow (xorN_lt h m) (h m)

theorem xorN_xor (f f' : ℕ → ℕ) : ∀ m, xorN (fun b => f b ^^^ f' b) m = xorN f m ^^^ xorN f' m
  | 0 => by rw [xorN_zero, xorN_zero, xorN_zero, Nat.zero_xor]
  | m + 1 => by
    rw [xorN_succ, xorN_succ, xorN_succ, xorN_xor f f' m]
    ac_rfl

@[expose] noncomputable def sel (R : ℕ → ℕ) (v m : ℕ) : ℕ :=
  xorN (fun b => if v.testBit b then R b else 0) m

theorem sel_xor (R : ℕ → ℕ) (x y m : ℕ) : sel R (x ^^^ y) m = sel R x m ^^^ sel R y m := by
  unfold sel
  rw [← xorN_xor]
  refine xorN_congr fun b _ => ?_
  rw [Nat.testBit_xor]
  cases x.testBit b <;> cases y.testBit b <;> simp

theorem sel_zero (R : ℕ → ℕ) (m : ℕ) : sel R 0 m = 0 := by
  unfold sel
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [xorN_succ, ih]
    simp

theorem sel_xorN (R S : ℕ → ℕ) (v k : ℕ) : ∀ m,
    sel R (xorN (fun a => if v.testBit a then S a else 0) m) k =
      xorN (fun a => if v.testBit a then sel R (S a) k else 0) m
  | 0 => sel_zero R k
  | m + 1 => by
    rw [xorN_succ, xorN_succ, sel_xor, sel_xorN R S v k m]
    cases v.testBit m <;> simp [sel_zero]

theorem sel_sel (R S : ℕ → ℕ) (v k m : ℕ) :
    sel R (sel S v m) k = xorN (fun a => if v.testBit a then sel R (S a) k else 0) m :=
  sel_xorN R S v k m

theorem actGo_eq (rows : Array ℕ) (v : ℕ) : ∀ (m acc : ℕ),
    CFSG.Monster.VisCert.Native.actGo rows v m acc = acc ^^^ sel (fun i => rows[i]!) v m
  | 0, acc => by simp [CFSG.Monster.VisCert.Native.actGo, sel, xorN_zero]
  | m + 1, acc => by
    rw [CFSG.Monster.VisCert.Native.actGo, actGo_eq rows v m, sel, sel, xorN_succ]
    cases v.testBit m <;> simp <;> ac_rfl

theorem actD_eq (rows : Array ℕ) (v : ℕ) :
    Native.actD 22 rows v = sel (fun i => rows[i]!) v 22 := by
  rw [Native.actD, actGo_eq, Nat.zero_xor]

theorem sel_lt {R : ℕ → ℕ} (hR : ∀ i < 22, R i < 2 ^ 22) (v : ℕ) : sel R v 22 < 2 ^ 22 := by
  rw [sel, xorN_congr (f' := fun b => if b < 22 ∧ v.testBit b then R b else 0) fun b hb => by
    by_cases h : v.testBit b <;> simp [h, hb]]
  refine xorN_lt (fun b => ?_) 22
  split
  · rename_i h
    exact hR b h.1
  · positivity

theorem mul_rowOf {g : ℕ} (hg : g < 2 ^ 22) : ∀ (t m : ℕ), (∀ s, rowOf m s ≤ 1) →
    rowOf (m * g) t = rowOf m t * g := by
  intro t
  induction t with
  | zero =>
    intro m hm
    have h0 := hm 0
    rw [rowOf_zero] at h0
    have hlt : m % 2 ^ 22 * g < 2 ^ 22 :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ h0) (by omega)
    rw [rowOf_zero, rowOf_zero, Nat.mul_mod, Nat.mod_eq_of_lt hg, Nat.mod_eq_of_lt hlt]
  | succ t ih =>
    intro m hm
    have h0 := hm 0
    rw [rowOf_zero] at h0
    have hlt : m % 2 ^ 22 * g < 2 ^ 22 :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ h0) (by omega)
    have hq : m * g / 2 ^ 22 = m / 2 ^ 22 * g := by
      conv_lhs => rw [← Nat.mod_add_div m (2 ^ 22)]
      rw [add_mul, mul_assoc, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt,
        zero_add]
    have hm' : ∀ s, rowOf (m / 2 ^ 22) s ≤ 1 := fun s => by
      rw [← rowOf_succ]
      exact hm (s + 1)
    rw [rowOf_succ, rowOf_succ, hq, ih _ hm']

theorem ones22_testBit (j : ℕ) :
    ones22.testBit j = (decide (j % 22 = 0) && decide (j < 484)) := by
  by_cases hj : j < 484
  · have h : ∀ j < 484, ones22.testBit j = decide (j % 22 = 0) := by decide +kernel
    rw [h j hj]
    simp [hj]
  · have hlt : ones22 < 2 ^ j := lt_of_lt_of_le (by decide +kernel : ones22 < 2 ^ 484)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow hlt]
    simp [hj]

theorem testBit_one_ne {i : ℕ} (hi : 0 < i) : Nat.testBit 1 i = false :=
  Bool.eq_false_iff.2 fun e => by
    have := Nat.testBit_one_eq_true_iff_self_eq_zero.1 e
    omega

theorem rowOf_land_ones (x t : ℕ) :
    rowOf (x &&& ones22) t = if t < 22 ∧ x.testBit (22 * t) = true then 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [rowOf, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_land,
    ones22_testBit]
  split
  · rename_i h
    obtain ⟨ht, hb⟩ := h
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [hb, Nat.mul_mod_right, show 22 * t < 484 by omega]
    · rw [testBit_one_ne hi]
      by_cases hi22 : i < 22
      · have h1 : ¬ (i + 22 * t) % 22 = 0 := by omega
        have h2 : ¬ i % 22 = 0 := by omega
        simp [h1, h2]
      · simp [hi22]
  · rename_i h
    rw [Nat.zero_testBit]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · by_cases ht : t < 22
      · have hb : x.testBit (22 * t) = false := by simpa [ht] using h
        simp [hb]
      · simp [show ¬ 22 * t < 484 by omega]
    · by_cases hi22 : i < 22
      · have h1 : ¬ (i + 22 * t) % 22 = 0 := by omega
        have h2 : ¬ i % 22 = 0 := by omega
        simp [h1, h2]
      · simp [hi22]

theorem rowOf_land_le (x s : ℕ) : rowOf (x &&& ones22) s ≤ 1 := by
  rw [rowOf_land_ones]
  split <;> omega

theorem rowOf_shift_ones {n b t : ℕ} (hb : b < 22) (ht : t < 22) :
    rowOf ((n >>> b) &&& ones22) t = if (rowOf n t).testBit b then 1 else 0 := by
  rw [rowOf_land_ones, Nat.testBit_shiftRight, rowOf, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.add_comm b]
  simp [hb, ht]

theorem fget_eq_rowOf (x a : ℕ) : fget x a 22 = rowOf x a := by
  change (x >>> (a * 22)) &&& (1 <<< 22 - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, rowOf,
    mul_comm]

theorem forceN_eq (y : ℕ) (k : ℕ → ℕ) : forceN y k = k y := by
  cases y <;> rfl

theorem mulR_eq (g n : ℕ) :
    mulR g n = xorN (fun b => ((n >>> b) &&& ones22) * fget g b 22) 22 := rfl

theorem mulL_eq (c u : ℕ) : mulL c u = xorN (fun a => fget c a 484 * fget u a 22) 22 := rfl

theorem rowOf_mulR {g : ℕ} {G : Array ℕ} (hg : ∀ b < 22, rowOf g b = G[b]!) (n : ℕ) {a : ℕ}
    (ha : a < 22) : rowOf (mulR g n) a = Native.actD 22 G (rowOf n a) := by
  rw [mulR_eq, rowOf_xorN, actD_eq, sel]
  refine xorN_congr fun b hb => ?_
  have hgb : fget g b 22 < 2 ^ 22 := by
    rw [fget_eq_rowOf]
    exact rowOf_lt22 g b
  rw [mul_rowOf hgb a _ (rowOf_land_le _), rowOf_shift_ones hb ha, fget_eq_rowOf, hg b hb]
  split <;> simp

theorem mulL_lt {c : ℕ} (hc : ∀ a < 22, fget c a 484 &&& ones22 = fget c a 484) (u : ℕ) :
    mulL c u < 2 ^ 484 := by
  rw [mulL_eq]
  have key : ∀ a, (if a < 22 then fget c a 484 * fget u a 22 else 0) < 2 ^ 484 := by
    intro a
    split
    · rename_i ha
      have h1 : fget c a 484 ≤ ones22 := by
        rw [← hc a ha]
        exact Nat.and_le_right
      have h2 : fget u a 22 ≤ 2 ^ 22 - 1 := by
        rw [fget_eq_rowOf]
        have := rowOf_lt22 u a
        omega
      calc fget c a 484 * fget u a 22 ≤ ones22 * (2 ^ 22 - 1) := Nat.mul_le_mul h1 h2
        _ < 2 ^ 484 := by decide +kernel
    · positivity
  rw [xorN_congr (f' := fun a => if a < 22 then fget c a 484 * fget u a 22 else 0)
    fun a ha => by simp [ha]]
  exact xorN_lt key 22

theorem encL_lt : ∀ L : List ℕ, encL L < 2 ^ (22 * L.length)
  | [] => by simp [encL]
  | r :: l => by
    have h := encL_lt l
    have hr : r % 2 ^ 22 < 2 ^ 22 := Nat.mod_lt _ (by positivity)
    rw [encL, List.length_cons, mul_add, mul_one, pow_add]
    calc r % 2 ^ 22 + 2 ^ 22 * encL l < 2 ^ 22 + 2 ^ 22 * encL l := Nat.add_lt_add_right hr _
      _ = 2 ^ 22 * (encL l + 1) := by ring
      _ ≤ 2 ^ 22 * 2 ^ (22 * l.length) := Nat.mul_le_mul_left _ h
      _ = 2 ^ (22 * l.length) * 2 ^ 22 := by ring

theorem rowOf_encL : ∀ (L : List ℕ) (t : ℕ), t < L.length → rowOf (encL L) t = L[t]! % 2 ^ 22
  | [], t, ht => absurd ht (by simp)
  | r :: l, 0, _ => by
    rw [encL, rowOf_zero]
    simp [Nat.add_mul_mod_self_left]
  | r :: l, t + 1, ht => by
    rw [encL, rowOf_succ, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity)), zero_add,
      rowOf_encL l t (by simpa using ht)]
    simp

theorem rowsOf_get (n : ℕ) {t : ℕ} (ht : t < 22) : (rowsOf n)[t]! = rowOf n t := by
  rw [rowsOf, getElem!_pos _ _ (by simp [ht])]
  simp

theorem map_range_get (F : ℕ → ℕ) {j : ℕ} (hj : j < 22) : ((List.range 22).map F)[j]! = F j := by
  rw [getElem!_pos _ _ (by simpa using hj)]
  simp

theorem conjM_eq {g c : ℕ} {G GI : Array ℕ} (hg : ∀ b < 22, rowOf g b = G[b]!)
    (hG : ∀ b < 22, G[b]! < 2 ^ 22) (hcl : ∀ a < 22, fget c a 484 &&& ones22 = fget c a 484)
    (hc : ∀ a < 22, ∀ j < 22, rowOf (fget c a 484) j = if GI[j]!.testBit a then 1 else 0)
    (n : ℕ) :
    conjM g c n = encL ((List.range 22).map fun j =>
      Native.actD 22 G (Native.actD 22 (rowsOf n) GI[j]!)) := by
  rw [conjM, forceN_eq]
  have hL := encL_lt ((List.range 22).map fun j =>
    Native.actD 22 G (Native.actD 22 (rowsOf n) GI[j]!))
  rw [List.length_map, List.length_range] at hL
  refine eq_of_rowOf 22 _ _ (mulL_lt hcl _) hL fun j hj => ?_
  rw [rowOf_encL _ _ (by simpa using hj), map_range_get _ hj, actD_eq G,
    Nat.mod_eq_of_lt (sel_lt hG _), actD_eq, mulL_eq, rowOf_xorN, sel_sel]
  refine xorN_congr fun a ha => ?_
  have hu : fget (mulR g n) a 22 < 2 ^ 22 := by
    rw [fget_eq_rowOf]
    exact rowOf_lt22 _ _
  have hm : ∀ s, rowOf (fget c a 484) s ≤ 1 := fun s => by
    rw [← hcl a ha]
    exact rowOf_land_le _ _
  rw [mul_rowOf hu j _ hm, hc a ha j hj, fget_eq_rowOf, rowOf_mulR hg n ha, rowsOf_get n ha,
    actD_eq]
  split <;> simp

end CFSG.KC.MatConj

end
