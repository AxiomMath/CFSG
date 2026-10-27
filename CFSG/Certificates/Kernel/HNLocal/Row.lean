module

public import CFSG.Certificates.Kernel.HNLocal.Defs
import all CFSG.Certificates.Kernel.Spor.OrdSound
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.HNLocal.RowPf

open CFSG.KC.Ord CFSG.KC.HNLocal CFSG.KS.Ord Matrix Finset

private theorem sN (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem letB_eq (y : Nat) (k : Nat → Bool) : letB y k = k y := by
  cases y <;> rfl

private theorem bAnd_true {a b : Bool}
    (h : (Bool.rec (motive := fun _ => Bool) false b a : Bool) = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

private theorem rec_bAnd (f : Nat → Bool) : ∀ n,
    (Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(f i, ih)) n : Bool) = true →
      ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have h' : (bAnd(f n, Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(f i, ih)) n) :
      Bool) = true := h
    obtain ⟨h1, h2⟩ := bAnd_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact rec_bAnd f n h2 i hi
    · exact h1

private theorem dm133 {i j : Nat} (hj : j < 133) : (133 * i + j) / 133 = i ∧ (133 * i + j) % 133 = j :=
  ⟨by omega, by omega⟩

private theorem rec_or_sum (f : Nat → Nat) (hf : ∀ r, f r < 2 ^ 1729) : ∀ c,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Nat.lor acc (Nat.shiftLeft (f r) (Nat.mul (nat_lit 1729) r))) c =
      ∑ r ∈ range c, f r * 2 ^ (1729 * r)
  | 0 => rfl
  | c + 1 => by
    have ih := rec_or_sum f hf c
    have hlt : ∑ r ∈ range c, f r * 2 ^ (1729 * r) < 2 ^ (1729 * c) := pk_lt fun t _ => hf t
    show Nat.lor (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Nat.lor acc (Nat.shiftLeft (f r) (Nat.mul (nat_lit 1729) r))) c)
        (Nat.shiftLeft (f c) (Nat.mul (nat_lit 1729) c)) = _
    rw [ih, Finset.sum_range_succ]
    change (∑ r ∈ range c, f r * 2 ^ (1729 * r)) ||| (f c <<< (1729 * c)) = _
    rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq, Nat.add_comm]

private theorem cm_M {CM3 M : Nat} (hcm : cmOK CM3 M = true) : M = 2 ^ 399 - 1 := by
  unfold cmOK at hcm
  have h := Nat.eq_of_beq_eq_true (bAnd_true hcm).2
  rw [h]
  show (1 <<< 399) - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

private theorem cm_CM3 {CM3 M : Nat} (hcm : cmOK CM3 M = true) :
    CM3 = ∑ r ∈ range 133, 7 * 2 ^ (1729 * r) := by
  unfold cmOK at hcm
  have h := Nat.eq_of_beq_eq_true (bAnd_true hcm).1
  rw [h]
  exact rec_or_sum (fun _ => 7) (fun _ => Nat.lt_of_lt_of_le (by norm_num : 7 < 2 ^ 3)
    (Nat.pow_le_pow_right (by omega) (by omega))) 133

theorem recC_lt {CM3 M : Nat} (hcm : cmOK CM3 M = true) (C r : Nat) : recC M C r < 2 ^ 399 := by
  rw [cm_M hcm]
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)

theorem recC_eq {CM3 M : Nat} (hcm : cmOK CM3 M = true) (C r : Nat) :
    recC M C r = C / 2 ^ (400 * r) % 2 ^ 399 := by
  rw [cm_M hcm]
  change (C >>> (400 * r)) &&& (2 ^ 399 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem recX_eq (XC : Nat → Nat) (M c r : Nat) (hr : r < 133) :
    recX XC M (133 * c + r) = recC M (XC c) r := by
  obtain ⟨e1, e2⟩ := dm133 (i := c) hr
  show recC M (XC ((133 * c + r) / 133)) ((133 * c + r) % 133) = _
  rw [e1, e2]

theorem leafA_eq {CM3 M : Nat} (hcm : cmOK CM3 M = true) (C c : Nat) :
    leafA M C c = ∑ r ∈ range c, recC M C r * 2 ^ (1729 * r) :=
  rec_or_sum (recC M C) (fun r => Nat.lt_of_lt_of_le (recC_lt hcm C r)
    (Nat.pow_le_pow_right (by omega) (by omega))) c

private theorem rec_add (F : Nat → Nat) : ∀ n,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.add acc (F k)) n =
      ∑ k ∈ range n, F k
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← rec_add F n]
    rfl

private theorem mulC_rec (A G CM3 RM n : Nat) :
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Nat.add acc (Nat.mul (Nat.land (Nat.shiftRight A (Nat.mul (nat_lit 3) k)) CM3)
        (Nat.land (Nat.shiftRight G (Nat.mul (nat_lit 1729) k)) RM))) n =
      ∑ k ∈ range n, ((A >>> (3 * k)) &&& CM3) * ((G >>> (1729 * k)) &&& RM) :=
  rec_add _ n

private theorem tb8 {v b : Nat} (hv : v < 8) (hb : 3 ≤ b) : v.testBit b = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv
    (by rw [show (8 : Nat) = 2 ^ 3 by norm_num]; exact Nat.pow_le_pow_right (by omega) hb))

private theorem col_eq' {CM3 M A n : Nat} (hcm : cmOK CM3 M = true) {a : Nat → Nat}
    (hA : A = ∑ r ∈ range n, a r * 2 ^ (1729 * r)) (ha : ∀ r < n, a r < 2 ^ 1729)
    {k : Nat} (hk : k < 133) :
    (A >>> (3 * k)) &&& CM3 =
      ∑ r ∈ range 133, (if r < n then a r / 2 ^ (3 * k) % 8 else 0) * 2 ^ (1729 * r) := by
  have h7 : ∀ r < 133, (7 : Nat) < 2 ^ 1729 := fun _ _ =>
    Nat.lt_of_lt_of_le (by norm_num : (7 : Nat) < 2 ^ 3) (Nat.pow_le_pow_right (by omega) (by omega))
  have FA : CFSG.KS.PackFld.Fld 1729 (∑ r ∈ range n, a r * 2 ^ (1729 * r))
      (fun t => if t < n then a t else 0) := fld_pk ha
  have FC : CFSG.KS.PackFld.Fld 1729 (∑ r ∈ range 133, 7 * 2 ^ (1729 * r))
      (fun t => if t < 133 then 7 else 0) := fld_pk h7
  have hv : ∀ r, (if r < n then a r / 2 ^ (3 * k) % 8 else 0) < 8 := fun r => by
    split
    · exact Nat.mod_lt _ (by norm_num)
    · omega
  have hb : ∀ r < 133, (if r < n then a r / 2 ^ (3 * k) % 8 else 0) < 2 ^ 1729 := fun r _ =>
    Nat.lt_of_lt_of_le (hv r)
      (by rw [show (8 : Nat) = 2 ^ 3 by norm_num]; exact Nat.pow_le_pow_right (by omega) (by omega))
  rw [cm_CM3 hcm, hA]
  refine pk_of_fld (by omega) ?_ hb
  intro i b hbw
  rw [Nat.testBit_and, Nat.testBit_shiftRight, FC i b hbw]
  by_cases hi : i < 133
  · simp only [hi, if_true]
    rw [show (7 : Nat) = 2 ^ 3 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
    by_cases hb3 : b < 3
    · rw [show 3 * k + (1729 * i + b) = 1729 * i + (b + 3 * k) by ring, FA i _ (by omega)]
      by_cases hin : i < n
      · simp only [hin, if_true]
        rw [show (8 : Nat) = 2 ^ 3 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
        simp [hb3]
      · simp [hin]
    · rw [tb8 (hv i) (by omega)]
      simp [hb3]
  · simp [hi]

private theorem rowG_eq {G : Nat} (hG : Canon 5 133 13 G) {k : Nat} (hk : k < 133) :
    (G >>> (1729 * k)) &&& (2 ^ (13 * 133) - 1) =
      ∑ l ∈ range 133, lane 13 G (133 * k + l) * 2 ^ (13 * l) := by
  have hG' := pk_lane (w := 13) (n := 133 * 133) (by norm_num) hG.1
  have h := row_eq (w := 13) (d := 133) (k := k) (b := lane 13 G) (by norm_num)
    (fun t _ => Nat.mod_lt _ (by positivity)) hk
  rw [← hG', show 133 * 13 * k = 1729 * k by ring] at h
  exact h

private theorem rows13 (m : Nat) (G : Nat → Nat) :
    ∑ u ∈ range (133 * m), G u * 2 ^ (13 * u) =
      ∑ i ∈ range m, ∑ j ∈ range 133, G (133 * i + j) * 2 ^ (1729 * i + 13 * j) := by
  have := pk_rows 13 133 G m
  unfold pk at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2
  ring

private theorem prodU (c g : Nat → Nat → Nat) :
    ∑ k ∈ range 133, (∑ r ∈ range 133, c k r * 2 ^ (1729 * r)) *
        (∑ l ∈ range 133, g k l * 2 ^ (13 * l)) =
      ∑ u ∈ range (133 * 133), (∑ k ∈ range 133, c k (u / 133) * g k (u % 133)) * 2 ^ (13 * u) := by
  calc _ = ∑ k ∈ range 133, ∑ r ∈ range 133, ∑ l ∈ range 133,
        c k r * g k l * 2 ^ (1729 * r + 13 * l) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun l _ => ?_
        rw [Nat.pow_add]
        ring
    _ = ∑ r ∈ range 133, ∑ l ∈ range 133, ∑ k ∈ range 133,
        c k r * g k l * 2 ^ (1729 * r + 13 * l) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun r _ => Finset.sum_comm
    _ = _ := by
        rw [rows13]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
        obtain ⟨e1, e2⟩ := dm133 (i := i) (Finset.mem_range.1 hj)
        rw [e1, e2, Finset.sum_mul]

private theorem F_le {G : Nat} (hG : Canon 5 133 13 G) (c : Nat → Nat) (hc : ∀ k, c k < 8)
    {l : Nat} (hl : l < 133) :
    ∑ k ∈ range 133, c k * lane 13 G (133 * k + l) ≤ 3724 := by
  calc _ ≤ ∑ _k ∈ range 133, 28 := Finset.sum_le_sum fun k hk => by
          have h1 := hc k
          have h2 := hG.2 (133 * k + l) (by have := Finset.mem_range.1 hk; nlinarith)
          exact Nat.mul_le_mul (show _ ≤ 7 by omega) (show _ ≤ 4 by omega) |>.trans (by norm_num)
    _ = 3724 := by simp

private theorem mulC_pk {L H CM RM ONE LV HV CM3 M A G n : Nat} {a : Nat → Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hcm : cmOK CM3 M = true)
    (hA : A = ∑ r ∈ range n, a r * 2 ^ (1729 * r)) (ha : ∀ r < n, a r < 2 ^ 1729)
    (hG : Canon 5 133 13 G) :
    mulC L H CM3 RM A G = ∑ u ∈ range (133 * 133),
      ((∑ k ∈ range 133, (if u / 133 < n then a (u / 133) / 2 ^ (3 * k) % 8 else 0) *
        lane 13 G (133 * k + u % 133)) % 5) * 2 ^ (13 * u) := by
  obtain ⟨-, -, -, -, hT, -, hL, hH, -, hRM, -⟩ := consts_facts hc
  have hU : ∑ k ∈ range 133, ((A >>> (3 * k)) &&& CM3) * ((G >>> (1729 * k)) &&& RM) =
      ∑ u ∈ range (133 * 133), (∑ k ∈ range 133,
        (if u / 133 < n then a (u / 133) / 2 ^ (3 * k) % 8 else 0) *
          lane 13 G (133 * k + u % 133)) * 2 ^ (13 * u) := by
    rw [← prodU (fun k r => if r < n then a r / 2 ^ (3 * k) % 8 else 0)
      (fun k l => lane 13 G (133 * k + l))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [col_eq' hcm hA ha (Finset.mem_range.1 hk), hRM, rowG_eq hG (Finset.mem_range.1 hk)]
  have hFb : ∀ t < 133 * 133, (∑ k ∈ range 133,
      (if t / 133 < n then a (t / 133) / 2 ^ (3 * k) % 8 else 0) *
        lane 13 G (133 * k + t % 133)) ≤ 3724 := fun t _ =>
    F_le hG _ (fun k => by split; exact Nat.mod_lt _ (by norm_num); omega) (Nat.mod_lt _ (by omega))
  have hR := redP_pk (w := 13) (n := 133 * 133) (p := 5) (T := 9)
    (f := fun t => ∑ k ∈ range 133,
      (if t / 133 < n then a (t / 133) / 2 ^ (3 * k) % 8 else 0) * lane 13 G (133 * k + t % 133))
    (by omega) hT
    (fun t ht => Nat.lt_of_le_of_lt (hFb t ht) (by norm_num))
    (fun t ht => Nat.lt_of_le_of_lt (hFb t ht) (by norm_num))
  unfold pk at hR hL hH
  have hrec := mulC_rec A G CM3 RM (nat_lit 133)
  unfold mulC
  rw [hrec, hU, hL, hH]
  exact hR

theorem mulC_eq {L H CM RM ONE LV HV CM3 M A G n : Nat} {a : Nat → Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hcm : cmOK CM3 M = true)
    (hA : A = ∑ r ∈ range n, a r * 2 ^ (1729 * r)) (ha : ∀ r < n, a r < 2 ^ 399)
    (hG : Canon 5 133 13 G) :
    mulC L H CM3 RM A G = ∑ u ∈ range (133 * 133),
      ((∑ k ∈ range 133, (if u / 133 < n then a (u / 133) / 2 ^ (3 * k) % 8 else 0) *
        lane 13 G (133 * k + u % 133)) % 5) * 2 ^ (13 * u) :=
  mulC_pk hc hcm hA (fun r hr => Nat.lt_of_lt_of_le (ha r hr)
    (Nat.pow_le_pow_right (by omega) (by omega))) hG

theorem mulC_canon {L H CM RM ONE LV HV CM3 M A G n : Nat} {a : Nat → Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hcm : cmOK CM3 M = true)
    (hA : A = ∑ r ∈ range n, a r * 2 ^ (1729 * r)) (ha : ∀ r < n, a r < 2 ^ 399)
    (hG : Canon 5 133 13 G) : Canon 5 133 13 (mulC L H CM3 RM A G) := by
  rw [mulC_eq hc hcm hA ha hG]
  exact canon_pk (fun t _ => Nat.mod_lt _ (by norm_num)) (by norm_num)

theorem mulC_lane {L H CM RM ONE LV HV CM3 M A G n : Nat} {a : Nat → Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hcm : cmOK CM3 M = true)
    (hA : A = ∑ r ∈ range n, a r * 2 ^ (1729 * r)) (ha : ∀ r < n, a r < 2 ^ 399)
    (hG : Canon 5 133 13 G) {r l : Nat} (hr : r < 133) (hl : l < 133) :
    lane 13 (mulC L H CM3 RM A G) (133 * r + l) =
      (∑ k ∈ range 133, (if r < n then a r / 2 ^ (3 * k) % 8 else 0) *
        lane 13 G (133 * k + l)) % 5 := by
  rw [mulC_eq hc hcm hA ha hG]
  have h := lane_pk (w := 13) (n := 133 * 133) (s := 133 * r + l)
    (g := fun u => (∑ k ∈ range 133, (if u / 133 < n then a (u / 133) / 2 ^ (3 * k) % 8 else 0) *
        lane 13 G (133 * k + u % 133)) % 5)
    (fun t _ => Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
    (by nlinarith)
  unfold pk at h
  rw [h]
  obtain ⟨e1, e2⟩ := dm133 (i := r) hl
  simp only [e1, e2]

theorem mulVec_cvec (G y : Nat) (l : Fin 133) :
    ((OM G)ᵀ *ᵥ cvec y) l = (((∑ k ∈ range 133, (y / 2 ^ (3 * k) % 8) *
      lane 13 G (133 * k + l.val)) % 5 : Nat) : ZMod 5) := by
  rw [ZMod.natCast_mod, Nat.cast_sum]
  simp only [mulVec, dotProduct, transpose_apply, OM, ordMat, cvec]
  rw [← Fin.sum_univ_eq_sum_range (fun k => (((y / 2 ^ (3 * k) % 8) *
    lane 13 G (133 * k + l.val) : Nat) : ZMod 5))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.cast_mul, mul_comm]
  unfold lane
  congr 4
  ring

theorem mulC_vec {L H CM RM ONE LV HV CM3 M A G n : Nat} {a : Nat → Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hcm : cmOK CM3 M = true)
    (hA : A = ∑ r ∈ range n, a r * 2 ^ (1729 * r)) (ha : ∀ r < n, a r < 2 ^ 399)
    (hG : Canon 5 133 13 G) {r : Nat} (hr : r < 133) (hrn : r < n) :
    (fun l : Fin 133 => ((lane 13 (mulC L H CM3 RM A G) (133 * r + l.val) : Nat) : ZMod 5)) =
      (OM G)ᵀ *ᵥ cvec (a r) := by
  funext l
  rw [mulC_lane hc hcm hA ha hG hr l.isLt, mulVec_cvec]
  simp only [hrn, if_true]

theorem rowL_eq {L H CM RM ONE LV HV Y r : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hY : Canon 5 133 13 Y)
    (hr : r < 133) : rowL RM Y r = ∑ l ∈ range 133, lane 13 Y (133 * r + l) * 2 ^ (13 * l) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hRM, -⟩ := consts_facts hc
  rw [← rowG_eq hY hr, ← hRM]
  rfl

theorem rowL_mulC {L H CM RM ONE LV HV CM3 M A G n : Nat} {a : Nat → Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hcm : cmOK CM3 M = true)
    (hA : A = ∑ r ∈ range n, a r * 2 ^ (1729 * r)) (ha : ∀ r < n, a r < 2 ^ 399)
    (hG : Canon 5 133 13 G) {r : Nat} (hr : r < 133) (hrn : r < n) :
    rowL RM (mulC L H CM3 RM A G) r = ∑ l ∈ range 133,
      ((∑ k ∈ range 133, (a r / 2 ^ (3 * k) % 8) * lane 13 G (133 * k + l)) % 5) *
        2 ^ (13 * l) := by
  rw [rowL_eq hc (mulC_canon hc hcm hA ha hG) hr]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [mulC_lane hc hcm hA ha hG hr (Finset.mem_range.1 hl)]
  simp only [hrn, if_true]

private def spV (q u : Nat → Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => spV q u N + u N * 2 ^ (q N)

private theorem spV_succ (q u : Nat → Nat) (N : Nat) :
    spV q u (N + 1) = spV q u N + u N * 2 ^ (q N) := rfl

private theorem spV_sum (q u : Nat → Nat) : ∀ N, spV q u N = ∑ j ∈ range N, u j * 2 ^ (q j)
  | 0 => rfl
  | N + 1 => by rw [spV_succ, spV_sum q u N, Finset.sum_range_succ]

private theorem spV_lt (q u : Nat → Nat) (hq : ∀ j, q j + 3 ≤ q (j + 1)) (hu : ∀ j, u j < 8) :
    ∀ N, spV q u N < 2 ^ (q N) := by
  intro N
  induction N with
  | zero => exact Nat.two_pow_pos _
  | succ N ih =>
    rw [spV_succ]
    have h1 : u N * 2 ^ (q N) ≤ 7 * 2 ^ (q N) := Nat.mul_le_mul_right _ (by have := hu N; omega)
    have h2 : 2 ^ (q N + 3) ≤ 2 ^ (q (N + 1)) := Nat.pow_le_pow_right (by omega) (hq N)
    have h3 : 2 ^ (q N + 3) = 8 * 2 ^ (q N) := by rw [Nat.pow_add]; omega
    omega

private theorem and_split {A B a b w : Nat} (hA : A < 2 ^ w) (hB : B < 2 ^ w) :
    (A + a * 2 ^ w) &&& (B + b * 2 ^ w) = (A &&& B) + (a &&& b) * 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro n
  have hAB : A &&& B < 2 ^ w := Nat.and_lt_two_pow _ hB
  rw [Nat.add_comm A, Nat.add_comm B, Nat.add_comm (A &&& B), Nat.mul_comm a, Nat.mul_comm b,
    Nat.mul_comm (a &&& b), Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hA,
    Nat.testBit_two_pow_mul_add _ hB, Nat.testBit_two_pow_mul_add _ hAB]
  split <;> simp [Nat.testBit_and]

private theorem xor_split {A B a b w : Nat} (hA : A < 2 ^ w) (hB : B < 2 ^ w) :
    (A + a * 2 ^ w) ^^^ (B + b * 2 ^ w) = (A ^^^ B) + (a ^^^ b) * 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro n
  have hAB : A ^^^ B < 2 ^ w := Nat.xor_lt_two_pow hA hB
  rw [Nat.add_comm A, Nat.add_comm B, Nat.add_comm (A ^^^ B), Nat.mul_comm a, Nat.mul_comm b,
    Nat.mul_comm (a ^^^ b), Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hA,
    Nat.testBit_two_pow_mul_add _ hB, Nat.testBit_two_pow_mul_add _ hAB]
  split <;> simp [Nat.testBit_xor]

private theorem or_split {A B a b w : Nat} (hA : A < 2 ^ w) (hB : B < 2 ^ w) :
    (A + a * 2 ^ w) ||| (B + b * 2 ^ w) = (A ||| B) + (a ||| b) * 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro n
  have hAB : A ||| B < 2 ^ w := Nat.or_lt_two_pow hA hB
  rw [Nat.add_comm A, Nat.add_comm B, Nat.add_comm (A ||| B), Nat.mul_comm a, Nat.mul_comm b,
    Nat.mul_comm (a ||| b), Nat.testBit_or, Nat.testBit_two_pow_mul_add _ hA,
    Nat.testBit_two_pow_mul_add _ hB, Nat.testBit_two_pow_mul_add _ hAB]
  split <;> simp [Nat.testBit_or]

private theorem spV_and (q u v : Nat → Nat) (hq : ∀ j, q j + 3 ≤ q (j + 1)) (hu : ∀ j, u j < 8)
    (hv : ∀ j, v j < 8) (N : Nat) :
    spV q u N &&& spV q v N = spV q (fun j => u j &&& v j) N := by
  induction N with
  | zero => simp [spV]
  | succ N ih =>
    rw [spV_succ, spV_succ, spV_succ, and_split (spV_lt q u hq hu N) (spV_lt q v hq hv N), ih]

private theorem spV_xor (q u v : Nat → Nat) (hq : ∀ j, q j + 3 ≤ q (j + 1)) (hu : ∀ j, u j < 8)
    (hv : ∀ j, v j < 8) (N : Nat) :
    spV q u N ^^^ spV q v N = spV q (fun j => u j ^^^ v j) N := by
  induction N with
  | zero => simp [spV]
  | succ N ih =>
    rw [spV_succ, spV_succ, spV_succ, xor_split (spV_lt q u hq hu N) (spV_lt q v hq hv N), ih]

private theorem spV_or (q u v : Nat → Nat) (hq : ∀ j, q j + 3 ≤ q (j + 1)) (hu : ∀ j, u j < 8)
    (hv : ∀ j, v j < 8) (N : Nat) :
    spV q u N ||| spV q v N = spV q (fun j => u j ||| v j) N := by
  induction N with
  | zero => simp [spV]
  | succ N ih =>
    rw [spV_succ, spV_succ, spV_succ, or_split (spV_lt q u hq hu N) (spV_lt q v hq hv N), ih]

private theorem spV_shiftLeft (q u : Nat → Nat) (s N : Nat) :
    spV q u N <<< s = spV (fun j => q j + s) u N := by
  rw [Nat.shiftLeft_eq]
  induction N with
  | zero => simp [spV]
  | succ N ih =>
    rw [spV_succ, spV_succ, ← ih, Nat.add_mul, Nat.pow_add, Nat.mul_assoc]

private theorem spV_congr_pos (q q' u : Nat → Nat) (N : Nat)
    (h : ∀ j < N, u j = 0 ∨ q j = q' j) : spV q u N = spV q' u N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [spV_succ, spV_succ, ih (fun j hj => h j (by omega))]
    rcases h N (by omega) with h0 | h0 <;> simp [h0]

private theorem spV_congr_coef (q u v : Nat → Nat) (N : Nat)
    (h : ∀ j < N, u j = v j) : spV q u N = spV q v N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [spV_succ, spV_succ, ih (fun j hj => h j (by omega)), h N (by omega)]

private def spP (e j : Nat) : Nat := 3 * j + 10 * (j / 2 ^ e * 2 ^ e)

private def spG (t j : Nat) : Nat := if j / 2 ^ t % 2 = 1 then 7 else 0

private theorem spP_sep (e : Nat) : ∀ j, spP e j + 3 ≤ spP e (j + 1) := by
  intro j
  unfold spP
  have : j / 2 ^ e * 2 ^ e ≤ (j + 1) / 2 ^ e * 2 ^ e :=
    Nat.mul_le_mul_right _ (Nat.div_le_div_right (by omega))
  omega

private theorem spP_le (e : Nat) : spP e 133 ≤ 1729 := by
  unfold spP
  have := Nat.div_mul_le_self 133 (2 ^ e)
  omega

private theorem spP_step (t j : Nat) :
    (j / 2 ^ t % 2 = 1 → spP (t + 1) j + 10 * 2 ^ t = spP t j) ∧
    (j / 2 ^ t % 2 ≠ 1 → spP (t + 1) j = spP t j) := by
  unfold spP
  have hd : j / 2 ^ (t + 1) = j / 2 ^ t / 2 := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [hd, Nat.pow_succ]
  generalize j / 2 ^ t = d
  have hk : d = 2 * (d / 2) + d % 2 := (Nat.div_add_mod d 2).symm
  generalize d / 2 = k at hk
  constructor
  · intro h1
    rw [h1] at hk
    subst hk
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.one_mul]
    omega
  · intro h1
    have h0 : d % 2 = 0 := by omega
    rw [h0] at hk
    subst hk
    simp only [Nat.add_zero, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem and_seven {a : Nat} (ha : a < 8) : a &&& 7 = a := by
  rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt ha

private theorem sp_step (t : Nat) (f : Nat → Nat) (hf : ∀ j, f j < 8) (N : Nat) :
    (spV (spP (t + 1)) f N ^^^ (spV (spP (t + 1)) f N &&& spV (spP (t + 1)) (spG t) N)) |||
      ((spV (spP (t + 1)) f N &&& spV (spP (t + 1)) (spG t) N) <<< (10 * 2 ^ t)) =
        spV (spP t) f N := by
  have hg : ∀ j, spG t j < 8 := by intro j; unfold spG; split <;> omega
  let fa : Nat → Nat := fun j => if j / 2 ^ t % 2 = 1 then f j else 0
  let fb : Nat → Nat := fun j => if j / 2 ^ t % 2 = 1 then 0 else f j
  have hfa : ∀ j, fa j < 8 := by intro j; simp only [fa]; split <;> simp [hf]
  have hfb : ∀ j, fb j < 8 := by intro j; simp only [fb]; split <;> simp [hf]
  have hsep := spP_sep (t + 1)
  have e1 : spV (spP (t + 1)) f N &&& spV (spP (t + 1)) (spG t) N = spV (spP (t + 1)) fa N := by
    rw [spV_and _ _ _ hsep hf hg]
    apply spV_congr_coef
    intro j _
    simp only [spG, fa]
    split
    · exact and_seven (hf j)
    · exact Nat.and_zero _
  rw [e1, spV_xor _ _ _ hsep hf hfa, spV_shiftLeft]
  have e2 : spV (spP (t + 1)) (fun j => f j ^^^ fa j) N = spV (spP t) fb N := by
    rw [spV_congr_coef _ _ fb]
    · apply spV_congr_pos
      intro j _
      by_cases h : j / 2 ^ t % 2 = 1
      · left; simp [fb, h]
      · right; exact (spP_step t j).2 h
    · intro j _
      simp only [fa, fb]
      split
      · exact Nat.xor_self _
      · exact Nat.xor_zero _
  have e3 : spV (fun j => spP (t + 1) j + 10 * 2 ^ t) fa N = spV (spP t) fa N := by
    apply spV_congr_pos
    intro j _
    by_cases h : j / 2 ^ t % 2 = 1
    · right; exact (spP_step t j).1 h
    · left; simp [fa, h]
  rw [e2, e3, spV_or _ _ _ (spP_sep t) hfb hfa]
  apply spV_congr_coef
  intro j _
  simp only [fa, fb]
  split
  · exact Nat.zero_or _
  · exact Nat.or_zero _

private theorem rec_invN {α : Type} (z : α) (F : Nat → α → α) (P : Nat → α → Prop) (h0 : P 0 z)
    (hs : ∀ n a, P n a → P (n + 1) (F n a)) : ∀ n, P n (Nat.rec (motive := fun _ => α) z F n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact hs n _ ih

private theorem spG_lt (t : Nat) : ∀ j, spG t j < 8 := by
  intro j; unfold spG; split <;> omega

private theorem maskB_rec (t n : Nat) :
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => nIf(Nat.beq (Nat.land (Nat.shiftRight j t) (nat_lit 1)) (nat_lit 1),
        Nat.lor acc (Nat.shiftLeft (nat_lit 7) (Nat.add (Nat.mul (nat_lit 3) j)
          (Nat.mul (nat_lit 10) (Nat.shiftLeft (Nat.shiftRight j (Nat.succ t)) (Nat.succ t))))), acc))
      n : Nat) = spV (spP (t + 1)) (spG t) n := by
  refine rec_invN _ _ (fun n a => a = spV (spP (t + 1)) (spG t) n) rfl ?_ n
  intro n a ha
  subst ha
  beta_reduce
  rw [spV_succ]
  have hb : Nat.land (Nat.shiftRight n t) 1 = n / 2 ^ t % 2 := by
    change n >>> t &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  have hp : Nat.add (Nat.mul 3 n) (Nat.mul 10 (Nat.shiftLeft (Nat.shiftRight n (Nat.succ t))
      (Nat.succ t))) = spP (t + 1) n := by
    change 3 * n + 10 * ((n >>> (t + 1)) <<< (t + 1)) = _
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    rfl
  have hlt := spV_lt (spP (t + 1)) (spG t) (spP_sep (t + 1)) (spG_lt t) n
  rw [hb, hp]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ t) with h | h
  · have hg : spG t n = 0 := by simp [spG, h]
    rw [hg, h]
    show spV (spP (t + 1)) (spG t) n = _
    simp
  · have hg : spG t n = 7 := by simp [spG, h]
    rw [hg, h]
    show spV (spP (t + 1)) (spG t) n ||| 7 <<< spP (t + 1) n = _
    rw [Nat.shiftLeft_eq, Nat.or_comm, Nat.mul_comm 7, ← Nat.two_pow_add_eq_or_of_lt hlt]
    ring

private theorem maskB_eq (i : Nat) : maskB i = spV (spP (7 - i + 1)) (spG (7 - i)) 133 :=
  maskB_rec (7 - i) 133

private theorem masks_eq {MS : Nat} (hm : masksOK MS = true) : ∀ i < 8, CFSG.KC.HNLocal.mask MS i = maskB i := by
  unfold masksOK at hm
  have h := rec_bAnd (fun i => Nat.beq (CFSG.KC.HNLocal.mask MS i) (maskB i)) 8 (bAnd_true hm).2
  exact fun i hi => Nat.eq_of_beq_eq_true (h i hi)

private theorem sp_mod (x N : Nat) :
    x % 2 ^ (3 * N) = spV (fun j => 3 * j) (fun j => x / 2 ^ (3 * j) % 8) N := by
  induction N with
  | zero => simp [spV, Nat.mod_one]
  | succ N ih =>
    rw [show 3 * (N + 1) = 3 * N + 3 by omega, Nat.pow_add, Nat.mod_mul, ih, spV_succ,
      Nat.mul_comm (2 ^ (3 * N))]

private theorem sp_init {x : Nat} (hx : x < 2 ^ 399) :
    x = spV (spP 8) (fun j => x / 2 ^ (3 * j) % 8) 133 := by
  have h1 := sp_mod x 133
  rw [Nat.mod_eq_of_lt (show x < 2 ^ (3 * 133) from hx)] at h1
  refine h1.trans ?_
  apply spV_congr_pos
  intro j hj
  right
  unfold spP
  have : j / 2 ^ 8 = 0 := Nat.div_eq_of_lt (by norm_num; omega)
  rw [this]; simp

private theorem spP_zero : spP 0 = fun j => 13 * j := by
  funext j; unfold spP; simp; omega

private noncomputable def stS (k z : Nat) : Nat := spV (spP (8 - k)) (fun j => z / 2 ^ (3 * j) % 8) 133

private theorem stS_lt (k z : Nat) : stS k z < 2 ^ 1729 :=
  Nat.lt_of_lt_of_le (spV_lt _ _ (spP_sep _) (fun j => Nat.mod_lt _ (by omega)) 133)
    (Nat.pow_le_pow_right (by omega) (spP_le _))

private theorem shift_eq (k : Nat) :
    Nat.mul (nat_lit 10) (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 7) k)) = 10 * 2 ^ (7 - k) := by
  show 10 * (1 <<< (7 - k)) = _
  rw [Nat.one_shiftLeft]

private theorem stS_step {MS : Nat} (hm : masksOK MS = true) {k : Nat} (hk : k < 8) (z : Nat) :
    (stS k z ^^^ (stS k z &&& CFSG.KC.HNLocal.mask MS k)) ||| ((stS k z &&& CFSG.KC.HNLocal.mask MS k) <<< (10 * 2 ^ (7 - k))) =
      stS (k + 1) z := by
  unfold stS
  rw [masks_eq hm k hk, maskB_eq k, show 8 - k = 7 - k + 1 by omega,
    show 8 - (k + 1) = 7 - k by omega]
  exact sp_step (7 - k) _ (fun j => Nat.mod_lt _ (by omega)) 133

private theorem sp_iter {MS x : Nat} (hm : masksOK MS = true) (hx : x < 2 ^ 399) :
    ∀ k ≤ 8, (Nat.rec (motive := fun _ => Nat) x
      (fun i acc => CFSG.KC.Loop.strictN acc (fun a => sp1 a (CFSG.KC.HNLocal.mask MS i)
        (Nat.mul (nat_lit 10) (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 7) i)))))
      k : Nat) = stS k x := by
  refine rec_invN _ _ (fun k a => k ≤ 8 → a = stS k x) (fun _ => sp_init hx) ?_
  intro k a ih hk
  beta_reduce
  rw [ih (by omega), sN]
  unfold sp1
  rw [sN, shift_eq]
  exact stS_step hm (by omega) x

theorem spread_eq {MS x : Nat} (hm : masksOK MS = true) (hx : x < 2 ^ 399) :
    spread MS x = ∑ l ∈ range 133, (x / 2 ^ (3 * l) % 8) * 2 ^ (13 * l) := by
  have h := sp_iter hm hx 8 le_rfl
  unfold stS at h
  rw [Nat.sub_self, spP_zero, spV_sum] at h
  exact h

theorem spread_lane {MS x : Nat} (hm : masksOK MS = true) (hx : x < 2 ^ 399) {l : Nat}
    (hl : l < 133) : lane 13 (spread MS x) l = x / 2 ^ (3 * l) % 8 := by
  rw [spread_eq hm hx]
  have h := lane_pk (w := 13) (n := 133) (s := l) (g := fun j => x / 2 ^ (3 * j) % 8)
    (fun t _ => Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)) hl
  unfold pk at h
  exact h

open CFSG.KS.PackFld in
private theorem fld_xor {w A B : Nat} {g h : Nat → Nat} (hA : Fld w A g) (hB : Fld w B h) :
    Fld w (A ^^^ B) (fun i => g i ^^^ h i) := by
  intro i k hk
  rw [Nat.testBit_xor, hA i k hk, hB i k hk, Nat.testBit_xor]

open CFSG.KS.PackFld in
private theorem fld_shlb {w B s : Nat} {h : Nat → Nat} (hB : Fld w B h) (hsw : s ≤ w)
    (hs : ∀ i, h i <<< s < 2 ^ w) : Fld w (B <<< s) (fun i => h i <<< s) := by
  intro i k hk
  rw [Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  by_cases hks : s ≤ k
  · have e : w * i + k - s = w * i + (k - s) := by omega
    rw [e, hB i (k - s) (by omega)]
    simp [show w * i + k ≥ s by omega, show k ≥ s from hks]
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [show ¬ (w * 0 + k ≥ s) by omega, show ¬ (k ≥ s) by omega]
    · have hwi : w ≤ w * i := Nat.le_mul_of_pos_right w hi
      have e : w * i + k - s = w * (i - 1) + (w + k - s) := by
        have : w * i = w * (i - 1) + w := by
          conv_lhs => rw [show i = (i - 1) + 1 by omega]
          rw [Nat.mul_add, Nat.mul_one]
        omega
      have h2 : (h (i - 1) <<< s).testBit (w + k) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hs (i - 1))
          (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [Nat.testBit_shiftLeft] at h2
      simp only [show w + k ≥ s by omega, decide_true, Bool.true_and] at h2
      rw [e, hB (i - 1) _ (by omega), h2]
      simp [show ¬ (k ≥ s) by omega]

private theorem msf_eq {MS : Nat} {MSF : Nat → Nat} (hmsf : msfOK MS MSF = true) :
    ∀ i < 8, MSF i = ∑ r ∈ range 133, CFSG.KC.HNLocal.mask MS i * 2 ^ (1729 * r) := by
  intro i hi
  have h := rec_bAnd (fun i => Nat.beq (MSF i) (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Nat.lor acc (Nat.shiftLeft (CFSG.KC.HNLocal.mask MS i) (Nat.mul (nat_lit 1729) r)))
        (nat_lit 133))) 8 hmsf i hi
  rw [Nat.eq_of_beq_eq_true h]
  exact rec_or_sum (fun _ => CFSG.KC.HNLocal.mask MS i) (fun _ => Nat.and_lt_two_pow _ (by
    show (1 <<< 1729) - 1 < 2 ^ 1729
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)) 133

private noncomputable def stM (n : Nat) (x : Nat → Nat) (k r : Nat) : Nat :=
  if r < n then (if r < 133 then stS k (x r) else x r) else 0

private theorem stM_lt {n : Nat} {x : Nat → Nat} (hx : ∀ r < n, x r < 2 ^ 399) (k r : Nat) :
    stM n x k r < 2 ^ 1729 := by
  unfold stM
  split
  · split
    · exact stS_lt _ _
    · exact Nat.lt_of_lt_of_le (hx r (by omega)) (Nat.pow_le_pow_right (by omega) (by omega))
  · exact Nat.two_pow_pos _

private theorem stM_step {MS : Nat} (hm : masksOK MS = true) {n : Nat} {x : Nat → Nat}
    {k : Nat} (hk : k < 8) (r : Nat) :
    (stM n x k r ^^^ (stM n x k r &&& (if r < 133 then CFSG.KC.HNLocal.mask MS k else 0))) |||
      ((stM n x k r &&& (if r < 133 then CFSG.KC.HNLocal.mask MS k else 0)) <<< (10 * 2 ^ (7 - k))) =
        stM n x (k + 1) r := by
  unfold stM
  by_cases hrn : r < n
  · by_cases hr : r < 133
    · simp only [hrn, hr, if_true]
      exact stS_step hm hk _
    · simp [hrn, hr]
  · simp [hrn]

private theorem spM_iter {MS n CA : Nat} {MSF : Nat → Nat} {x : Nat → Nat}
    (hm : masksOK MS = true) (hmsf : msfOK MS MSF = true)
    (hCA : CA = ∑ r ∈ range n, x r * 2 ^ (1729 * r)) (hx : ∀ r < n, x r < 2 ^ 399) :
    ∀ k ≤ 8, CFSG.KS.PackFld.Fld 1729 (Nat.rec (motive := fun _ => Nat) CA
      (fun i acc => CFSG.KC.Loop.strictN acc (fun a => sp1 a (MSF i)
        (Nat.mul (nat_lit 10) (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 7) i)))))
      k : Nat) (stM n x k) := by
  refine rec_invN _ _ (fun k a => k ≤ 8 → CFSG.KS.PackFld.Fld 1729 a (stM n x k)) ?_ ?_
  · intro _
    rw [hCA]
    refine CFSG.KS.PackFld.fld_congr (fld_pk fun r hr => Nat.lt_of_lt_of_le (hx r hr)
      (Nat.pow_le_pow_right (by omega) (by omega))) fun r => ?_
    unfold stM stS
    split
    · split
      · exact sp_init (hx r (by omega))
      · rfl
    · rfl
  · intro k a ih hk
    have hA := ih (by omega)
    beta_reduce
    rw [sN]
    unfold sp1
    rw [sN, shift_eq]
    have hM : CFSG.KS.PackFld.Fld 1729 (MSF k) (fun r => if r < 133 then CFSG.KC.HNLocal.mask MS k else 0) := by
      rw [msf_eq hmsf k (by omega)]
      exact fld_pk fun _ _ => Nat.and_lt_two_pow _ (by
        show (1 <<< 1729) - 1 < 2 ^ 1729
        rw [Nat.shiftLeft_eq, Nat.one_mul]
        exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
    have hAM := fld_and hA hM
    have hsw : 10 * 2 ^ (7 - k) ≤ 1729 := by
      have : 2 ^ (7 - k) ≤ 2 ^ 7 := Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
      have h7 : (2 : Nat) ^ 7 = 128 := by norm_num
      omega
    have hb : ∀ r, (stM n x k r &&& (if r < 133 then CFSG.KC.HNLocal.mask MS k else 0)) <<< (10 * 2 ^ (7 - k)) <
        2 ^ 1729 := fun r => by
      have e := stM_step hm (n := n) (x := x) (k := k) (by omega) r
      have h2 := stM_lt hx (k + 1) r
      rw [← e] at h2
      exact Nat.lt_of_le_of_lt Nat.right_le_or h2
    refine CFSG.KS.PackFld.fld_congr
      (CFSG.KS.PackFld.fld_or (fld_xor hA hAM) (fld_shlb hAM hsw hb)) fun r => ?_
    exact stM_step hm (by omega) r

theorem spreadM_eq {MS n CA : Nat} {MSF : Nat → Nat} {x : Nat → Nat}
    (hm : masksOK MS = true) (hmsf : msfOK MS MSF = true)
    (hCA : CA = ∑ r ∈ range n, x r * 2 ^ (1729 * r)) (hx : ∀ r < n, x r < 2 ^ 399) :
    spreadM MSF CA = ∑ r ∈ range n,
      (if r < 133 then spread MS (x r) else x r) * 2 ^ (1729 * r) := by
  have h := spM_iter hm hmsf hCA hx 8 le_rfl
  have hb : ∀ r < n, (if r < 133 then spread MS (x r) else x r) < 2 ^ 1729 := fun r hr => by
    split
    · have e : spread MS (x r) = stS 8 (x r) := sp_iter hm (hx r hr) 8 le_rfl
      rw [e]
      exact stS_lt _ _
    · exact Nat.lt_of_lt_of_le (hx r hr) (Nat.pow_le_pow_right (by omega) (by omega))
  refine pk_of_fld (by omega) (CFSG.KS.PackFld.fld_congr h fun r => ?_) hb
  unfold stM
  split
  · split
    · rename_i hr _
      exact (sp_iter hm (hx r hr) 8 le_rfl).symm
    · rfl
  · rfl

theorem spread_eq_rowL {L H CM RM ONE LV HV CM3 M MS A G n r z : Nat} {a : Nat → Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hms : masksOK MS = true)
    (hcm : cmOK CM3 M = true)
    (hA : A = ∑ r ∈ range n, a r * 2 ^ (1729 * r)) (ha : ∀ r < n, a r < 2 ^ 399)
    (hG : Canon 5 133 13 G) (hr : r < 133) (hrn : r < n) (hz : z < 2 ^ 399)
    (h : spread MS z = rowL RM (mulC L H CM3 RM A G) r) :
    CCanon z ∧ cvec z = (OM G)ᵀ *ᵥ cvec (a r) := by
  have hf : ∀ l < 133, z / 2 ^ (3 * l) % 8 =
      (∑ k ∈ range 133, (a r / 2 ^ (3 * k) % 8) * lane 13 G (133 * k + l)) % 5 := by
    intro l hl
    have h1 : lane 13 (spread MS z) l = lane 13 (rowL RM (mulC L H CM3 RM A G) r) l :=
      congrArg (fun Y => lane 13 Y l) h
    rw [spread_lane hms hz hl, rowL_mulC hc hcm hA ha hG hr hrn] at h1
    rw [h1]
    have h2 := lane_pk (w := 13) (n := 133) (s := l)
      (g := fun l => (∑ k ∈ range 133, (a r / 2 ^ (3 * k) % 8) * lane 13 G (133 * k + l)) % 5)
      (fun t _ => Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)) hl
    unfold pk at h2
    exact h2
  refine ⟨⟨hz, fun j hj => by rw [hf j hj]; exact Nat.mod_lt _ (by norm_num)⟩, ?_⟩
  funext l
  rw [mulVec_cvec]
  unfold cvec
  rw [hf l l.isLt]

theorem fixVec_sound' {L H CM RM ONE LV HV CM3 M MS G x : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hms : masksOK MS = true) (hcm : cmOK CM3 M = true) (hG : Canon 5 133 13 G) (hx : x < 2 ^ 399)
    (h : fixVec MS L H CM3 RM G x = true) : CCanon x ∧ (OM G)ᵀ *ᵥ cvec x = cvec x := by
  have he : rowL RM (mulC L H CM3 RM x G) 0 = spread MS x := Nat.eq_of_beq_eq_true h
  obtain ⟨h1, h2⟩ := spread_eq_rowL (a := fun _ => x) (n := 1) hc hms hcm (by simp)
    (fun _ _ => hx) hG (by norm_num) (by norm_num) hx he.symm
  exact ⟨h1, h2.symm⟩

theorem actLeaf_sound' {L H CM RM ONE LV HV CM3 M MS : Nat} {XC PI : Nat → Nat} {nW G c nr : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (hms : masksOK MS = true)
    (hcm : cmOK CM3 M = true) (hG : Canon 5 133 13 G) (hnr : nr ≤ 133)
    (h : actLeaf XC PI M MS L H CM3 RM nW G c nr = true) :
    ∀ r < nr, PI (133 * c + r) < nW ∧ CCanon (recX XC M (PI (133 * c + r))) ∧
      cvec (recX XC M (PI (133 * c + r))) = (OM G)ᵀ *ᵥ cvec (recX XC M (133 * c + r)) := by
  intro r hr
  unfold actLeaf at h
  rw [letB_eq] at h
  have h1 := rec_bAnd (fun r => letB (PI (133 * c + r)) (fun k =>
    bAnd(Nat.blt k nW, Nat.beq (spread MS (recX XC M k))
      (rowL RM (mulC L H CM3 RM (leafA M (XC c) nr) G) r)))) nr h r hr
  rw [letB_eq] at h1
  obtain ⟨hk, he⟩ := bAnd_true h1
  have hk' : PI (133 * c + r) < nW := Nat.blt_eq.mp hk
  have he' := Nat.eq_of_beq_eq_true he
  have hz : recX XC M (PI (133 * c + r)) < 2 ^ 399 := recC_lt hcm _ _
  obtain ⟨h2, h3⟩ := spread_eq_rowL hc hms hcm (leafA_eq hcm (XC c) nr)
    (fun r _ => recC_lt hcm (XC c) r) hG (by omega) hr hz he'
  rw [recX_eq XC M c r (by omega)]
  exact ⟨hk', h2, h3⟩

end CFSG.KS.HNLocal.RowPf

end
