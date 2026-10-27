module

public import Certificates.Data.Kernel.Suz2301
public import CFSG.Certificates.Kernel.Fi22Snd.Rows
public import Certificates.Data.CFSGNative.Schreier.Refine
import CFSG.Certificates.Kernel.Fi22Snd.Colour

public section

namespace CFSG.KC.S2301

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.KC.Fi22Snd

@[expose] noncomputable def colOf (n X Q : Nat) : Array Nat :=
  Array.ofFn (n := n) fun v => xg X (rk Q v.val)

theorem colOf_size (n X Q : Nat) : (colOf n X Q).size = n := by
  simp [colOf]

theorem colOf_get {n X Q v : Nat} (hv : v < n) : (colOf n X Q)[v]! = xg X (rk Q v) := by
  rw [colOf, getElem!_ofFn_nat _ hv]

theorem unpack11_get {n B x : Nat} (hx : x < n) :
    (unpack n 11 B)[x]! = pg (nat_lit 11) (nat_lit 2047) B x := by
  rw [CFSG.KS.Raw.Orb.unpack_get hx]
  rfl

theorem unpack_size (n w P : Nat) : (unpack n w P).size = n := by
  simp [unpack]

theorem bindK_sound {n G B : Nat} (h : bindK n G B = true) : unpack n 12 G = unpack n 11 B := by
  have he := CFSG.KC.Pack.allN_spec h
  refine Array.ext (by rw [unpack_size, unpack_size]) fun x h1 h2 => ?_
  have hx : x < n := by rwa [unpack_size] at h1
  rw [← getElem!_pos _ x h1, ← getElem!_pos _ x h2, unpack12_get hx, unpack11_get hx]
  exact Nat.eq_of_beq_eq_true (he x hx)

theorem xg_strictMono {K X Q n : Nat} (htab : tabOK n K X Q = true) {a b : Nat} (hab : a < b)
    (hb : b < K) : xg X a < xg X b := by
  unfold tabOK at htab
  obtain ⟨h1, -⟩ := CFSG.KC.Pack.band_iff.1 htab
  have hs := CFSG.KC.Pack.allN_spec h1
  induction b with
  | zero => omega
  | succ b ih =>
    have hstep : xg X b < xg X (b + 1) :=
      Nat.le_of_ble_eq_true (hs b (by change b < K - 1; omega))
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
    · exact lt_trans (ih h (by omega)) hstep
    · exact hstep

theorem rk_lt {K X Q n : Nat} (htab : tabOK n K X Q = true) {v : Nat} (hv : v < n) : rk Q v < K := by
  unfold tabOK at htab
  obtain ⟨-, h2⟩ := CFSG.KC.Pack.band_iff.1 htab
  exact Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec h2 v hv)

private def fvK (x k : Nat) : Nat := x / 2 ^ (64 * k) % 2 ^ 64

private def HasF (m : Nat) (a : Nat → Nat) (x : Nat) : Prop :=
  x < 2 ^ (64 * m) ∧ ∀ k < m, fvK x k = a k

private theorem fvK_lt (x k : Nat) : fvK x k < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos 64)

private theorem hasF_lt {m : Nat} {a : Nat → Nat} {x : Nat} (h : HasF m a x) {k : Nat}
    (hk : k < m) : a k < 2 ^ 64 := by
  rw [← h.2 k hk]
  exact fvK_lt x k

private theorem hasF_sum {m : Nat} {a : Nat → Nat} (ha : ∀ k < m, a k < 2 ^ 64) :
    HasF m a (∑ k ∈ Finset.range m, a k * 2 ^ (64 * k)) :=
  ⟨packSum_lt m ha, fun k hk => by
    have h := packSum_get (w := 64) (g := a) m ha k
    rw [if_pos hk] at h
    exact h⟩

private theorem fvK_div (x k : Nat) : fvK (x / 2 ^ 64) k = fvK x (k + 1) := by
  unfold fvK
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 3
  ring

private theorem rep_of_lt : ∀ (m x : Nat), x < 2 ^ (64 * m) →
    x = ∑ k ∈ Finset.range m, fvK x k * 2 ^ (64 * k)
  | 0, x, h => by
    have : x = 0 := by simpa using h
    simp [this]
  | m + 1, x, h => by
    have h1 : x / 2 ^ 64 < 2 ^ (64 * m) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), ← pow_add]
      convert h using 2
    have ih := rep_of_lt m (x / 2 ^ 64) h1
    rw [Finset.sum_range_succ']
    have e : ∀ k ∈ Finset.range m, fvK x (k + 1) * 2 ^ (64 * (k + 1)) =
        2 ^ 64 * (fvK (x / 2 ^ 64) k * 2 ^ (64 * k)) := by
      intro k _
      rw [fvK_div, show 64 * (k + 1) = 64 + 64 * k by ring, pow_add]
      ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← ih]
    have h0 : fvK x 0 = x % 2 ^ 64 := by
      unfold fvK
      simp
    rw [h0]
    simp only [Nat.mul_zero, pow_zero, Nat.mul_one]
    exact (Nat.div_add_mod x (2 ^ 64)).symm

private theorem hasF_eq_sum {m : Nat} {a : Nat → Nat} {x : Nat} (h : HasF m a x) :
    x = ∑ k ∈ Finset.range m, a k * 2 ^ (64 * k) := by
  rw [rep_of_lt m x h.1]
  exact Finset.sum_congr rfl fun k hk => by rw [h.2 k (Finset.mem_range.1 hk)]

private theorem hasF_add {m : Nat} {a b : Nat → Nat} {x y : Nat} (hx : HasF m a x)
    (hy : HasF m b y) (hab : ∀ k < m, a k + b k < 2 ^ 64) :
    HasF m (fun k => a k + b k) (x + y) := by
  have e : x + y = ∑ k ∈ Finset.range m, (a k + b k) * 2 ^ (64 * k) := by
    rw [hasF_eq_sum hx, hasF_eq_sum hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => (Nat.add_mul _ _ _).symm
  rw [e]
  exact hasF_sum hab

private theorem hasF_mul {m : Nat} {a : Nat → Nat} {x : Nat} (c : Nat) (hx : HasF m a x)
    (hc : ∀ k < m, a k * c < 2 ^ 64) : HasF m (fun k => a k * c) (x * c) := by
  have e : x * c = ∑ k ∈ Finset.range m, (a k * c) * 2 ^ (64 * k) := by
    rw [hasF_eq_sum hx, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  exact hasF_sum hc

private theorem fvK_eq_and (x k : Nat) : fvK x k = (x >>> (64 * k)) &&& (2 ^ 64 - 1) := by
  unfold fvK
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem fvK_and (x y k : Nat) : fvK (x &&& y) k = fvK x k &&& fvK y k := by
  rw [fvK_eq_and, fvK_eq_and, fvK_eq_and, Nat.shiftRight_and_distrib]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and]
  cases (x >>> (64 * k)).testBit j <;> cases (y >>> (64 * k)).testBit j <;>
    cases (2 ^ 64 - 1).testBit j <;> rfl

private theorem hasF_and {m : Nat} {a b : Nat → Nat} {x y : Nat} (hx : HasF m a x)
    (hy : HasF m b y) : HasF m (fun k => a k &&& b k) (x &&& y) :=
  ⟨lt_of_le_of_lt Nat.and_le_left hx.1, fun k hk => by rw [fvK_and, hx.2 k hk, hy.2 k hk]⟩

private def redF (t : Nat) : Nat := t / 2 ^ 42 * 11 + t % 2 ^ 42

private theorem fvK_shr42 (x k : Nat) : fvK (x >>> 42) k % 2 ^ 22 = fvK x k / 2 ^ 42 := by
  unfold fvK
  rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num : 22 ≤ 64))]
  have h : (2 : Nat) ^ 64 = 2 ^ 42 * 2 ^ 22 := by norm_num
  rw [h, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ (64 * k))]

private theorem hasF_red {m : Nat} {a : Nat → Nat} {x L H : Nat}
    (hL : HasF m (fun _ => 2 ^ 42 - 1) L) (hH : HasF m (fun _ => 2 ^ 22 - 1) H)
    (hx : HasF m a x) : HasF m (fun k => redF (a k)) (redK L H x) := by
  have h1 : HasF m (fun k => a k / 2 ^ 42) (Nat.land (Nat.shiftRight x 42) H) :=
    ⟨lt_of_le_of_lt Nat.and_le_right hH.1, fun k hk => by
      show fvK ((x >>> 42) &&& H) k = _
      rw [fvK_and, hH.2 k hk, Nat.and_two_pow_sub_one_eq_mod, fvK_shr42, hx.2 k hk]⟩
  have h2 : HasF m (fun k => a k % 2 ^ 42) (Nat.land x L) := by
    have h := hasF_and hx hL
    refine ⟨h.1, fun k hk => ?_⟩
    show fvK (x &&& L) k = _
    rw [h.2 k hk]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have h3 := hasF_mul 11 h1 (fun k hk => by
    have := hasF_lt hx hk
    have : a k / 2 ^ 42 < 2 ^ 22 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 42), ← pow_add]
      exact this
    omega)
  have h4 := hasF_add h3 h2 (fun k hk => by
    have := hasF_lt hx hk
    have : a k / 2 ^ 42 < 2 ^ 22 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 42), ← pow_add]
      exact this
    have h5 : a k % 2 ^ 42 < 2 ^ 42 := Nat.mod_lt _ (Nat.two_pow_pos 42)
    omega)
  exact h4

private theorem pM_eq : pM = 4398046511093 := rfl

private theorem bM_eq : bM = 1000003 := rfl

private theorem redF_lt {t : Nat} (ht : t < 2 ^ 64) : redF t < 2 ^ 43 := by
  unfold redF
  omega

private theorem redF_mod (t : Nat) : redF t % pM = t % pM := by
  unfold redF
  rw [pM_eq]
  omega

private theorem hasF_step {m : Nat} {a wf : Nat → Nat} {h E L H Wm y : Nat}
    (hE : HasF m (fun _ => 1) E) (hL : HasF m (fun _ => 2 ^ 42 - 1) L)
    (hH : HasF m (fun _ => 2 ^ 22 - 1) H) (hh : HasF m a h) (ha : ∀ k < m, a k < 2 ^ 43)
    (hW : HasF m wf Wm) (hy : y ≤ 2 ^ 48) :
    HasF m (fun k => redF (a k + ((a k * 1000002 + y) &&& wf k))) (stepW E L H Wm y h) := by
  have h1 : HasF m (fun k => a k * 1000002) (h * 1000002) :=
    hasF_mul _ hh (fun k hk => by have := ha k hk; omega)
  have h2 : HasF m (fun _ => y) (y * E) := by
    have h := hasF_mul y hE (fun k hk => by simp; omega)
    rw [Nat.mul_comm y E]
    simpa using h
  have h3 : HasF m (fun k => a k * 1000002 + y) (h * 1000002 + y * E) :=
    hasF_add h1 h2 (fun k hk => by have := ha k hk; omega)
  have h4 := hasF_and h3 hW
  have h5 : HasF m (fun k => a k + ((a k * 1000002 + y) &&& wf k))
      (h + ((h * 1000002 + y * E) &&& Wm)) :=
    hasF_add hh h4 (fun k hk => by
      have := ha k hk
      have := Nat.and_le_left (n := a k * 1000002 + y) (m := wf k)
      omega)
  exact hasF_red hL hH h5

private theorem step_sel {m : Nat} {a wf : Nat → Nat} {h E L H Wm y : Nat} {sel : Nat → Bool}
    (hE : HasF m (fun _ => 1) E) (hL : HasF m (fun _ => 2 ^ 42 - 1) L)
    (hH : HasF m (fun _ => 2 ^ 22 - 1) H) (hh : HasF m a h) (ha : ∀ k < m, a k < 2 ^ 43)
    (hW : HasF m wf Wm) (hy : y ≤ 2 ^ 48)
    (hsel : ∀ p, p + 1 < m → wf (p + 1) = if sel p = true then 2 ^ 64 - 1 else 0) :
    ∃ a', HasF m a' (stepW E L H Wm y h) ∧ (∀ k < m, a' k < 2 ^ 43) ∧
      ∀ p, p + 1 < m →
        a' (p + 1) % pM = (if sel p = true then a (p + 1) * 1000003 + y else a (p + 1)) % pM := by
  refine ⟨_, hasF_step hE hL hH hh ha hW hy, fun k hk => ?_, fun p hp => ?_⟩
  · apply redF_lt
    have := ha k hk
    have := Nat.and_le_left (n := a k * 1000002 + y) (m := wf k)
    omega
  · show redF _ % pM = _
    rw [redF_mod]
    by_cases hs : sel p = true
    · have hlt : a (p + 1) * 1000002 + y < 2 ^ 64 := by have := ha (p + 1) hp; omega
      rw [hsel p hp, if_pos hs, if_pos hs, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
      have e : a (p + 1) + (a (p + 1) * 1000002 + y) = a (p + 1) * 1000003 + y := by omega
      rw [e]
    · rw [hsel p hp, if_neg hs, if_neg hs, Nat.and_zero, Nat.add_zero]

private theorem loop_inv {n : Nat} {E L H : Nat} {W c : Nat → Nat} {adj : Nat → Nat → Bool}
    (hE : HasF (n + 1) (fun _ => 1) E) (hL : HasF (n + 1) (fun _ => 2 ^ 42 - 1) L)
    (hH : HasF (n + 1) (fun _ => 2 ^ 22 - 1) H)
    (hWm : ∀ w < n, ∃ wf, HasF (n + 1) wf (W w) ∧
      ∀ p < n, wf (p + 1) = if adj w p = true then 2 ^ 64 - 1 else 0)
    (hc : ∀ w < n, c w + 1 ≤ 2 ^ 48) :
    ∀ (ws : List Nat), (∀ w ∈ ws, w < n) → ∀ (h0 : Nat) (a0 : Nat → Nat),
      HasF (n + 1) a0 h0 → (∀ k < n + 1, a0 k < 2 ^ 43) →
      ∃ a, HasF (n + 1) a (ws.foldl (fun h w => stepW E L H (W w) (c w + 1) h) h0) ∧
        (∀ k < n + 1, a k < 2 ^ 43) ∧
        ∀ v < n, a (v + 1) % pM = (ws.filter (fun w => adj w v)).foldl
          (fun x w => (x * 1000003 + c w + 1) % pM) (a0 (v + 1) % pM)
  | [], _, h0, a0, h0F, ha0 => ⟨a0, h0F, ha0, fun v hv => rfl⟩
  | w :: ws, hws, h0, a0, h0F, ha0 => by
    have hw : w < n := hws w List.mem_cons_self
    obtain ⟨wf, hwf, hsel⟩ := hWm w hw
    obtain ⟨a1, h1F, ha1, hmod⟩ := step_sel (sel := adj w) hE hL hH h0F ha0 hwf (hc w hw)
      (fun p hp => hsel p (by omega))
    obtain ⟨a, hF, ha, hv⟩ := loop_inv hE hL hH hWm hc ws
      (fun w' hw' => hws w' (List.mem_cons_of_mem _ hw')) _ a1 h1F ha1
    refine ⟨a, hF, ha, fun v hv' => ?_⟩
    rw [hv v hv', List.filter_cons]
    have hm := hmod v (by omega)
    by_cases hs : adj w v = true
    · rw [if_pos hs] at hm
      rw [if_pos hs, List.foldl_cons]
      have e : a1 (v + 1) % pM = (a0 (v + 1) % pM * 1000003 + c w + 1) % pM := by
        rw [hm, pM_eq]
        omega
      rw [e]
    · rw [if_neg hs] at hm
      rw [if_neg hs]
      rw [hm]

private theorem hasF_cons {m : Nat} {b : Nat → Nat} {x : Nat} (hx : HasF m b (x / 2 ^ 64)) :
    HasF (m + 1) (fun k => if k = 0 then x % 2 ^ 64 else b (k - 1)) x := by
  refine ⟨?_, fun k hk => ?_⟩
  · have := hx.1
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64), ← pow_add] at this
    convert this using 2
  · cases k with
    | zero =>
      show x / 2 ^ (64 * 0) % 2 ^ 64 = _
      simp
    | succ k =>
      rw [← fvK_div, hx.2 k (by omega)]
      simp

private theorem xg_lt (X k : Nat) : xg X k < 2 ^ 48 := by
  have h : xg X k = X / 2 ^ (48 * k) % 2 ^ 48 := CFSG.KC.Pack.fld_eq X (48 * k) 48
  rw [h]
  exact Nat.mod_lt _ (Nat.two_pow_pos 48)

private theorem vg_eq (C v : Nat) : vg C v = fvK C (v + 1) :=
  CFSG.KC.Pack.fld_eq C (64 * (v + 1)) 64

private theorem startK_lt (X Q T v : Nat) : startK X Q T v < pM :=
  Nat.mod_lt _ (by rw [pM_eq]; norm_num)

private theorem onesK_eq (n : Nat) : onesK n = ∑ v ∈ Finset.range (n + 1), 1 * 2 ^ (64 * v) := by
  have h := foldN_add (f := fun v a => Nat.add a (Nat.shiftLeft (nat_lit 1)
    (Nat.mul (nat_lit 64) v))) (g := fun v => 1 * 2 ^ (64 * v)) (fun v a => by
      change a + 1 <<< (64 * v) = _
      rw [Nat.shiftLeft_eq]) (n + 1) 0
  rw [Nat.zero_add] at h
  exact h

private theorem hasF_ones (n : Nat) : HasF (n + 1) (fun _ => 1) (onesK n) := by
  rw [onesK_eq]
  exact hasF_sum (a := fun _ => 1) (fun _ _ => by norm_num)

private theorem hasF_L (n : Nat) :
    HasF (n + 1) (fun _ => 2 ^ 42 - 1) (Nat.mul (onesK n) 4398046511103) := by
  have h := hasF_mul 4398046511103 (hasF_ones n) (fun k hk => by norm_num)
  simpa using h

private theorem hasF_H (n : Nat) :
    HasF (n + 1) (fun _ => 2 ^ 22 - 1) (Nat.mul (onesK n) 4194303) := by
  have h := hasF_mul 4194303 (hasF_ones n) (fun k hk => by norm_num)
  simpa using h

private theorem startVec_eq (n X Q T s : Nat) :
    startVec n X Q T s = s + ∑ v ∈ Finset.range n, startK X Q T v * 2 ^ (64 * (v + 1)) := by
  have h := foldN_add (f := fun v a => Nat.add a (Nat.shiftLeft (startK X Q T v)
    (Nat.mul (nat_lit 64) (Nat.add v (nat_lit 1)))))
    (g := fun v => startK X Q T v * 2 ^ (64 * (v + 1))) (fun v a => by
      change a + startK X Q T v <<< (64 * (v + 1)) = _
      rw [Nat.shiftLeft_eq]) n s
  exact h

private theorem hasF_start (n X Q T : Nat) :
    HasF (n + 1) (fun k => if k = 0 then 5 else startK X Q T (k - 1)) (startVec n X Q T 5) := by
  have h := hasF_sum (m := n + 1) (a := fun k => if k = 0 then 5 else startK X Q T (k - 1))
    (fun k hk => by
      split_ifs
      · norm_num
      · exact lt_trans (startK_lt X Q T _) (by rw [pM_eq]; norm_num))
  rw [startVec_eq]
  convert h using 1
  rw [Finset.sum_range_succ']
  simp
  omega

private theorem wmaskK_eq (d r : Nat) :
    wmaskK d r = 2 ^ 64 * ∑ i ∈ Finset.range d, (2 ^ 64 - 1) * 2 ^ (64 * rg r i) := by
  have h := foldN_add (f := fun i a => Nat.add a (Nat.shiftLeft (nat_lit 18446744073709551615)
    (Nat.mul (nat_lit 64) (Nat.add (rg r i) (nat_lit 1)))))
    (g := fun i => 2 ^ 64 * ((2 ^ 64 - 1) * 2 ^ (64 * rg r i))) (fun i a => by
      change a + 18446744073709551615 <<< (64 * (rg r i + 1)) = _
      rw [Nat.shiftLeft_eq, show 64 * (rg r i + 1) = 64 * rg r i + 64 by ring, pow_add]
      norm_num
      ring) d 0
  rw [Nat.zero_add, ← Finset.mul_sum] at h
  exact h

private theorem hasF_mask {n d w : Nat} {R M S W : Nat → Nat}
    (hrow : rowOK n d R M S w = true) (hmask : maskOK d R W w = true) :
    ∃ wf, HasF (n + 1) wf (W w) ∧
      ∀ p < n, wf (p + 1) = if p ∈ decodeRow d (R w) then 2 ^ 64 - 1 else 0 := by
  have h1 : W w / 2 ^ 64 = ∑ p ∈ Finset.range n,
      (if p ∈ decodeRow d (R w) then 2 ^ 64 - 1 else 0) * 2 ^ (64 * p) := by
    have e := Nat.eq_of_beq_eq_true hmask
    change W w >>> 64 = wmaskK d (R w) >>> 64 at e
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, wmaskK_eq,
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos 64)] at e
    rw [e]
    have e2 := row_sum_rg (R := R) (x := w) (d := d) (fun p => (2 ^ 64 - 1) * 2 ^ (64 * p))
    rw [e2, ← sum_ite_row hrow (fun p => (2 ^ 64 - 1) * 2 ^ (64 * p))]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  have h2 := hasF_sum (m := n) (a := fun p => if p ∈ decodeRow d (R w) then 2 ^ 64 - 1 else 0)
    (fun p _ => by split_ifs <;> norm_num)
  rw [← h1] at h2
  exact ⟨_, hasF_cons h2, fun p _ => by simp⟩

private theorem foldr_or_testBit (g : Nat → Nat) (q : Nat) :
    ∀ (l : List Nat) (s : Nat), (l.foldr (fun i a => a ||| 1 <<< g i) s).testBit q = true →
      s.testBit q = true ∨ ∃ i ∈ l, g i = q
  | [], s, h => Or.inl h
  | i :: l, s, h => by
    rw [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · rcases foldr_or_testBit g q l s h with h | ⟨j, hj, e⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, e⟩
    · right
      refine ⟨i, List.mem_cons_self, ?_⟩
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at h
      simpa using h

private theorem ordOK_facts {n Q O : Nat} (h : ordOK n Q O = true) :
    (∀ i < n, rg O i < n) ∧ (∀ i < n - 1, rk Q (rg O i) ≤ rk Q (rg O (i + 1))) ∧
      ∀ q < n, ∃ i < n, rg O i = q := by
  unfold ordOK at h
  obtain ⟨h1, h'⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h2, h3⟩ := CFSG.KC.Pack.band_iff.1 h'
  refine ⟨fun i hi => Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec h1 i hi),
    fun i hi => Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec h2 i hi), fun q hq => ?_⟩
  have e := Nat.eq_of_beq_eq_true h3
  rw [CFSG.KC.Pack.foldN_eq] at e
  have hb : ((List.range n).foldr (fun i a => a ||| 1 <<< rg O i) 0).testBit q = true := by
    change ((List.range n).foldr
      (fun i a => Nat.lor a (Nat.shiftLeft 1 (rg O i))) 0).testBit q = true
    rw [e]
    change ((1 <<< n) - 1).testBit q = true
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
    simpa using hq
  rcases foldr_or_testBit (rg O) q _ _ hb with h | ⟨i, hi, e⟩
  · simp at h
  · exact ⟨i, List.mem_range.1 hi, e⟩

private theorem range_map_perm {d : Nat} {π : Nat → Nat} (hlt : ∀ j < d, π j < d)
    (hon : ∀ i < d, ∃ j < d, π j = i) : List.Perm ((List.range d).map π) (List.range d) := by
  have himg : (Finset.range d).image π = Finset.range d := by
    ext i
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hlt j hj
    · intro hi
      exact hon i hi
  have hinj : Set.InjOn π (Finset.range d) :=
    Finset.injOn_of_card_image_eq (by rw [himg])
  have hnd : ((List.range d).map π).Nodup :=
    List.Nodup.map_on (fun a ha b hb e => hinj (by simpa using ha) (by simpa using hb) e)
      List.nodup_range
  refine (List.perm_ext_iff_of_nodup hnd List.nodup_range).2 fun i => ?_
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hlt j hj
  · exact hon i

private theorem pairwise_le_of_adj {d : Nat} {g : Nat → Nat}
    (h : ∀ j, j + 1 < d → g j ≤ g (j + 1)) : ((List.range d).map g).Pairwise (· ≤ ·) := by
  have hm : ∀ i j, i ≤ j → j < d → g i ≤ g j := by
    intro i j hij hj
    induction j with
    | zero =>
      have : i = 0 := by omega
      rw [this]
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hij) with hij' | rfl
      · exact Nat.le_trans (ih (by omega) (by omega)) (h j hj)
      · exact Nat.le_refl _
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp_of_mem fun {i j} _ hj hij =>
    hm i j (Nat.le_of_lt hij) (List.mem_range.1 hj)

private theorem xg_mono {K X Q n : Nat} (htab : tabOK n K X Q = true) {a b : Nat} (hab : a ≤ b)
    (hb : b < K) : xg X a ≤ xg X b := by
  rcases Nat.lt_or_ge a b with h | h
  · exact (xg_strictMono htab h hb).le
  · rw [Nat.le_antisymm hab h]

private theorem nbr_sorted {n d K X Q O v : Nat} {R M S : Nat → Nat} (hv : v < n)
    (hrow : ∀ x < n, rowOK n d R M S x = true) (htab : tabOK n K X Q = true)
    (hord : ordOK n Q O = true) :
    (((decodeRow d (R v)).map fun w => (colOf n X Q)[w]!).mergeSort fun a b => decide (a ≤ b)) =
      (((List.range n).map (rg O)).filter (fun w => decide (w ∈ decodeRow d (R v)))).map
        (fun w => xg X (rk Q w)) := by
  obtain ⟨hlt, hmono, hsurj⟩ := ordOK_facts hord
  have hperm_ws : ((List.range n).map (rg O)).Perm (List.range n) :=
    range_map_perm hlt hsurj
  have hperm1 : (((List.range n).map (rg O)).filter
      (fun w => decide (w ∈ decodeRow d (R v)))).Perm (decodeRow d (R v)) := by
    refine (hperm_ws.filter _).trans ?_
    refine (List.perm_ext_iff_of_nodup ((List.nodup_range).filter _)
      (row_pairwise (hrow v hv)).nodup).2 fun w => ?_
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨row_entry_lt (hrow v hv) h, h⟩⟩
  have e1 : (decodeRow d (R v)).map (fun w => (colOf n X Q)[w]!) =
      (decodeRow d (R v)).map (fun w => xg X (rk Q w)) :=
    List.map_congr_left fun w hw => colOf_get (row_entry_lt (hrow v hv) hw)
  rw [e1]
  symm
  refine List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2) ?_ ?_ ?_
  · have hp : ((List.range n).map (fun i => xg X (rk Q (rg O i)))).Pairwise (· ≤ ·) :=
      pairwise_le_of_adj fun j hj =>
        xg_mono htab (hmono j (by omega)) (rk_lt htab (hlt (j + 1) hj))
    have hp' : (((List.range n).map (rg O)).map (fun w => xg X (rk Q w))).Pairwise (· ≤ ·) := by
      rw [List.map_map]
      exact hp
    exact hp'.sublist (List.filter_sublist.map _)
  · exact List.sortedLE_iff_pairwise.1 List.sortedLE_mergeSort
  · exact (hperm1.map _).trans (List.mergeSort_perm _ _).symm

private theorem codesK_eq (n X Q T O : Nat) (W : Nat → Nat) :
    codesK n X Q T O W = ((List.range n).map (rg O)).foldl
      (fun h w => stepW (onesK n) (Nat.mul (onesK n) 4398046511103) (Nat.mul (onesK n) 4194303)
        (W w) (xg X (rk Q w) + 1) h) (startVec n X Q T 5) := by
  unfold codesK
  simp only [CFSG.KC.Pack.strictN_eq]
  rw [CFSG.KC.Pack.foldN_eq, List.foldl_map]
  exact CFSG.KC.Pack.foldr_rev (fun j s => stepW (onesK n) (Nat.mul (onesK n) 4398046511103)
    (Nat.mul (onesK n) 4194303) (W (rg O j)) (xg X (rk Q (rg O j)) + 1) s) n _

private theorem sigCode_singleton (a y : Nat) :
    sigCode a [y] = ((a + 7) % 4398046511093 * 1000003 + y + 1) % 4398046511093 := by
  unfold sigCode
  rw [List.foldl_cons, List.foldl_nil]

private theorem sigCode_eq_foldl (a : Nat) (l : List Nat) :
    sigCode a l = l.foldl (fun h x => (h * 1000003 + x + 1) % 4398046511093)
      ((a + 7) % 4398046511093) := rfl

private theorem startK_eq (X Q T v : Nat) :
    startK X Q T v = (((xg X (rk Q v) + 7) % 4398046511093 * 1000003 +
      (xg X (rk Q (tg T v)) + 1)) % 4398046511093 + 7) % 4398046511093 := by
  unfold startK
  rw [pM_eq, bM_eq]
  rfl

theorem round_sound {n d K X Q X' Q' T O : Nat} {R M S W : Nat → Nat} (hn : n < 2048)
    (hrow : ∀ x < n, rowOK n d R M S x = true)
    (hsym : ∀ x < n, ∀ y < n, y ∈ decodeRow d (R x) → x ∈ decodeRow d (R y))
    (hmask : ∀ x < n, maskOK d R W x = true) (htab : tabOK n K X Q = true)
    (hord : ordOK n Q O = true) (hT : ∀ v < n, tg T v < n)
    (hr : roundOK n X Q X' Q' T O W = true) :
    ∀ v < n, sigCode (sigCode (colOf n X Q)[v]! [(colOf n X Q)[(unpack n 12 T)[v]!]!])
      (nbrColours (rowsArr n d R) (colOf n X Q) v) = (colOf n X' Q')[v]! := by
  have _ := hn
  intro v hv
  obtain ⟨hlt, -, -⟩ := ordOK_facts hord
  have hws : ∀ w ∈ (List.range n).map (rg O), w < n := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
    exact hlt i (List.mem_range.1 hi)
  have h5 : (5 : Nat) < 2 ^ 43 := by norm_num
  obtain ⟨a, hF, -, hmod⟩ := loop_inv (n := n) (E := onesK n)
    (L := Nat.mul (onesK n) 4398046511103) (H := Nat.mul (onesK n) 4194303) (W := W)
    (c := fun w => xg X (rk Q w)) (adj := fun w p => decide (p ∈ decodeRow d (R w)))
    (hasF_ones n) (hasF_L n) (hasF_H n)
    (fun w hw => by
      obtain ⟨wf, h1, h2⟩ := hasF_mask (hrow w hw) (hmask w hw)
      exact ⟨wf, h1, fun p hp => by rw [h2 p hp]; simp⟩)
    (fun w _ => by have := xg_lt X (rk Q w); omega)
    _ hws (startVec n X Q T 5) _ (hasF_start n X Q T)
    (fun k hk => by
      split_ifs
      · exact h5
      · exact lt_trans (startK_lt X Q T _) (by rw [pM_eq]; norm_num))
  rw [← codesK_eq] at hF
  have hvg : vg (codesK n X Q T O W) v = a (v + 1) := by
    rw [vg_eq]
    exact hF.2 (v + 1) (by omega)
  have hv1 := hmod v hv
  have hrr : vg (codesK n X Q T O W) v % pM = xg X' (rk Q' v) := by
    have h : roundOK n X Q X' Q' T O W = true := hr
    unfold roundOK at h
    rw [CFSG.KC.Pack.strictB_eq] at h
    exact Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec h v hv)
  have e1 : (colOf n X' Q')[v]! = xg X' (rk Q' v) := colOf_get hv
  have e2 : (colOf n X Q)[v]! = xg X (rk Q v) := colOf_get hv
  have e3 : (unpack n 12 T)[v]! = tg T v := unpack12_get hv
  have e4 : (colOf n X Q)[tg T v]! = xg X (rk Q (tg T v)) := colOf_get (hT v hv)
  have e5 : nbrColours (rowsArr n d R) (colOf n X Q) v =
      (((List.range n).map (rg O)).filter (fun w => decide (w ∈ decodeRow d (R v)))).map
        (fun w => xg X (rk Q w)) := by
    unfold nbrColours
    rw [rowsArr_get hv]
    exact nbr_sorted hv hrow htab hord
  have hfilt : ((List.range n).map (rg O)).filter (fun w => decide (v ∈ decodeRow d (R w))) =
      ((List.range n).map (rg O)).filter (fun w => decide (w ∈ decodeRow d (R v))) := by
    refine List.filter_congr fun w hw => ?_
    have hwn := hws w hw
    exact decide_eq_decide.2 ⟨hsym w hwn v hv, hsym v hv w hwn⟩
  have e6 : (sigCode (xg X (rk Q v)) [xg X (rk Q (tg T v))] + 7) % 4398046511093 =
      startK X Q T v := by
    rw [sigCode_singleton, startK_eq, Nat.add_assoc (_ * 1000003) (xg X (rk Q (tg T v))) 1]
  have hv2 : a (v + 1) % pM = List.foldl (fun x w => (x * 1000003 + xg X (rk Q w) + 1) % pM)
      (startK X Q T v)
      (((List.range n).map (rg O)).filter (fun w => decide (w ∈ decodeRow d (R v)))) := by
    rw [hv1, hfilt]
    have h : (if v + 1 = 0 then 5 else startK X Q T (v + 1 - 1)) % pM = startK X Q T v := by
      rw [if_neg (Nat.succ_ne_zero v)]
      exact Nat.mod_eq_of_lt (startK_lt X Q T v)
    rw [h]
  rw [e1, e2, e3, e4, e5, ← hrr, hvg, hv2, sigCode_eq_foldl, e6, List.foldl_map, pM_eq]

theorem set_get_eq {c : Array Nat} {p x : Nat} (hp : p < c.size) : (c.set! p x)[p]! = x := by
  rw [getElem!_pos _ p (by simpa using hp)]
  simp [Array.set!]

theorem set_get_ne {c : Array Nat} {p q x : Nat} (hq : q < c.size) (hpq : p ≠ q) :
    (c.set! p x)[q]! = c[q]! := by
  rw [getElem!_pos _ q (by simpa using hq), getElem!_pos c q hq]
  exact Array.getElem_setIfInBounds_ne hq hpq

theorem indiv_sound {n X Q X' Q' p j : Nat} (h : ∀ v < n, indivOK X Q X' Q' p j v = true) :
    colOf n X' Q' = (colOf n X Q).set! p (pM + j) := by
  refine Array.ext (by simp [colOf_size]) fun v h1 h2 => ?_
  have hv : v < n := by rwa [colOf_size] at h1
  rw [← getElem!_pos _ v h1, ← getElem!_pos _ v h2, colOf_get hv]
  have e := Nat.eq_of_beq_eq_true (h v hv)
  rw [e]
  by_cases hvp : v = p
  · subst hvp
    rw [Nat.beq_refl, set_get_eq (by rw [colOf_size]; exact hv)]
    rfl
  · have hb : Nat.beq v p = false := by
      cases e' : Nat.beq v p
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e') hvp
    rw [hb, set_get_ne (by rw [colOf_size]; exact hv) (Ne.symm hvp), colOf_get hv]

theorem colOf_eq_iff {K X Q n : Nat} (htab : tabOK n K X Q = true) {v w : Nat} (hv : v < n)
    (hw : w < n) : (colOf n X Q)[v]! = (colOf n X Q)[w]! ↔ rk Q v = rk Q w := by
  rw [colOf_get hv, colOf_get hw]
  constructor
  · intro h
    rcases Nat.lt_trichotomy (rk Q v) (rk Q w) with h' | h' | h'
    · exact absurd h (Nat.ne_of_lt (xg_strictMono htab h' (rk_lt htab hw)))
    · exact h'
    · exact absurd h (Nat.ne_of_gt (xg_strictMono htab h' (rk_lt htab hv)))
  · intro h
    rw [h]

theorem cellCntK_eq (n Q q : Nat) :
    cellCntK n Q q = (List.range n).countP fun w => rk Q w == q := by
  rw [cellCntK, CFSG.KC.Pack.foldN_eq]
  have key : ∀ m s, (List.range m).foldr
      (fun w a => nIf(Nat.beq (rk Q w) q, Nat.add a (nat_lit 1), a)) s =
      s + (List.range m).countP fun w => rk Q w == q := by
    intro m
    induction m with
    | zero => intro s; rfl
    | succ m ih =>
      intro s
      rw [List.range_succ, List.foldr_append, List.countP_append, List.foldr_cons, List.foldr_nil,
        ih, List.countP_singleton]
      have e : (rk Q m == q) = Nat.beq (rk Q m) q := rfl
      rw [e]
      cases Nat.beq (rk Q m) q
      · rfl
      · change s + 1 + _ = s + (_ + if true = true then 1 else 0)
        rw [if_pos rfl]
        omega
  have h := key n 0
  rw [Nat.zero_add] at h
  exact h

end CFSG.KC.S2301

end
