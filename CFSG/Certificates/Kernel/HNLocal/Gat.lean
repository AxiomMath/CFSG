module

public import Certificates.Data.Kernel.HNLocalK
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.HNLocal.GatPf

open CFSG.KC.HNLocal CFSG.KC.Loop Finset

theorem letB_eq (y : Nat) (k : Nat → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem bAnd_iff {a b : Bool} : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := by
  cases a <;> simp

theorem nIf_beq (a b t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t (Nat.beq a b) = if a = b then t else e := by
  cases hb : Nat.beq a b
  · rw [if_neg (Nat.ne_of_beq_eq_false hb)]
  · rw [if_pos (Nat.eq_of_beq_eq_true hb)]

theorem nIf_ble (a b : Nat) : Bool.rec (motive := fun _ => Nat) b a (Nat.ble a b) = min a b := by
  cases hb : Nat.ble a b
  · have : ¬ a ≤ b := fun h => by simp [Nat.ble_eq_true_of_le h] at hb
    simp only
    omega
  · have := Nat.le_of_ble_eq_true hb
    simp only
    omega

theorem recC_eq (M C r : Nat) : recC M C r = C >>> (400 * r) &&& M := rfl

theorem recX_eq (XC : Nat → Nat) (M k : Nat) : recX XC M k = recC M (XC (k / 133)) (k % 133) := rfl

theorem childF_eq (h t : Nat) : childF h t = h >>> (30 + 9 * t) &&& 511 := rfl

theorem rowL_eq (RM Y r : Nat) : rowL RM Y r = Y >>> (1729 * r) &&& RM := rfl

theorem chunk3_eq (XC : Nat → Nat) (c : Nat) : chunk3 XC c =
    (XC (c / 133) ||| (XC (c / 133 + 1) <<< 53200 ||| XC (c / 133 + 2) <<< 106400)) >>>
      (400 * (c - 133 * (c / 133))) := rfl

theorem recC_mod (C r : Nat) : recC (2 ^ 399 - 1) C r = C / 2 ^ (400 * r) % 2 ^ 399 := by
  rw [recC_eq, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem recC_lt {M : Nat} (hM : M = 2 ^ 399 - 1) (C r : Nat) : recC M C r < 2 ^ 1729 := by
  subst hM
  rw [recC_mod]
  exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by norm_num)
    (by norm_num))

private theorem childrenOK_succ (h j c n t : Nat) : childrenOK h j c (n + 1) t =
    letB (childF h t >>> 1) (fun r => bAnd(Nat.blt r 133,
      bAnd(Nat.blt (133 * j + r) (c + t), childrenOK h j c n (t + 1)))) := rfl

theorem childrenOK_spec {h j c : Nat} : ∀ {n t0 : Nat}, childrenOK h j c n t0 = true →
    ∀ t, t0 ≤ t → t < t0 + n → childF h t / 2 < 133 ∧ 133 * j + childF h t / 2 < c + t
  | 0, t0, _, t, h1, h2 => absurd h2 (by omega)
  | n + 1, t0, hc, t, h1, h2 => by
    rw [childrenOK_succ, letB_eq] at hc
    simp only [bAnd_iff, Nat.blt_eq, Nat.shiftRight_eq_div_pow, pow_one] at hc
    rcases Nat.eq_or_lt_of_le h1 with e | lt
    · subst e
      exact ⟨hc.1, hc.2.1⟩
    · exact childrenOK_spec hc.2.2 t (by omega) (by omega)

private theorem bit_lo {x K : Nat} (hx : x < 2 ^ 53200) (hK : 53200 ≤ K) : x.testBit K = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hK))

theorem chunk3_rec {XC : Nat → Nat} {M c t : Nat} (hM : M = 2 ^ 399 - 1) (hct : c % 133 + t < 399)
    (hXC : ∀ i, c / 133 ≤ i → i < (c + t) / 133 → XC i < 2 ^ 53200) :
    recC M (chunk3 XC c) t = recX XC M (c + t) := by
  subst hM
  rw [recX_eq, recC_mod, recC_mod, chunk3_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_shiftRight,
    Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 399
  · simp only [hi, decide_true, Bool.true_and]
    rcases (show c % 133 + t < 133 ∨ (133 ≤ c % 133 + t ∧ c % 133 + t < 266) ∨
        266 ≤ c % 133 + t by omega) with h0 | h1 | h2
    · have hq : (c + t) / 133 = c / 133 := by omega
      have h5 : ¬ 400 * (c - 133 * (c / 133)) + (i + 400 * t) ≥ 53200 := by omega
      have h6 : ¬ 400 * (c - 133 * (c / 133)) + (i + 400 * t) ≥ 106400 := by omega
      rw [hq, show i + 400 * ((c + t) % 133) = 400 * (c - 133 * (c / 133)) + (i + 400 * t) by
        omega]
      simp [h5, h6]
    · have hq : (c + t) / 133 = c / 133 + 1 := by omega
      have h5 : 400 * (c - 133 * (c / 133)) + (i + 400 * t) ≥ 53200 := by omega
      have h6 : ¬ 400 * (c - 133 * (c / 133)) + (i + 400 * t) ≥ 106400 := by omega
      rw [hq, bit_lo (hXC _ le_rfl (by omega)) h5,
        show i + 400 * ((c + t) % 133) = 400 * (c - 133 * (c / 133)) + (i + 400 * t) - 53200 by
          omega]
      simp [h5, h6]
    · have hq : (c + t) / 133 = c / 133 + 2 := by omega
      have h5 : 400 * (c - 133 * (c / 133)) + (i + 400 * t) ≥ 53200 := by omega
      have h6 : 400 * (c - 133 * (c / 133)) + (i + 400 * t) ≥ 106400 := by omega
      rw [hq, bit_lo (hXC _ le_rfl (by omega)) h5,
        bit_lo (hXC (c / 133 + 1) (by omega) (by omega)) (show 53200 ≤
          400 * (c - 133 * (c / 133)) + (i + 400 * t) - 53200 by omega),
        show i + 400 * ((c + t) % 133) = 400 * (c - 133 * (c / 133)) + (i + 400 * t) - 106400 by
          omega]
      simp [h5, h6]
  · simp [hi]

private theorem gat_succ_raw (M C CH h : Nat) (fin : Nat → Nat → Nat → Nat → Bool)
    (n t PA CA nA PB CB nB : Nat) : gat M C CH h fin (n + 1) t PA CA nA PB CB nB =
    letB (childF h t) (fun e => letB (recC M C (e >>> 1)) (fun p => letB (recC M CH t) (fun x =>
      Bool.rec (motive := fun _ => Bool)
        (letB (PA ||| p <<< (1729 * nA)) (fun PA' => letB (CA ||| x <<< (1729 * nA)) (fun CA' =>
          gat M C CH h fin n (t + 1) PA' CA' (nA + 1) PB CB nB)))
        (letB (PB ||| p <<< (1729 * nB)) (fun PB' => letB (CB ||| x <<< (1729 * nB)) (fun CB' =>
          gat M C CH h fin n (t + 1) PA CA nA PB' CB' (nB + 1))))
        (Nat.beq (e &&& 1) 1)))) := rfl

theorem gat_succ (M C CH h : Nat) (fin : Nat → Nat → Nat → Nat → Bool)
    (n t PA CA nA PB CB nB : Nat) : gat M C CH h fin (n + 1) t PA CA nA PB CB nB =
    if childF h t % 2 = 1 then
      gat M C CH h fin n (t + 1) PA CA nA (PB ||| recC M C (childF h t / 2) <<< (1729 * nB))
        (CB ||| recC M CH t <<< (1729 * nB)) (nB + 1)
    else
      gat M C CH h fin n (t + 1) (PA ||| recC M C (childF h t / 2) <<< (1729 * nA))
        (CA ||| recC M CH t <<< (1729 * nA)) (nA + 1) PB CB nB := by
  rw [gat_succ_raw]
  simp only [letB_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, pow_one]
  rcases Nat.mod_two_eq_zero_or_one (childF h t) with h0 | h0
  · rw [h0, if_neg (by omega)]
    rfl
  · rw [h0, if_pos rfl]
    rfl

private noncomputable def S (h ℓ : Nat) (f : Nat → Nat) (T : Nat) : Nat :=
  ∑ t ∈ (range T).filter (fun t => childF h t % 2 = ℓ),
    f t * 2 ^ (1729 * ((range t).filter fun t' => childF h t' % 2 = childF h t % 2).card)

private noncomputable def nc (h ℓ T : Nat) : Nat := ((range T).filter fun t => childF h t % 2 = ℓ).card

private theorem S_succ_of_eq {h ℓ T : Nat} {f : Nat → Nat} (hT : childF h T % 2 = ℓ) :
    S h ℓ f (T + 1) = S h ℓ f T + f T * 2 ^ (1729 * nc h ℓ T) := by
  unfold S nc
  rw [range_add_one, filter_insert, if_pos hT, sum_insert (by simp), add_comm, hT]

private theorem S_succ_of_ne {h ℓ T : Nat} {f : Nat → Nat} (hT : childF h T % 2 ≠ ℓ) :
    S h ℓ f (T + 1) = S h ℓ f T := by
  unfold S
  rw [range_add_one, filter_insert, if_neg hT]

private theorem nc_succ_of_eq {h ℓ T : Nat} (hT : childF h T % 2 = ℓ) :
    nc h ℓ (T + 1) = nc h ℓ T + 1 := by
  unfold nc
  rw [range_add_one, filter_insert, if_pos hT, card_insert_of_notMem (by simp)]

private theorem nc_succ_of_ne {h ℓ T : Nat} (hT : childF h T % 2 ≠ ℓ) :
    nc h ℓ (T + 1) = nc h ℓ T := by
  unfold nc
  rw [range_add_one, filter_insert, if_neg hT]

private theorem S_lt {h ℓ : Nat} {f : Nat → Nat} (hf : ∀ t, f t < 2 ^ 1729) :
    ∀ T, S h ℓ f T < 2 ^ (1729 * nc h ℓ T)
  | 0 => by simp [S, nc]
  | T + 1 => by
    by_cases hT : childF h T % 2 = ℓ
    · rw [S_succ_of_eq hT, nc_succ_of_eq hT, Nat.mul_succ, pow_add]
      have h1 := S_lt (h := h) (ℓ := ℓ) hf T
      have h2 : f T + 1 ≤ 2 ^ 1729 := hf T
      calc S h ℓ f T + f T * 2 ^ (1729 * nc h ℓ T)
          < 2 ^ (1729 * nc h ℓ T) + f T * 2 ^ (1729 * nc h ℓ T) := by omega
        _ = (f T + 1) * 2 ^ (1729 * nc h ℓ T) := by ring
        _ ≤ 2 ^ 1729 * 2 ^ (1729 * nc h ℓ T) := Nat.mul_le_mul_right _ h2
        _ = _ := Nat.mul_comm _ _
    · rw [S_succ_of_ne hT, nc_succ_of_ne hT]
      exact S_lt hf T

private theorem lor_step {h ℓ T : Nat} {f : Nat → Nat} (hf : ∀ t, f t < 2 ^ 1729)
    (hT : childF h T % 2 = ℓ) : S h ℓ f T ||| f T <<< (1729 * nc h ℓ T) = S h ℓ f (T + 1) := by
  rw [S_succ_of_eq hT, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (S_lt (h := h) (ℓ := ℓ) hf T), Nat.shiftLeft_eq,
    Nat.add_comm]

private theorem gat_go {M C CH h : Nat} {fin : Nat → Nat → Nat → Nat → Bool}
    (hp : ∀ t, recC M C (childF h t / 2) < 2 ^ 1729) (hx : ∀ t, recC M CH t < 2 ^ 1729) :
    ∀ n t0, gat M C CH h fin n t0 (S h 0 (fun t => recC M C (childF h t / 2)) t0)
      (S h 0 (fun t => recC M CH t) t0) (nc h 0 t0)
      (S h 1 (fun t => recC M C (childF h t / 2)) t0) (S h 1 (fun t => recC M CH t) t0) (nc h 1 t0) =
      fin (S h 0 (fun t => recC M C (childF h t / 2)) (t0 + n)) (S h 0 (fun t => recC M CH t) (t0 + n))
        (S h 1 (fun t => recC M C (childF h t / 2)) (t0 + n)) (S h 1 (fun t => recC M CH t) (t0 + n))
  | 0, t0 => rfl
  | n + 1, t0 => by
    rw [gat_succ, show t0 + (n + 1) = t0 + 1 + n by omega, ← gat_go (fin := fin) hp hx n (t0 + 1)]
    rcases Nat.mod_two_eq_zero_or_one (childF h t0) with h0 | h0
    · have h1 : childF h t0 % 2 ≠ 1 := by omega
      rw [if_neg h1, S_succ_of_ne (f := fun t => recC M C (childF h t / 2)) h1,
        S_succ_of_ne (f := fun t => recC M CH t) h1, nc_succ_of_ne h1, nc_succ_of_eq h0,
        ← lor_step (f := fun t => recC M C (childF h t / 2)) hp h0,
        ← lor_step (f := fun t => recC M CH t) hx h0]
    · have h1 : childF h t0 % 2 ≠ 0 := by omega
      rw [if_pos h0, S_succ_of_ne (f := fun t => recC M C (childF h t / 2)) h1,
        S_succ_of_ne (f := fun t => recC M CH t) h1, nc_succ_of_ne h1, nc_succ_of_eq h0,
        ← lor_step (f := fun t => recC M C (childF h t / 2)) hp h0,
        ← lor_step (f := fun t => recC M CH t) hx h0]

theorem gat_eq {M C CH h : Nat} (hM : M = 2 ^ 399 - 1) (fin : Nat → Nat → Nat → Nat → Bool)
    (n : Nat) : gat M C CH h fin n 0 0 0 0 0 0 0 =
    fin (∑ t ∈ (range n).filter (fun t => childF h t % 2 = 0), recC M C (childF h t / 2) *
          2 ^ (1729 * ((range t).filter fun t' => childF h t' % 2 = childF h t % 2).card))
      (∑ t ∈ (range n).filter (fun t => childF h t % 2 = 0), recC M CH t *
          2 ^ (1729 * ((range t).filter fun t' => childF h t' % 2 = childF h t % 2).card))
      (∑ t ∈ (range n).filter (fun t => childF h t % 2 = 1), recC M C (childF h t / 2) *
          2 ^ (1729 * ((range t).filter fun t' => childF h t' % 2 = childF h t % 2).card))
      (∑ t ∈ (range n).filter (fun t => childF h t % 2 = 1), recC M CH t *
          2 ^ (1729 * ((range t).filter fun t' => childF h t' % 2 = childF h t % 2).card)) := by
  have := gat_go (fin := fin) (h := h) (fun t => recC_lt hM C (childF h t / 2))
    (fun t => recC_lt hM CH t) n 0
  simp only [zero_add] at this
  exact this

theorem gat_spec {M C CH h : Nat} (hM : M = 2 ^ 399 - 1) {fin : Nat → Nat → Nat → Nat → Bool}
    {n : Nat} (hg : gat M C CH h fin n 0 0 0 0 0 0 0 = true) :
    fin (∑ t ∈ (range n).filter (fun t => childF h t % 2 = 0), recC M C (childF h t / 2) *
          2 ^ (1729 * ((range t).filter fun t' => childF h t' % 2 = childF h t % 2).card))
      (∑ t ∈ (range n).filter (fun t => childF h t % 2 = 0), recC M CH t *
          2 ^ (1729 * ((range t).filter fun t' => childF h t' % 2 = childF h t % 2).card))
      (∑ t ∈ (range n).filter (fun t => childF h t % 2 = 1), recC M C (childF h t / 2) *
          2 ^ (1729 * ((range t).filter fun t' => childF h t' % 2 = childF h t % 2).card))
      (∑ t ∈ (range n).filter (fun t => childF h t % 2 = 1), recC M CH t *
          2 ^ (1729 * ((range t).filter fun t' => childF h t' % 2 = childF h t % 2).card)) =
      true := by
  rw [gat_eq (C := C) (CH := CH) (h := h) hM fin n] at hg
  exact hg

private theorem fixRows_succ_raw (RM Y r : Nat) : fixRows RM Y (r + 1) =
    strictN (rowL RM Y r) (fun y => fixRows RM Y r +
      (nIf(Nat.beq (y &&& (1 <<< 728 - 1)) 0, 1, 0) +
        nIf(Nat.beq ((y >>> 728) &&& (1 <<< 832 - 1)) 0, 1 <<< 24, 0))) := rfl

private theorem card_filter_range_succ (P : Nat → Prop) [DecidablePred P] (n : Nat) :
    ((range (n + 1)).filter P).card = ((range n).filter P).card + if P n then 1 else 0 := by
  rw [range_add_one, filter_insert]
  split_ifs with hP
  · rw [card_insert_of_notMem (by simp)]
  · rfl

private theorem mod_div_mod (a n m k : Nat) (h : m + k ≤ n) :
    a % 2 ^ n / 2 ^ m % 2 ^ k = a / 2 ^ m % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < k
  · have : i + m < n := by omega
    simp [hi, this]
  · simp [hi]

theorem fixRows_spec {RM : Nat} (hRM : RM = 2 ^ 1729 - 1) (Y : Nat) : ∀ nr, fixRows RM Y nr =
    ((range nr).filter fun r => Y / 2 ^ (1729 * r) % 2 ^ 728 = 0).card +
      2 ^ 24 * ((range nr).filter fun r => Y / 2 ^ (1729 * r + 728) % 2 ^ 832 = 0).card
  | 0 => rfl
  | r + 1 => by
    rw [fixRows_succ_raw, strictN_eq]
    beta_reduce
    rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.one_shiftLeft, fixRows_spec hRM Y r,
      card_filter_range_succ, card_filter_range_succ, rowL_eq, hRM,
      Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
      Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, nIf_beq, nIf_beq,
      Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num : 728 ≤ 1729)),
      mod_div_mod _ _ _ _ (by norm_num : 728 + 832 ≤ 1729), Nat.div_div_eq_div_mul, ← pow_add]
    split_ifs <;> ring

private theorem land_21 (x : Nat) : Nat.land x (nat_lit 2097151) = x % 2 ^ 21 :=
  Nat.and_two_pow_sub_one_eq_mod x 21

private theorem land_9 (x : Nat) : Nat.land (Nat.shiftRight x (nat_lit 21)) (nat_lit 511) =
    x / 2 ^ 21 % 512 := by
  show (x >>> 21) &&& (2 ^ 9 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem treeLeaf_raw (XC TD MSF : Nat → Nat) (N M L H CM3 RM GA GB GFC j : Nat) :
    treeLeaf XC TD MSF N M L H CM3 RM GA GB GFC j =
      nIf(bAnd(Nat.beq (TD j % 2 ^ 21 + TD j / 2 ^ 21 % 512) (TD (j + 1) % 2 ^ 21),
        bAnd(Nat.ble (TD j / 2 ^ 21 % 512) 266,
          bAnd(childrenOK (TD j) j (TD j % 2 ^ 21) (TD j / 2 ^ 21 % 512) 0,
            gat M (XC j) (chunk3 XC (TD j % 2 ^ 21)) (TD j) (fun PA CA PB CB =>
                bAnd(Nat.beq (mulC L H CM3 RM PA GA) (spreadM MSF CA),
                  Nat.beq (mulC L H CM3 RM PB GB) (spreadM MSF CB)))
              (TD j / 2 ^ 21 % 512) 0 0 0 0 0 0 0))),
        fixRows RM (mulC L H CM3 RM (leafA M (XC j) 133) GFC) (min (N - 133 * j) 133),
        2 ^ 50) := by
  show strictN (XC j) _ = _
  rw [strictN_eq]; beta_reduce
  rw [strictN_eq]; beta_reduce
  rw [strictN_eq]; beta_reduce
  rw [strictN_eq]; beta_reduce
  rw [letB_eq]; beta_reduce
  rw [strictN_eq]; beta_reduce
  rw [strictN_eq]; beta_reduce
  rw [land_21, land_21, land_9, nIf_ble]
  rfl

theorem treeLeaf_unfold {XC TD MSF : Nat → Nat} {N M L H CM3 RM GA GB GFC j : Nat}
    (h : treeLeaf XC TD MSF N M L H CM3 RM GA GB GFC j < 2 ^ 50) :
    TD j % 2 ^ 21 + TD j / 2 ^ 21 % 512 = TD (j + 1) % 2 ^ 21 ∧
      TD j / 2 ^ 21 % 512 ≤ 266 ∧
      childrenOK (TD j) j (TD j % 2 ^ 21) (TD j / 2 ^ 21 % 512) 0 = true ∧
      gat M (XC j) (chunk3 XC (TD j % 2 ^ 21)) (TD j) (fun PA CA PB CB =>
          bAnd(Nat.beq (mulC L H CM3 RM PA GA) (spreadM MSF CA),
            Nat.beq (mulC L H CM3 RM PB GB) (spreadM MSF CB)))
        (TD j / 2 ^ 21 % 512) 0 0 0 0 0 0 0 = true ∧
      treeLeaf XC TD MSF N M L H CM3 RM GA GB GFC j =
        fixRows RM (mulC L H CM3 RM (leafA M (XC j) 133) GFC) (min (N - 133 * j) 133) := by
  rw [treeLeaf_raw] at h ⊢
  generalize hc : bAnd(Nat.beq (TD j % 2 ^ 21 + TD j / 2 ^ 21 % 512) (TD (j + 1) % 2 ^ 21),
    bAnd(Nat.ble (TD j / 2 ^ 21 % 512) 266,
      bAnd(childrenOK (TD j) j (TD j % 2 ^ 21) (TD j / 2 ^ 21 % 512) 0,
        gat M (XC j) (chunk3 XC (TD j % 2 ^ 21)) (TD j) (fun PA CA PB CB =>
            bAnd(Nat.beq (mulC L H CM3 RM PA GA) (spreadM MSF CA),
              Nat.beq (mulC L H CM3 RM PB GB) (spreadM MSF CB)))
          (TD j / 2 ^ 21 % 512) 0 0 0 0 0 0 0))) = b at h ⊢
  cases b
  · exact absurd h (lt_irrefl _)
  · simp only [bAnd_iff] at hc
    exact ⟨Nat.eq_of_beq_eq_true hc.1, Nat.le_of_ble_eq_true hc.2.1, hc.2.2.1, hc.2.2.2, rfl⟩

end CFSG.KS.HNLocal.GatPf

end
