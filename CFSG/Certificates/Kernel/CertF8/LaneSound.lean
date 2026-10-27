module

public import Certificates.Data.Kernel.CertF8.Lane
public import CFSG.Certificates.Kernel.CertF8.PackSound

public section

namespace CFSG.KC.CertF8

open CFSG.KC.Misc.G2U (pk testBit_pk pk_lt)

@[expose] def blin (P : List (ℕ × ℕ)) (f : ℕ → Bool) (q : ℕ) : Bool :=
  P.foldr (fun p acc => (decide (p.2 = q) && f p.1) ^^ acc) false

theorem blin_congr (P : List (ℕ × ℕ)) {f g : ℕ → Bool} (h : ∀ p ∈ P, f p.1 = g p.1) (q : ℕ) :
    blin P f q = blin P g q := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    simp only [blin, List.foldr_cons] at ih ⊢
    rw [h p (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem M_bit {w N M : ℕ} (hw : 0 < w) (hM : M = pk w (List.replicate N 1)) {t k : ℕ}
    (ht : t < N) (hk : k < w) : M.testBit (w * t + k) = decide (k = 0) := by
  have hr : ∀ x ∈ List.replicate N 1, x < 2 ^ w := by
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    exact one_lt_two_pow' hw
  rw [hM, testBit_pk hr t hk, List.getD_eq_getElem _ _ (by simpa using ht),
    List.getElem_replicate]
  rcases k with _ | k
  · simp
  · simp [Nat.testBit_add_one]

theorem M_bit_hi {w N M : ℕ} (hw : 0 < w) (hM : M = pk w (List.replicate N 1)) {p : ℕ}
    (hp : w * N ≤ p) : M.testBit p = false := by
  have hr : ∀ x ∈ List.replicate N 1, x < 2 ^ w := by
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    exact one_lt_two_pow' hw
  have h := pk_lt hr
  rw [List.length_replicate] at h
  rw [hM]
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hp))

theorem linT_bit {w N M : ℕ} (hw : 0 < w) (hM : M = pk w (List.replicate N 1)) (y b b' : ℕ)
    (hb : b < w) (hb' : b' < w) {t q : ℕ} (ht : t < N) (hq : q < w) :
    (Nat.shiftLeft (Nat.land (Nat.shiftRight y b) M) b').testBit (w * t + q) =
      (decide (b' = q) && y.testBit (w * t + b)) := by
  change ((y >>> b &&& M) <<< b').testBit (w * t + q) = _
  rw [Nat.testBit_shiftLeft]
  by_cases hq' : b' = q
  · subst hq'
    have e : w * t + b' - b' = w * t + 0 := by omega
    rw [e, Nat.testBit_and, Nat.testBit_shiftRight, M_bit hw hM ht (by omega)]
    simp [Nat.add_comm b]
  · rw [decide_eq_false hq', Bool.false_and]
    by_cases hlt : b' < q
    · have e : w * t + q - b' = w * t + (q - b') := by omega
      rw [e, Nat.testBit_and, M_bit hw hM ht (by omega)]
      simp
      omega
    · rcases t with _ | t
      · simp only [Nat.mul_zero, Nat.zero_add]
        rw [decide_eq_false (by omega)]
        simp
      · have e : w * (t + 1) + q - b' = w * t + (w + q - b') := by
          rw [Nat.mul_succ]
          omega
        rw [e, Nat.testBit_and, M_bit hw hM (by omega) (by omega)]
        simp
        omega

theorem lin_bit {w N M : ℕ} (hw : 0 < w) (hM : M = pk w (List.replicate N 1)) (P : List (ℕ × ℕ))
    (hP : ∀ p ∈ P, p.1 < w ∧ p.2 < w) (y : ℕ) {t q : ℕ} (ht : t < N) (hq : q < w) :
    (lin M P y).testBit (w * t + q) = blin P (fun b => y.testBit (w * t + b)) q := by
  induction P with
  | nil => simp [lin, blin]
  | cons p P ih =>
    change (Nat.shiftLeft (Nat.land (Nat.shiftRight y p.1) M) p.2 ^^^ lin M P y).testBit _ = _
    have hp := hP p (List.mem_cons_self ..)
    rw [Nat.testBit_xor, linT_bit hw hM y p.1 p.2 hp.1 hp.2 ht hq,
      ih (fun x hx => hP x (List.mem_cons_of_mem _ hx))]
    rfl

@[expose] def Rep (w N x : ℕ) (E : ℕ → ℕ) : Prop := ∀ t < N, ∀ q < w, x.testBit (w * t + q) = (E t).testBit q

theorem lin_rep {w N M : ℕ} (hw : 0 < w) (hN : 0 < N) (hM : M = pk w (List.replicate N 1))
    (P : List (ℕ × ℕ)) (hP : ∀ p ∈ P, p.1 < w ∧ p.2 < w) {x : ℕ} {E : ℕ → ℕ} (h : Rep w N x E) :
    Rep w N (lin M P x) (fun t => lin M P (E t)) := by
  intro t ht q hq
  have h0 := lin_bit hw hM P hP (E t) hN hq
  simp only [Nat.mul_zero, Nat.zero_add] at h0
  rw [lin_bit hw hM P hP x ht hq, h0]
  exact blin_congr P (fun p hp => h t ht p.1 (hP p hp).1) q

end CFSG.KC.CertF8

end
