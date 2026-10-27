module

public import CFSG.Certificates.Kernel.Spor.PK.Enc
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS

@[expose] def recOf (n w c : Nat) (P Pos T Ti : Nat → Nat) (LV : Nat) : Nat :=
  c + 2 ^ 16 * (enc w P n + 2 ^ (n * w) * (enc w Pos n + 2 ^ (n * w) *
    (enc (n * w) T n + 2 ^ (n * w * n) * (enc (n * w) Ti n + 2 ^ (n * w * n) * LV))))

@[expose] def RecOK (n w c : Nat) (P Pos T Ti : Nat → Nat) : Prop :=
  c < 2 ^ 16 ∧ (∀ k < n, P k < 2 ^ w) ∧ (∀ x < n, Pos x < 2 ^ w) ∧
    (∀ k < n, T k < 2 ^ (n * w)) ∧ (∀ k < n, Ti k < 2 ^ (n * w))

@[expose] def upd (f : Nat → Nat) (i v : Nat) : Nat → Nat := fun j => if j = i then v else f j

private theorem div_peel {A B a o : Nat} (hA : A < 2 ^ a) :
    (A + 2 ^ a * B) / 2 ^ (a + o) = B / 2 ^ o := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos a),
    Nat.div_eq_of_lt hA, Nat.zero_add]

private theorem field_low {A B a o w : Nat} (h : o + w ≤ a) :
    (A + 2 ^ a * B) / 2 ^ o % 2 ^ w = A / 2 ^ o % 2 ^ w := by
  obtain ⟨d, rfl⟩ : ∃ d, a = o + w + d := ⟨a - (o + w), by omega⟩
  have e : 2 ^ (o + w + d) * B = 2 ^ o * (2 ^ w * (2 ^ d * B)) := by
    rw [Nat.pow_add, Nat.pow_add, Nat.mul_assoc, Nat.mul_assoc]
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos o), Nat.add_mul_mod_self_left]

private theorem lcnt_eq (S : Nat) : lcnt S = S % 2 ^ 16 := Nat.and_two_pow_sub_one_eq_mod S 16

private theorem lpt_eq (w S k : Nat) : lpt w (mask w) S k = S / 2 ^ (16 + w * k) % 2 ^ w :=
  fld_eq S (16 + w * k) w

private theorem lpos_eq (w nw S x : Nat) :
    lpos w (mask w) nw S x = S / 2 ^ (16 + (nw + w * x)) % 2 ^ w := by
  rw [← Nat.add_assoc]
  exact fld_eq S (16 + nw + w * x) w

private theorem ltr_eq (nw S k : Nat) :
    ltr nw (mask nw) S k = S / 2 ^ (16 + (nw + (nw + nw * k))) % 2 ^ nw := by
  have e : 16 + (nw + (nw + nw * k)) = 16 + (nw + nw) + nw * k := by omega
  rw [e]
  exact fld_eq S (16 + (nw + nw) + nw * k) nw

private theorem ltri_eq (n nw S k : Nat) :
    ltri n nw (mask nw) S k = S / 2 ^ (16 + (nw + (nw + (nw * n + nw * k)))) % 2 ^ nw := by
  have e : 16 + (nw + (nw + (nw * n + nw * k))) = 16 + (nw + nw) + nw * (n + k) := by
    rw [Nat.mul_add]; omega
  rw [e]
  exact fld_eq S (16 + (nw + nw) + nw * (n + k)) nw

private theorem llv_eq (n nw S : Nat) :
    llv n nw S = S / 2 ^ (16 + (nw + (nw + (nw * n + (nw * n + 0))))) := by
  have e : 16 + (nw + (nw + (nw * n + (nw * n + 0)))) = lvOff n nw := by
    unfold lvOff
    show _ = 16 + (nw + nw) + nw * (n + n)
    rw [Nat.mul_add]
    omega
  rw [e]
  exact Nat.shiftRight_eq_div_pow S (lvOff n nw)

variable {n w c : Nat} {P Pos T Ti : Nat → Nat} {LV : Nat}

private theorem enc_lt' (hP : ∀ k < n, P k < 2 ^ w) : enc w P n < 2 ^ (n * w) := by
  rw [Nat.mul_comm]
  exact enc_lt hP

private theorem mul_add_le_mul {a n k : Nat} (hk : k < n) : a * k + a ≤ a * n := by
  calc a * k + a = a * (k + 1) := by rw [Nat.mul_succ]
    _ ≤ a * n := Nat.mul_le_mul_left _ hk

private theorem le_mul_left_of_lt {n w k : Nat} (hk : k < n) : w * k + w ≤ n * w := by
  rw [Nat.mul_comm n w]
  exact mul_add_le_mul hk

theorem lcnt_recOf (h : RecOK n w c P Pos T Ti) : lcnt (recOf n w c P Pos T Ti LV) = c := by
  rw [lcnt_eq]
  unfold recOf
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.1]

theorem lpt_recOf (h : RecOK n w c P Pos T Ti) {k : Nat} (hk : k < n) :
    lpt w (mask w) (recOf n w c P Pos T Ti LV) k = P k := by
  obtain ⟨hc, hP, hPos, hT, hTi⟩ := h
  rw [lpt_eq]
  unfold recOf
  rw [div_peel hc, field_low (le_mul_left_of_lt hk)]
  exact fd_enc hP hk

theorem lpos_recOf (h : RecOK n w c P Pos T Ti) {x : Nat} (hx : x < n) :
    lpos w (mask w) (n * w) (recOf n w c P Pos T Ti LV) x = Pos x := by
  obtain ⟨hc, hP, hPos, hT, hTi⟩ := h
  rw [lpos_eq]
  unfold recOf
  rw [div_peel hc, div_peel (enc_lt' hP), field_low (le_mul_left_of_lt hx)]
  exact fd_enc hPos hx

theorem ltr_recOf (h : RecOK n w c P Pos T Ti) {k : Nat} (hk : k < n) :
    ltr (n * w) (mask (n * w)) (recOf n w c P Pos T Ti LV) k = T k := by
  obtain ⟨hc, hP, hPos, hT, hTi⟩ := h
  rw [ltr_eq]
  unfold recOf
  rw [div_peel hc, div_peel (enc_lt' hP), div_peel (enc_lt' hPos),
    field_low (mul_add_le_mul (a := n * w) hk)]
  exact fd_enc hT hk

theorem ltri_recOf (h : RecOK n w c P Pos T Ti) {k : Nat} (hk : k < n) :
    ltri n (n * w) (mask (n * w)) (recOf n w c P Pos T Ti LV) k = Ti k := by
  obtain ⟨hc, hP, hPos, hT, hTi⟩ := h
  rw [ltri_eq]
  unfold recOf
  rw [div_peel hc, div_peel (enc_lt' hP), div_peel (enc_lt' hPos),
    div_peel (enc_lt hT), field_low (mul_add_le_mul (a := n * w) hk)]
  exact fd_enc hTi hk

theorem llv_recOf (h : RecOK n w c P Pos T Ti) : llv n (n * w) (recOf n w c P Pos T Ti LV) = LV := by
  obtain ⟨hc, hP, hPos, hT, hTi⟩ := h
  rw [llv_eq]
  unfold recOf
  rw [div_peel hc, div_peel (enc_lt' hP), div_peel (enc_lt' hPos),
    div_peel (enc_lt hT), div_peel (enc_lt hTi), Nat.pow_zero, Nat.div_one]

private theorem enc_mask (w len : Nat) : enc w (fun _ => mask w) len + 1 = 2 ^ (w * len) := by
  induction len with
  | zero => rw [enc_zero, Nat.mul_zero, Nat.pow_zero]
  | succ len ih =>
    have hm : mask w + 1 = 2 ^ w := by
      rw [mask_eq]; exact Nat.sub_add_cancel (Nat.two_pow_pos w)
    have e : 2 ^ (w * (len + 1)) = 2 ^ (w * len) * 2 ^ w := by rw [Nat.mul_succ, Nat.pow_add]
    rw [enc_succ, e, ← hm, ← ih]
    ring

private theorem enc_upd {w : Nat} {f : Nat → Nat} {r v : Nat} :
    ∀ {len : Nat}, r < len →
      enc w (upd f r v) len + f r * 2 ^ (w * r) = enc w f len + v * 2 ^ (w * r)
  | 0, h => absurd h (Nat.not_lt_zero _)
  | len + 1, h => by
    rw [enc_succ, enc_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with hlt | heq
    · have ih := enc_upd (w := w) (f := f) (r := r) (v := v) (len := len) hlt
      have hne : upd f r v len = f len := if_neg (Nat.ne_of_gt hlt)
      rw [hne]
      omega
    · have h1 : enc w (upd f r v) len = enc w f len :=
        enc_congr fun i hi => if_neg (by omega)
      have h2 : upd f r v len = v := if_pos heq.symm
      rw [h1, h2, ← heq]
      omega

private theorem enc_zero_fun (w len : Nat) : enc w (fun _ => 0) len = 0 := by
  induction len with
  | zero => rfl
  | succ len ih => rw [enc_succ, ih, Nat.zero_mul]

private theorem enc_single {w n i v : Nat} (hi : i < n) :
    enc w (fun k => if k = i then v else 0) n = v * 2 ^ (w * i) := by
  have h : enc w (fun k => if k = i then v else 0) n + 0 * 2 ^ (w * i) =
      enc w (fun _ => 0) n + v * 2 ^ (w * i) :=
    enc_upd (w := w) (f := fun _ => 0) (r := i) (v := v) hi
  rw [enc_zero_fun, Nat.zero_mul, Nat.add_zero, Nat.zero_add] at h
  exact h

private theorem mul_pow_lt {x d a b : Nat} (hx : x < 2 ^ d) (hab : a + d ≤ b) :
    x * 2 ^ a < 2 ^ b :=
  calc x * 2 ^ a < 2 ^ d * 2 ^ a := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos a)
    _ = 2 ^ (d + a) := (Nat.pow_add 2 d a).symm
    _ ≤ 2 ^ b := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)

private theorem pow_dvd_mul_pow {z k j : Nat} (h : k ≤ j) : 2 ^ k ∣ z * 2 ^ j :=
  Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 h) z

private theorem lInit_unfold (n w m nw pm idn r LV : Nat) :
    lInit n w m nw pm idn r LV =
      (((1 ||| (r <<< 16)) ||| (pm <<< (16 + nw) - m <<< (16 + nw + w * r))) |||
        (((idn <<< (16 + (nw + nw))) ||| (idn <<< (16 + (nw + nw) + nw * n))) |||
          (LV <<< (16 + (nw + nw) + nw * (n + n))))) := rfl

theorem lInit_eq {r idn : Nat} (hr : r < n) (hw : n < 2 ^ w) (hidn : idn < 2 ^ (n * w)) :
    lInit n w (mask w) (n * w) (mask (n * w)) idn r LV =
      recOf n w 1 (fun k => if k = 0 then r else 0) (fun x => if x = r then 0 else mask w)
        (fun k => if k = 0 then idn else 0) (fun k => if k = 0 then idn else 0) LV := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  have hwle : w ≤ n * w := Nat.le_mul_of_pos_left w hn
  have hnw : n * w ≤ n * w * n := Nat.le_mul_of_pos_right (n * w) hn
  have hrN : r < 2 ^ (n * w) :=
    calc r < n := hr
      _ < 2 ^ w := hw
      _ ≤ 2 ^ (n * w) := Nat.pow_le_pow_right Nat.zero_lt_two hwle
  have hP : enc w (fun k => if k = 0 then r else 0) n = r := by
    rw [enc_single hn, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
  have hT : enc (n * w) (fun k => if k = 0 then idn else 0) n = idn := by
    rw [enc_single hn, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
  have hE : enc w (fun x => if x = r then 0 else mask w) n + mask w * 2 ^ (w * r) =
      mask (n * w) := by
    have h1 : enc w (fun x => if x = r then 0 else mask w) n + mask w * 2 ^ (w * r) =
        enc w (fun _ => mask w) n + 0 * 2 ^ (w * r) :=
      enc_upd (w := w) (f := fun _ => mask w) (r := r) (v := 0) hr
    have h2 := enc_mask w n
    rw [mask_eq (n * w), Nat.mul_comm n w]
    omega
  unfold recOf
  rw [hP, hT, lInit_unfold, Nat.mul_add (n * w) n n]
  generalize enc w (fun x => if x = r then 0 else mask w) n = E at hE ⊢
  have hElt : E < 2 ^ (n * w) := by
    rw [mask_eq (n * w)] at hE
    have := Nat.two_pow_pos (n * w)
    omega
  simp only [Nat.shiftLeft_eq]
  have hA3 : mask (n * w) * 2 ^ (16 + n * w) - mask w * 2 ^ (16 + n * w + w * r) =
      E * 2 ^ (16 + n * w) := by
    rw [← hE]
    have : (E + mask w * 2 ^ (w * r)) * 2 ^ (16 + n * w) =
        E * 2 ^ (16 + n * w) + mask w * 2 ^ (16 + n * w + w * r) := by ring
    rw [this, Nat.add_sub_cancel]
  rw [hA3]
  simp only [Nat.or_assoc]
  have s4 : idn * 2 ^ (16 + (n * w + n * w) + n * w * n) |||
      LV * 2 ^ (16 + (n * w + n * w) + (n * w * n + n * w * n)) =
      idn * 2 ^ (16 + (n * w + n * w) + n * w * n) +
        LV * 2 ^ (16 + (n * w + n * w) + (n * w * n + n * w * n)) :=
    lor_eq_add_of_lt_of_dvd (mul_pow_lt hidn (by omega)) (Nat.dvd_mul_left _ _)
  rw [s4]
  have s3 : idn * 2 ^ (16 + (n * w + n * w)) |||
      (idn * 2 ^ (16 + (n * w + n * w) + n * w * n) +
        LV * 2 ^ (16 + (n * w + n * w) + (n * w * n + n * w * n))) =
      idn * 2 ^ (16 + (n * w + n * w)) +
        (idn * 2 ^ (16 + (n * w + n * w) + n * w * n) +
          LV * 2 ^ (16 + (n * w + n * w) + (n * w * n + n * w * n))) :=
    lor_eq_add_of_lt_of_dvd (mul_pow_lt hidn (by omega))
      (Nat.dvd_add (Nat.dvd_mul_left _ _) (pow_dvd_mul_pow (by omega)))
  rw [s3]
  have s2 : E * 2 ^ (16 + n * w) |||
      (idn * 2 ^ (16 + (n * w + n * w)) +
        (idn * 2 ^ (16 + (n * w + n * w) + n * w * n) +
          LV * 2 ^ (16 + (n * w + n * w) + (n * w * n + n * w * n)))) =
      E * 2 ^ (16 + n * w) +
        (idn * 2 ^ (16 + (n * w + n * w)) +
          (idn * 2 ^ (16 + (n * w + n * w) + n * w * n) +
            LV * 2 ^ (16 + (n * w + n * w) + (n * w * n + n * w * n)))) :=
    lor_eq_add_of_lt_of_dvd (k := 16 + (n * w + n * w)) (mul_pow_lt hElt (by omega))
      (Nat.dvd_add (pow_dvd_mul_pow (by omega)) (Nat.dvd_add (pow_dvd_mul_pow (by omega))
        (pow_dvd_mul_pow (by omega))))
  rw [s2]
  have s1 : r * 2 ^ 16 |||
      (E * 2 ^ (16 + n * w) +
        (idn * 2 ^ (16 + (n * w + n * w)) +
          (idn * 2 ^ (16 + (n * w + n * w) + n * w * n) +
            LV * 2 ^ (16 + (n * w + n * w) + (n * w * n + n * w * n))))) =
      r * 2 ^ 16 +
        (E * 2 ^ (16 + n * w) +
          (idn * 2 ^ (16 + (n * w + n * w)) +
            (idn * 2 ^ (16 + (n * w + n * w) + n * w * n) +
              LV * 2 ^ (16 + (n * w + n * w) + (n * w * n + n * w * n))))) :=
    lor_eq_add_of_lt_of_dvd (k := 16 + n * w) (mul_pow_lt hrN (by omega))
      (Nat.dvd_add (pow_dvd_mul_pow (by omega)) (Nat.dvd_add (pow_dvd_mul_pow (by omega))
        (Nat.dvd_add (pow_dvd_mul_pow (by omega)) (pow_dvd_mul_pow (by omega)))))
  rw [s1]
  rw [lor_eq_add_of_lt_of_dvd (by norm_num : 1 < 2 ^ 16)
    (Nat.dvd_add (Nat.dvd_mul_left _ _) (Nat.dvd_add (pow_dvd_mul_pow (by omega))
      (Nat.dvd_add (pow_dvd_mul_pow (by omega)) (Nat.dvd_add (pow_dvd_mul_pow (by omega))
        (pow_dvd_mul_pow (by omega))))))]
  ring

private theorem lAdd_unfold (n w m nw S q t ti : Nat) :
    lAdd n w m nw S q t ti =
      ((S + 1 + (q <<< (16 + w * lcnt S))) - ((m - lcnt S) <<< (16 + nw + w * q))) +
        ((t <<< (16 + (nw + nw) + nw * lcnt S)) +
          (ti <<< (16 + (nw + nw) + nw * (n + lcnt S)))) := by
  unfold lAdd
  exact strictN_eq _ _

private theorem add_sub_assoc' {A D Y X R : Nat} (h1 : A = Y + D) (h2 : Y + X = R) :
    A - D + X = R := by
  omega

theorem lAdd_eq {q t ti : Nat} (h : RecOK n w c P Pos T Ti) (hc : c < n) (hc16 : c + 1 < 2 ^ 16)
    (hq : q < n) (hw : n < 2 ^ w) (hPc : P c = 0) (hTc : T c = 0) (hTic : Ti c = 0)
    (hPos : Pos q = mask w) (ht : t < 2 ^ (n * w)) (hti : ti < 2 ^ (n * w)) :
    lAdd n w (mask w) (n * w) (recOf n w c P Pos T Ti LV) q t ti =
      recOf n w (c + 1) (upd P c q) (upd Pos q c) (upd T c t) (upd Ti c ti) LV := by
  rw [lAdd_unfold, lcnt_recOf h]
  simp only [Nat.shiftLeft_eq]
  have hm : mask w + 1 = 2 ^ w := by
    rw [mask_eq]; exact Nat.sub_add_cancel (Nat.two_pow_pos w)
  have hcm : c ≤ mask w := by omega
  have e1 : enc w (upd P c q) n = enc w P n + q * 2 ^ (w * c) := by
    have h1 : enc w (upd P c q) n + P c * 2 ^ (w * c) = enc w P n + q * 2 ^ (w * c) :=
      enc_upd (w := w) (f := P) (r := c) (v := q) hc
    rw [hPc, Nat.zero_mul, Nat.add_zero] at h1
    exact h1
  have e2 : enc w Pos n = enc w (upd Pos q c) n + (mask w - c) * 2 ^ (w * q) := by
    have h1 : enc w (upd Pos q c) n + Pos q * 2 ^ (w * q) = enc w Pos n + c * 2 ^ (w * q) :=
      enc_upd (w := w) (f := Pos) (r := q) (v := c) hq
    rw [hPos] at h1
    obtain ⟨k, hk⟩ : ∃ k, mask w = c + k := ⟨mask w - c, by omega⟩
    rw [hk, Nat.add_sub_cancel_left]
    rw [hk, Nat.add_mul] at h1
    omega
  have e3 : enc (n * w) (upd T c t) n = enc (n * w) T n + t * 2 ^ (n * w * c) := by
    have h1 : enc (n * w) (upd T c t) n + T c * 2 ^ (n * w * c) =
        enc (n * w) T n + t * 2 ^ (n * w * c) :=
      enc_upd (w := n * w) (f := T) (r := c) (v := t) hc
    rw [hTc, Nat.zero_mul, Nat.add_zero] at h1
    exact h1
  have e4 : enc (n * w) (upd Ti c ti) n = enc (n * w) Ti n + ti * 2 ^ (n * w * c) := by
    have h1 : enc (n * w) (upd Ti c ti) n + Ti c * 2 ^ (n * w * c) =
        enc (n * w) Ti n + ti * 2 ^ (n * w * c) :=
      enc_upd (w := n * w) (f := Ti) (r := c) (v := ti) hc
    rw [hTic, Nat.zero_mul, Nat.add_zero] at h1
    exact h1
  unfold recOf
  rw [e1, e3, e4, e2]
  generalize enc w P n = EP
  generalize enc w (upd Pos q c) n = E'
  generalize enc (n * w) T n = ET
  generalize enc (n * w) Ti n = ETi
  refine add_sub_assoc' (Y := c + 1 + 2 ^ 16 * ((EP + q * 2 ^ (w * c)) + 2 ^ (n * w) *
    (E' + 2 ^ (n * w) * (ET + 2 ^ (n * w * n) * (ETi + 2 ^ (n * w * n) * LV))))) ?_ ?_
  · ring
  · ring

end CFSG.KS.PK

end
