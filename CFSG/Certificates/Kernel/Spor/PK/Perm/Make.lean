module

public import CFSG.Certificates.Kernel.Spor.PK.Enc
public import Certificates.Data.Kernel.Spor.M11

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS

private noncomputable def clogIter (n k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun _ ih => nIf(Nat.blt (1 <<< ih) n, Nat.succ ih, ih)) k

private theorem clog_eq_iter (n : Nat) : clog n = clogIter n 24 := rfl

private theorem clogIter_zero (n : Nat) : clogIter n 0 = 0 := rfl

private theorem clogIter_succ (n k : Nat) :
    clogIter n (k + 1) = nIf(Nat.blt (1 <<< clogIter n k) n, Nat.succ (clogIter n k), clogIter n k) :=
  rfl

private theorem clogIter_spec (n k : Nat) :
    clogIter n k ≤ k ∧ (n ≤ 2 ^ clogIter n k ∨ clogIter n k = k) := by
  induction k with
  | zero => rw [clogIter_zero]; exact ⟨Nat.le_refl 0, Or.inr rfl⟩
  | succ k ih =>
    obtain ⟨hle, hcase⟩ := ih
    have hshift : (1 <<< clogIter n k) = 2 ^ clogIter n k := by
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [clogIter_succ, hshift, nIf_eq]
    by_cases h : Nat.blt (2 ^ clogIter n k) n = true
    · rw [if_pos h]
      rw [Nat.blt_eq] at h
      rcases hcase with hc | hc
      · omega
      · exact ⟨by omega, Or.inr (by omega)⟩
    · rw [if_neg h]
      rw [Nat.blt_eq] at h
      exact ⟨by omega, Or.inl (Nat.not_lt.mp h)⟩

theorem clog_spec {n : Nat} (hn : n ≤ 2 ^ 24) : n ≤ 2 ^ clog n := by
  rw [clog_eq_iter]
  rcases (clogIter_spec n 24).2 with h | h
  · exact h
  · rw [h]; exact hn

private theorem pmkT_zero' (n w : Nat) (f : Nat → Nat) (lo : Nat) :
    pmkT n w f 0 lo = if lo < n then f lo else 0 := by
  show nIf(Nat.blt lo n, f lo, 0) = _
  simp only [nIf_eq, Nat.blt_eq]

private theorem pmkT_succ' (n w : Nat) (f : Nat → Nat) (d lo : Nat) :
    pmkT n w f (d + 1) lo =
      pmkT n w f d lo ||| (pmkT n w f d (lo + (1 <<< d)) <<< (w * (1 <<< d))) :=
  rfl

private theorem one_shiftLeft' (d : Nat) : (1 <<< d) = 2 ^ d := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]

private theorem enc_one' (w : Nat) (f : Nat → Nat) : enc w f 1 = f 0 := by
  rw [show (1 : Nat) = 0 + 1 from rfl, enc_succ, enc_zero, Nat.mul_zero, Nat.pow_zero,
    Nat.mul_one, Nat.zero_add]

theorem pmkT_eq {n w : Nat} {f : Nat → Nat} (hf : ∀ i < n, f i < 2 ^ w) (d lo : Nat) :
    pmkT n w f d lo = enc w (fun i => if lo + i < n then f (lo + i) else 0) (2 ^ d) := by
  induction d generalizing lo with
  | zero =>
    rw [pmkT_zero', Nat.pow_zero, enc_one']
    simp
  | succ d ih =>
    have hA : enc w (fun i => if lo + i < n then f (lo + i) else 0) (2 ^ d) < 2 ^ (w * 2 ^ d) := by
      apply enc_lt
      intro i _
      show (if lo + i < n then f (lo + i) else 0) < 2 ^ w
      by_cases h : lo + i < n
      · rw [if_pos h]
        exact hf _ h
      · rw [if_neg h]
        exact Nat.two_pow_pos w
    have hB : enc w (fun i => if lo + 2 ^ d + i < n then f (lo + 2 ^ d + i) else 0) (2 ^ d)
        = enc w (fun i => if lo + (2 ^ d + i) < n then f (lo + (2 ^ d + i)) else 0) (2 ^ d) := by
      apply enc_congr
      intro i _
      show (if lo + 2 ^ d + i < n then f (lo + 2 ^ d + i) else 0)
          = (if lo + (2 ^ d + i) < n then f (lo + (2 ^ d + i)) else 0)
      simp only [Nat.add_assoc]
    rw [pmkT_succ', one_shiftLeft', ih lo, ih (lo + 2 ^ d), lor_shiftLeft_eq_add hA,
      Nat.pow_succ, Nat.mul_two, enc_add, hB]

theorem pmk_eq {n w : Nat} {f : Nat → Nat} (hn : n ≤ 2 ^ 24) (hf : ∀ i < n, f i < 2 ^ w) :
    pmk n w f = enc w f n := by
  have hc := clog_spec hn
  have hz : enc w (fun i => if 0 + i < n then f (0 + i) else 0) (2 ^ clog n)
      = enc w (fun i => if 0 + i < n then f (0 + i) else 0) n := by
    apply enc_of_zero hc
    intro i hi _
    have hni : ¬ (0 + i < n) := by omega
    show (if 0 + i < n then f (0 + i) else 0) = 0
    rw [if_neg hni]
  have h1 : pmk n w f = pmkT n w f (clog n) 0 := by
    unfold pmk
    exact strictN_eq _ _
  rw [h1, pmkT_eq hf (clog n) 0, hz]
  apply enc_congr
  intro i hi
  simp [hi]

theorem pidn_eq {n w : Nat} (hn : n ≤ 2 ^ 24) (hw : n ≤ 2 ^ w) :
    pidn n w = enc w (fun i => i) n := by
  unfold pidn
  exact pmk_eq (f := fun i => i) hn (fun i hi => Nat.lt_of_lt_of_le hi hw)

theorem packU_eq {w : Nat} {l : List UInt32} (hl : ∀ x ∈ l, x.toNat < 2 ^ w) :
    CFSG.KS.Mathieu.packU w l = enc w (fun i => (l.getD i 0).toNat) l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx : x.toNat < 2 ^ w := hl x (by simp)
    have ih' := ih (fun y hy => hl y (by simp [hy]))
    have h1 : enc w (fun i => ((x :: l).getD i 0).toNat) 1 = x.toNat := by
      rw [enc_one']
      simp
    have h2 : enc w (fun i => ((x :: l).getD (1 + i) 0).toNat) l.length
        = enc w (fun i => (l.getD i 0).toNat) l.length := by
      apply enc_congr
      intro i _
      show ((x :: l).getD (1 + i) 0).toNat = (l.getD i 0).toNat
      rw [Nat.add_comm 1 i, List.getD_cons_succ]
    show x.toNat ||| (CFSG.KS.Mathieu.packU w l <<< w) = _
    rw [lor_shiftLeft_eq_add hx, ih', List.length_cons, Nat.add_comm l.length 1, enc_add, h1, h2,
      Nat.mul_one]

theorem packL_eq {w : Nat} {l : List Nat} (hl : ∀ x ∈ l, x < 2 ^ w) :
    CFSG.KS.M11.packL w l = enc w (fun i => l.getD i 0) l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx : x < 2 ^ w := hl x (by simp)
    have ih' := ih (fun y hy => hl y (by simp [hy]))
    have h1 : enc w (fun i => (x :: l).getD i 0) 1 = x := by
      rw [enc_one']
      simp
    have h2 : enc w (fun i => (x :: l).getD (1 + i) 0) l.length
        = enc w (fun i => l.getD i 0) l.length := by
      apply enc_congr
      intro i _
      show (x :: l).getD (1 + i) 0 = l.getD i 0
      rw [Nat.add_comm 1 i, List.getD_cons_succ]
    show x ||| (CFSG.KS.M11.packL w l <<< w) = _
    rw [lor_shiftLeft_eq_add hx, ih', List.length_cons, Nat.add_comm l.length 1, enc_add, h1, h2,
      Nat.mul_one]

end CFSG.KS.PK

end
