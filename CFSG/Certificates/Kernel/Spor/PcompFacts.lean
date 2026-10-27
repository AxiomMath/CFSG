module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.LocalQT.PermW
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.PF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

theorem shl_eq (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem shr_eq (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b

theorem mask_eq (w : Nat) : mask w = 2 ^ w - 1 := by
  unfold mask
  rw [shl_eq, Nat.one_mul]
  rfl

theorem testBit_pgM (w p j k : Nat) :
    (pg w (mask w) p j).testBit k = (decide (k < w) && p.testBit (w * j + k)) := by
  have e : pg w (mask w) p j = (p >>> (w * j)) &&& (2 ^ w - 1) := by rw [← mask_eq]; rfl
  rw [e, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem pg_lt (w p j : Nat) : pg w (mask w) p j < 2 ^ w := by
  have e : pg w (mask w) p j = (p >>> (w * j)) &&& (2 ^ w - 1) := by rw [← mask_eq]; rfl
  rw [e]
  exact Nat.and_lt_two_pow _ (by have := Nat.one_le_two_pow (n := w); omega)

def Fld (w X : Nat) (g : Nat → Nat) : Prop :=
  ∀ i k, k < w → X.testBit (w * i + k) = (g i).testBit k

theorem fld_congr {w X : Nat} {g g' : Nat → Nat} (h : Fld w X g) (e : ∀ i, g i = g' i) :
    Fld w X g' := fun i k hk => by rw [h i k hk, e]

theorem fld_or {w A B : Nat} {g h : Nat → Nat} (hA : Fld w A g) (hB : Fld w B h) :
    Fld w (A ||| B) (fun i => g i ||| h i) := by
  intro i k hk
  rw [Nat.testBit_or, hA i k hk, hB i k hk, Nat.testBit_or]

theorem fld_zero (w : Nat) : Fld w 0 (fun _ => 0) := by
  intro i k _
  simp

theorem fld_one {w v : Nat} (hv : v < 2 ^ w) : Fld w v (fun i => if i = 0 then v else 0) := by
  intro i k hk
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have h1 : w ≤ w * i + k := Nat.le_trans (Nat.le_mul_of_pos_right w hi) (Nat.le_add_right _ _)
    have hi0 : i ≠ 0 := by omega
    simp only [hi0, ↓reduceIte, Nat.zero_testBit]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) h1))

theorem fld_shl {w B : Nat} {h : Nat → Nat} (s : Nat) (hB : Fld w B h) :
    Fld w (B <<< (w * s)) (fun i => if s ≤ i then h (i - s) else 0) := by
  intro i k hk
  rw [Nat.testBit_shiftLeft]
  by_cases hs : s ≤ i
  · have m1 := Nat.mul_le_mul_left w hs
    have e2 : w * i + k - w * s = w * (i - s) + k := by
      rw [Nat.mul_sub]
      omega
    have e1 : w * s ≤ w * i + k := by omega
    simp only [hs, ↓reduceIte, e2, hB _ _ hk, ge_iff_le, e1, decide_true, Bool.true_and]
  · have m1 := Nat.mul_le_mul_left w (by omega : i + 1 ≤ s)
    rw [Nat.mul_add, Nat.mul_one] at m1
    have e1 : ¬ w * s ≤ w * i + k := by omega
    simp only [hs, ↓reduceIte, ge_iff_le, e1, decide_false, Bool.false_and, Nat.zero_testBit]

theorem pg_of_fld {w X i : Nat} {g : Nat → Nat} (hX : Fld w X g) (hg : g i < 2 ^ w) :
    pg w (mask w) X i = g i := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_pgM]
  by_cases hk : k < w
  · simp [hk, hX i k hk]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hg (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hk]

theorem eq_of_fld {w X Y : Nat} {g : Nat → Nat} (hw : 0 < w) (hX : Fld w X g) (hY : Fld w Y g) :
    X = Y := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hd := Nat.div_add_mod j w
  have hk : j % w < w := Nat.mod_lt j hw
  rw [← hd, hX _ _ hk, hY _ _ hk]

theorem fld_double {w A B x y c : Nat} {F : Nat → Nat}
    (hA : Fld w A (fun i => if i < c then F (x + i) else 0))
    (hB : Fld w B (fun i => if i < c then F (y + i) else 0)) (hy : y = x + c) :
    Fld w (A ||| B <<< (w * c)) (fun i => if i < c + c then F (x + i) else 0) := by
  subst hy
  refine fld_congr (fld_or hA (fld_shl c hB)) ?_
  intro i
  by_cases h1 : i < c
  · have h2 : ¬ c ≤ i := by omega
    have h3 : i < c + c := by omega
    simp only [h1, h2, h3, ↓reduceIte, Nat.or_zero]
  · have e : x + c + (i - c) = x + i := by omega
    have h2 : c ≤ i := by omega
    by_cases h3 : i < c + c
    · have h4 : i - c < c := by omega
      simp only [h1, h2, h3, h4, e, ↓reduceIte, Nat.zero_or]
    · have h4 : ¬ i - c < c := by omega
      simp only [h1, h2, h3, h4, ↓reduceIte, Nat.zero_or]

theorem fld_single {w x : Nat} {F : Nat → Nat} (hF : F x < 2 ^ w) :
    Fld w (F x) (fun i => if i < 1 then F (x + i) else 0) := by
  refine fld_congr (fld_one hF) ?_
  intro i
  by_cases h : i = 0
  · subst h
    simp
  · have h1 : ¬ i < 1 := by omega
    simp only [h, h1, ↓reduceIte]

theorem fld_pair {w x y : Nat} {F : Nat → Nat} (hF : ∀ z, F z < 2 ^ w) (hy : y = x + 1) :
    Fld w (Nat.lor (F x) (Nat.shiftLeft (F y) w)) (fun i => if i < 2 then F (x + i) else 0) := by
  have h := fld_double (F := F) (x := x) (y := y) (c := 1) (fld_single (x := x) (hF x))
    (fld_single (x := y) (hF y)) hy
  rw [Nat.mul_one] at h
  exact h

theorem fld_pmkH (w p q : Nat) : ∀ d lo, Fld w (pmkH w (mask w) p q d lo)
    (fun i => if i < 2 ^ d then pg w (mask w) p (pg w (mask w) q (lo + i)) else 0)
  | 0, lo => fld_single (F := fun x => pg w (mask w) p (pg w (mask w) q x)) (pg_lt _ _ _)
  | d + 1, lo => by
    have e : pmkH w (mask w) p q (d + 1) lo = Nat.lor (pmkH w (mask w) p q d lo)
        (Nat.shiftLeft (pmkH w (mask w) p q d (Nat.add lo (Nat.shiftLeft (nat_lit 1) d)))
          (Nat.mul w (Nat.shiftLeft (nat_lit 1) d))) := rfl
    rw [e, shl_eq 1 d, Nat.one_mul]
    refine fld_congr (fld_double (F := fun x => pg w (mask w) p (pg w (mask w) q x))
      (x := lo) (y := Nat.add lo (2 ^ d)) (c := 2 ^ d)
      (fld_pmkH w p q d lo) (fld_pmkH w p q d _) rfl) ?_
    intro i
    rw [Nat.pow_succ, Nat.mul_two]

theorem fld_pmkH8 (w p q : Nat) : ∀ d lo, Fld w (pmkH8 w (mask w) p q d lo)
    (fun i => if i < 8 * 2 ^ d then pg w (mask w) p (pg w (mask w) q (lo + i)) else 0)
  | 0, lo => by
    have hF : ∀ z, (fun x => pg w (mask w) p (pg w (mask w) q x)) z < 2 ^ w :=
      fun _ => pg_lt _ _ _
    have h4 : ∀ x, Fld w (Nat.lor (Nat.lor (pg w (mask w) p (pg w (mask w) q x))
        (Nat.shiftLeft (pg w (mask w) p (pg w (mask w) q (x + 1))) w))
        (Nat.shiftLeft (Nat.lor (pg w (mask w) p (pg w (mask w) q (x + 2)))
          (Nat.shiftLeft (pg w (mask w) p (pg w (mask w) q (x + 2 + 1))) w)) (Nat.mul w 2)))
        (fun i => if i < 4 then pg w (mask w) p (pg w (mask w) q (x + i)) else 0) := fun x =>
      fld_double (F := fun x => pg w (mask w) p (pg w (mask w) q x)) (x := x) (y := x + 2)
        (c := 2) (fld_pair hF rfl) (fld_pair hF rfl) rfl
    have e : pmkH8 w (mask w) p q 0 lo = Nat.lor
        (Nat.lor (Nat.lor (pg w (mask w) p (pg w (mask w) q lo))
          (Nat.shiftLeft (pg w (mask w) p (pg w (mask w) q (lo + 1))) w))
          (Nat.shiftLeft (Nat.lor (pg w (mask w) p (pg w (mask w) q (lo + 2)))
            (Nat.shiftLeft (pg w (mask w) p (pg w (mask w) q (lo + 2 + 1))) w)) (Nat.mul w 2)))
        (Nat.shiftLeft (Nat.lor (Nat.lor (pg w (mask w) p (pg w (mask w) q (lo + 4)))
          (Nat.shiftLeft (pg w (mask w) p (pg w (mask w) q (lo + 4 + 1))) w))
          (Nat.shiftLeft (Nat.lor (pg w (mask w) p (pg w (mask w) q (lo + 4 + 2)))
            (Nat.shiftLeft (pg w (mask w) p (pg w (mask w) q (lo + 4 + 2 + 1))) w)) (Nat.mul w 2)))
          (Nat.mul w 4)) := rfl
    rw [e]
    exact fld_double (F := fun x => pg w (mask w) p (pg w (mask w) q x)) (x := lo) (y := lo + 4)
      (c := 4) (h4 lo) (h4 (lo + 4)) rfl
  | d + 1, lo => by
    have e : pmkH8 w (mask w) p q (d + 1) lo = Nat.lor (pmkH8 w (mask w) p q d lo)
        (Nat.shiftLeft (pmkH8 w (mask w) p q d (Nat.add lo (Nat.shiftLeft (nat_lit 8) d)))
          (Nat.mul w (Nat.shiftLeft (nat_lit 8) d))) := rfl
    rw [e, shl_eq 8 d]
    refine fld_congr (fld_double (F := fun x => pg w (mask w) p (pg w (mask w) q x))
      (x := lo) (y := Nat.add lo (8 * 2 ^ d)) (c := 8 * 2 ^ d)
      (fld_pmkH8 w p q d lo) (fld_pmkH8 w p q d _) rfl) ?_
    intro i
    rw [Nat.pow_succ]
    congr 1
    apply propext
    constructor <;> intro h <;> omega

theorem strictN_eqP (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eqP (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem iteT {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by
  simp [h]

theorem iteF {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by
  simp [h]

theorem false_of_beq {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e
  subst e
  rw [Nat.beq_refl] at h
  exact Bool.noConfusion h

@[expose] noncomputable def pcR (n w m p q : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih b rem => nIf(Nat.beq rem (nat_lit 0), nat_lit 0,
      nIf(Nat.beq (Nat.land rem (nat_lit 1)) (nat_lit 0), ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)),
        strictN (Nat.sub n (Nat.shiftLeft rem b)) (fun lo =>
          Nat.lor (Nat.shiftLeft (nIf(Nat.blt b (nat_lit 3), pmkH w m p q b lo, pmkH8 w m p q (Nat.sub b (nat_lit 3)) lo))
              (Nat.mul w lo))
            (ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)))))))

theorem pcomp_eq_pcR (n w m p q : Nat) : pcomp n w m p q = pcR n w m p q 32 0 n := rfl

theorem pcR_succ (n w m p q k b rem : Nat) : pcR n w m p q (k + 1) b rem =
    nIf(Nat.beq rem (nat_lit 0), nat_lit 0,
      nIf(Nat.beq (Nat.land rem (nat_lit 1)) (nat_lit 0), pcR n w m p q k (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)),
        strictN (Nat.sub n (Nat.shiftLeft rem b)) (fun lo =>
          Nat.lor (Nat.shiftLeft (nIf(Nat.blt b (nat_lit 3), pmkH w m p q b lo, pmkH8 w m p q (Nat.sub b (nat_lit 3)) lo))
              (Nat.mul w lo))
            (pcR n w m p q k (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)))))) := rfl

theorem fld_blk (w p q b lo : Nat) :
    Fld w (nIf(Nat.blt b (nat_lit 3), pmkH w (mask w) p q b lo, pmkH8 w (mask w) p q (Nat.sub b (nat_lit 3)) lo))
      (fun i => if i < 2 ^ b then pg w (mask w) p (pg w (mask w) q (lo + i)) else 0) := by
  cases h : Nat.blt b 3
  · have hb : 3 ≤ b := by
      have h' : ¬ (Nat.blt b 3 = true) := by rw [h]; exact Bool.false_ne_true
      rw [Nat.blt_eq] at h'
      omega
    have e8 : (8 : Nat) = 2 ^ 3 := rfl
    have e : 8 * 2 ^ (b - 3) = 2 ^ b := by
      rw [e8, ← Nat.pow_add]
      congr 1
      omega
    have h8 := fld_pmkH8 w p q (b - 3) lo
    rw [e] at h8
    exact h8
  · exact fld_pmkH w p q b lo

theorem mod_two_pow_mono (n a k : Nat) : n % 2 ^ a ≤ n % 2 ^ (a + k) := by
  have h := Nat.mod_mod_of_dvd n (Nat.pow_dvd_pow 2 (Nat.le_add_right a k))
  rw [← h]
  exact Nat.mod_le _ _

theorem fld_pcR (n w p q : Nat) : ∀ k b rem, rem = n / 2 ^ b →
    Fld w (pcR n w (mask w) p q k b rem) (fun i => if n % 2 ^ b ≤ i ∧ i < n % 2 ^ (b + k) then
      pg w (mask w) p (pg w (mask w) q i) else 0)
  | 0, b, rem, _ => by
    refine fld_congr (fld_zero w) ?_
    intro i
    have h : ¬ (n % 2 ^ b ≤ i ∧ i < n % 2 ^ (b + 0)) := by
      rw [Nat.add_zero]
      omega
    simp only [h, ↓reduceIte]
  | k + 1, b, rem, hr => by
    rw [pcR_succ]
    have hs : Nat.shiftRight rem (nat_lit 1) = n / 2 ^ (b + 1) := by
      rw [shr_eq, hr, Nat.div_div_eq_div_mul, Nat.pow_one, ← Nat.pow_succ]
    have ih := fld_pcR n w p q k (b + 1) _ hs
    have ek : b + 1 + k = b + (k + 1) := by omega
    rw [ek] at ih
    have hms := Nat.mod_pow_succ (x := n) (b := 2) (k := b)
    have hmono := mod_two_pow_mono n (b + 1) k
    rw [ek] at hmono
    cases h0 : Nat.beq rem (nat_lit 0)
    · cases h1 : Nat.beq (Nat.land rem (nat_lit 1)) (nat_lit 0)
      · rw [strictN_eqP]
        have hodd : n / 2 ^ b % 2 = 1 := by
          have h1' : rem &&& 1 ≠ 0 := false_of_beq h1
          rw [Nat.and_one_is_mod] at h1'
          rw [← hr]
          omega
        have hlo : Nat.sub n (Nat.shiftLeft rem b) = n % 2 ^ b := by
          rw [shl_eq, hr, Nat.mod_eq_sub_mul_div, Nat.mul_comm]
          rfl
        rw [hlo]
        have hb := fld_or (fld_shl (n % 2 ^ b) (fld_blk w p q b (n % 2 ^ b))) ih
        refine fld_congr hb ?_
        intro i
        rw [hodd, Nat.mul_one] at hms
        rw [hms] at hmono
        rw [hms]
        by_cases c1 : n % 2 ^ b ≤ i
        · have e : n % 2 ^ b + (i - n % 2 ^ b) = i := by omega
          by_cases c2 : i - n % 2 ^ b < 2 ^ b
          · have c3 : ¬ (n % 2 ^ b + 2 ^ b ≤ i ∧ i < n % 2 ^ (b + (k + 1))) := by omega
            have c4 : n % 2 ^ b ≤ i ∧ i < n % 2 ^ (b + (k + 1)) := by omega
            rw [iteT c1, iteT c2, iteF c3, iteT c4, e, Nat.or_zero]
          · by_cases c3 : n % 2 ^ b + 2 ^ b ≤ i ∧ i < n % 2 ^ (b + (k + 1))
            · have c4 : n % 2 ^ b ≤ i ∧ i < n % 2 ^ (b + (k + 1)) := by omega
              rw [iteT c1, iteF c2, iteT c3, iteT c4, Nat.zero_or]
            · have c4 : ¬ (n % 2 ^ b ≤ i ∧ i < n % 2 ^ (b + (k + 1))) := by omega
              rw [iteT c1, iteF c2, iteF c3, iteF c4, Nat.zero_or]
        · have c3 : ¬ (n % 2 ^ b + 2 ^ b ≤ i ∧ i < n % 2 ^ (b + (k + 1))) := by omega
          have c4 : ¬ (n % 2 ^ b ≤ i ∧ i < n % 2 ^ (b + (k + 1))) := by omega
          rw [iteF c1, iteF c3, iteF c4, Nat.zero_or]
      · have heven : n / 2 ^ b % 2 = 0 := by
          have h1' : rem &&& 1 = 0 := Nat.eq_of_beq_eq_true h1
          rw [Nat.and_one_is_mod] at h1'
          rw [← hr]
          exact h1'
        have hms' : n % 2 ^ (b + 1) = n % 2 ^ b := by
          rw [hms, heven]
          rfl
        refine fld_congr ih ?_
        intro i
        rw [hms']
    · have hr0 : rem = 0 := by simpa using h0
      have hlt : n < 2 ^ b := by
        rw [hr0] at hr
        rcases Nat.div_eq_zero_iff.1 hr.symm with h | h
        · exact absurd h (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos b))
        · exact h
      have e1 : n % 2 ^ b = n := Nat.mod_eq_of_lt hlt
      have e2 : n % 2 ^ (b + (k + 1)) = n :=
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))
      refine fld_congr (fld_zero w) ?_
      intro i
      have h : ¬ (n % 2 ^ b ≤ i ∧ i < n % 2 ^ (b + (k + 1))) := by
        rw [e1, e2]
        omega
      simp only [h, ↓reduceIte]

theorem fld_pcomp {n w : Nat} (p q : Nat) (hn : n < 2 ^ 32) :
    Fld w (pcomp n w (mask w) p q)
      (fun i => if i < n then pg w (mask w) p (pg w (mask w) q i) else 0) := by
  have h := fld_pcR n w p q 32 0 n (by simp)
  rw [pcomp_eq_pcR]
  refine fld_congr h ?_
  intro i
  have e : n % 2 ^ (0 + 32) = n := Nat.mod_eq_of_lt (by simpa using hn)
  rw [e]
  simp only [Nat.pow_zero, Nat.mod_one, Nat.zero_le, true_and]

theorem pg_pcomp {n w p q i : Nat} (hn : n < 2 ^ 32) (hi : i < n) :
    pg w (mask w) (pcomp n w (mask w) p q) i = pg w (mask w) p (pg w (mask w) q i) := by
  have h := pg_of_fld (i := i) (fld_pcomp (w := w) p q hn) (by simp only [hi, ↓reduceIte]; exact pg_lt _ _ _)
  simp only [hi, ↓reduceIte] at h
  exact h

theorem shr_zero_of_fld {n w X : Nat} {g : Nat → Nat} (hw : 0 < w) (hX : Fld w X g)
    (hg : ∀ i, n ≤ i → g i = 0) : X >>> (n * w) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight, Nat.zero_testBit]
  have hd := Nat.div_add_mod (n * w + j) w
  have hk : (n * w + j) % w < w := Nat.mod_lt _ hw
  have hi : n ≤ (n * w + j) / w := by
    rw [Nat.le_div_iff_mul_le hw]
    omega
  rw [← hd, hX _ _ hk, hg _ hi, Nat.zero_testBit]

theorem pcomp_shr {n w : Nat} (p q : Nat) (hn : n < 2 ^ 32) (hw : 0 < w) :
    pcomp n w (mask w) p q >>> (n * w) = 0 :=
  shr_zero_of_fld hw (fld_pcomp p q hn) (fun i hi => by
    have : ¬ i < n := by omega
    simp [this])

theorem eq_of_fields {n w p q : Nat} (hw : 0 < w) (hp : p >>> (n * w) = 0)
    (hq : q >>> (n * w) = 0) (h : ∀ i < n, pg w (mask w) p i = pg w (mask w) q i) : p = q := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n * w
  · have hd := Nat.div_add_mod j w
    have hi : j / w < n := (Nat.div_lt_iff_lt_mul hw).2 hj
    have hk : j % w < w := Nat.mod_lt j hw
    have tp := testBit_pgM w p (j / w) (j % w)
    have tq := testBit_pgM w q (j / w) (j % w)
    rw [hd] at tp tq
    rw [h _ hi] at tp
    simp only [hk, decide_true, Bool.true_and] at tp tq
    rw [← tp, tq]
  · have e : j = n * w + (j - n * w) := by omega
    rw [e, ← Nat.testBit_shiftRight, ← Nat.testBit_shiftRight, hp, hq]

theorem w_pos {n w : Nat} (hw : n + 1 < 2 ^ w) : 0 < w := by
  rcases Nat.eq_zero_or_pos w with h0 | h0
  · subst h0
    simp at hw
  · exact h0

theorem canon_facts {n w m nw p : Nat} (hp : canonK n w m nw p = true) :
    n < 16777216 ∧ n + 1 < 2 ^ w ∧ p >>> nw = 0 ∧ ∀ i < n, pg w m p i < n := by
  unfold canonK szOK at hp
  simp only [bAnd_iff] at hp
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  refine ⟨by simpa [Nat.blt_eq] using h1, ?_, by simpa using h3, fun i hi => ?_⟩
  · simpa [Nat.blt_eq, Nat.shiftLeft_eq] using h2
  · simpa [Nat.blt_eq] using allN_spec h4 i hi

theorem fld_pmkT (n w : Nat) (f : Nat → Nat) (hf : ∀ x < n, f x < 2 ^ w) : ∀ d lo,
    Fld w (pmkT n w f d lo)
      (fun i => if i < 2 ^ d then (if lo + i < n then f (lo + i) else 0) else 0)
  | 0, lo => by
    have hG : ∀ z, (fun x => if x < n then f x else 0) z < 2 ^ w := by
      intro z
      by_cases hz : z < n
      · simp only [hz, ↓reduceIte]
        exact hf z hz
      · simp only [hz, ↓reduceIte]
        exact Nat.two_pow_pos w
    have e : pmkT n w f 0 lo = (fun x => if x < n then f x else 0) lo := by
      change Bool.rec (motive := fun _ => Nat) (nat_lit 0) (f lo) (Nat.blt lo n) = _
      cases h : Nat.blt lo n
      · have hl : ¬ lo < n := fun hh => by
          have := Nat.blt_eq.mpr hh
          rw [h] at this
          exact Bool.false_ne_true this
        exact (iteF hl).symm
      · exact (iteT (Nat.blt_eq.mp h)).symm
    rw [e]
    exact fld_single (F := fun x => if x < n then f x else 0) (hG lo)
  | d + 1, lo => by
    have e : pmkT n w f (d + 1) lo = Nat.lor (pmkT n w f d lo)
        (Nat.shiftLeft (pmkT n w f d (Nat.add lo (Nat.shiftLeft (nat_lit 1) d)))
          (Nat.mul w (Nat.shiftLeft (nat_lit 1) d))) := rfl
    rw [e, shl_eq 1 d, Nat.one_mul]
    refine fld_congr (fld_double (F := fun x => if x < n then f x else 0)
      (x := lo) (y := Nat.add lo (2 ^ d)) (c := 2 ^ d)
      (fld_pmkT n w f hf d lo) (fld_pmkT n w f hf d _) rfl) ?_
    intro i
    rw [Nat.pow_succ, Nat.mul_two]

@[expose] noncomputable def clogR (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun _ ih => nIf(Nat.blt (Nat.shiftLeft (nat_lit 1) ih) n, Nat.succ ih, ih))

theorem clogR_spec (n : Nat) : ∀ k, clogR n k = k ∨ n ≤ 2 ^ clogR n k
  | 0 => Or.inl rfl
  | k + 1 => by
    have e : clogR n (k + 1) =
        nIf(Nat.blt (Nat.shiftLeft (nat_lit 1) (clogR n k)) n, Nat.succ (clogR n k), clogR n k) :=
      rfl
    have ih := clogR_spec n k
    rw [e]
    generalize clogR n k = c at ih ⊢
    cases h : Nat.blt (Nat.shiftLeft 1 c) n
    · right
      have hl : ¬ Nat.shiftLeft 1 c < n := fun hh => by
        have := Nat.blt_eq.mpr hh
        rw [h] at this
        exact Bool.false_ne_true this
      rw [shl_eq, Nat.one_mul] at hl
      exact Nat.le_of_not_lt hl
    · have hl := Nat.blt_eq.mp h
      rw [shl_eq, Nat.one_mul] at hl
      rcases ih with ih | ih
      · left
        exact congrArg Nat.succ ih
      · omega

theorem clog_spec {n : Nat} (hn : n < 16777216) : n ≤ 2 ^ clog n := by
  have e : clog n = clogR n 24 := rfl
  rw [e]
  rcases clogR_spec n 24 with h | h
  · rw [h]
    have : (2 : Nat) ^ 24 = 16777216 := rfl
    omega
  · exact h

theorem fld_pidn {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    Fld w (pidn n w) (fun i => if i < n then i else 0) := by
  have hc := clog_spec hn
  have h := fld_pmkT n w (fun i => i) (fun x hx => by omega) (clog n) 0
  have e : pidn n w = pmkT n w (fun i => i) (clog n) 0 := by
    unfold pidn pmk
    rw [strictN_eqP]
  rw [e]
  refine fld_congr h ?_
  intro i
  by_cases hi : i < n
  · have h2 : i < 2 ^ clog n := by omega
    simp [hi, h2]
  · simp [hi]

theorem pg_pidn {n w i : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (hi : i < n) :
    pg w (mask w) (pidn n w) i = i := by
  rw [pg_of_fld (fld_pidn hn hw) (by simp only [hi, ↓reduceIte]; omega)]
  simp [hi]

theorem pidn_shr {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    pidn n w >>> (n * w) = 0 :=
  shr_zero_of_fld (w_pos hw) (fld_pidn hn hw) (fun i hi => by
    have : ¬ i < n := by omega
    simp [this])

theorem imgW_eq (w s i : Nat) : CFSG.KC.LQT.PW.imgW w s i = pg w (mask w) s i := rfl

theorem fld_ofFnW (w : Nat) (g : Nat → Nat) (hg : ∀ i, g i < 2 ^ w) : ∀ n,
    Fld w (CFSG.KC.LQT.PW.ofFnW n w g) (fun i => if i < n then g i else 0)
  | 0 => fld_congr (fld_zero w) (fun i => by simp)
  | n + 1 => by
    have e : CFSG.KC.LQT.PW.ofFnW (n + 1) w g =
        Nat.lor (CFSG.KC.LQT.PW.ofFnW n w g) (Nat.shiftLeft (g n) (Nat.mul w n)) := rfl
    rw [e]
    refine fld_congr (fld_or (fld_ofFnW w g hg n) (fld_shl n (fld_one (hg n)))) ?_
    intro i
    by_cases h1 : i < n
    · have h2 : ¬ n ≤ i := by omega
      have h3 : i < n + 1 := by omega
      simp only [h1, h2, h3, ↓reduceIte, Nat.or_zero]
    · by_cases h3 : i = n
      · subst h3
        simp
      · have h4 : ¬ i < n + 1 := by omega
        have h5 : n ≤ i := by omega
        have h6 : ¬ i - n = 0 := by omega
        simp only [h1, h4, h5, h6, ↓reduceIte, Nat.or_zero]

theorem mulW_eq_pcomp {n w : Nat} (s t : Nat) (hn : n < 2 ^ 32) (hw : 0 < w) :
    CFSG.KC.LQT.PW.mulW n w s t = pcomp n w (mask w) s t :=
  eq_of_fld hw (fld_ofFnW w _ (fun _ => pg_lt _ _ _) n) (fld_pcomp s t hn)

end CFSG.KS.PF

end
