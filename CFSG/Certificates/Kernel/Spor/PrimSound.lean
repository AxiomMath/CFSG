
module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Data.CFSGNative.Schreier.SetOrbit
public import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KS.Prim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Co3.Native
open CFSG.KS.Mathieu (icode)

private theorem shl_eq(a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

private theorem shr_eq(a b : Nat) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b

private theorem mask_eq(w : Nat) : mask w = 2 ^ w - 1 := by
  unfold mask
  rw [shl_eq, Nat.one_mul]
  rfl

private theorem testBit_pgM(w p j k : Nat) :
    (pg w (mask w) p j).testBit k = (decide (k < w) && p.testBit (w * j + k)) := by
  have e : pg w (mask w) p j = (p >>> (w * j)) &&& (2 ^ w - 1) := by rw [← mask_eq]; rfl
  rw [e, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

private theorem pg_lt(w p j : Nat) : pg w (mask w) p j < 2 ^ w := by
  have e : pg w (mask w) p j = (p >>> (w * j)) &&& (2 ^ w - 1) := by rw [← mask_eq]; rfl
  rw [e]
  exact Nat.and_lt_two_pow _ (by have := Nat.one_le_two_pow (n := w); omega)

private def Fld(w X : Nat) (g : Nat → Nat) : Prop :=
  ∀ i k, k < w → X.testBit (w * i + k) = (g i).testBit k

private theorem fld_congr {w X : Nat} {g g' : Nat → Nat} (h : Fld w X g) (e : ∀ i, g i = g' i) :
    Fld w X g' := fun i k hk => by rw [h i k hk, e]

private theorem fld_or {w A B : Nat} {g h : Nat → Nat} (hA : Fld w A g) (hB : Fld w B h) :
    Fld w (A ||| B) (fun i => g i ||| h i) := by
  intro i k hk
  rw [Nat.testBit_or, hA i k hk, hB i k hk, Nat.testBit_or]

private theorem fld_zero (w : Nat) : Fld w 0 (fun _ => 0) := by
  intro i k _
  simp

private theorem fld_one {w v : Nat} (hv : v < 2 ^ w) : Fld w v (fun i => if i = 0 then v else 0) := by
  intro i k hk
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have h1 : w ≤ w * i + k := le_trans (Nat.le_mul_of_pos_right w hi) (Nat.le_add_right _ _)
    have hi0 : i ≠ 0 := by omega
    simp only [hi0, ↓reduceIte, Nat.zero_testBit]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) h1))

private theorem fld_shl {w B : Nat} {h : Nat → Nat} (s : Nat) (hB : Fld w B h) :
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

private theorem pg_of_fld{w X i : Nat} {g : Nat → Nat} (hX : Fld w X g) (hg : g i < 2 ^ w) :
    pg w (mask w) X i = g i := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_pgM]
  by_cases hk : k < w
  · simp [hk, hX i k hk]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hg (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hk]

private theorem fld_double {w A B x y c : Nat} {F : Nat → Nat}
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

private theorem fld_single {w x : Nat} {F : Nat → Nat} (hF : F x < 2 ^ w) :
    Fld w (F x) (fun i => if i < 1 then F (x + i) else 0) := by
  refine fld_congr (fld_one hF) ?_
  intro i
  by_cases h : i = 0
  · subst h
    simp
  · have h1 : ¬ i < 1 := by omega
    simp only [h, h1, ↓reduceIte]

private theorem fld_pair {w x y : Nat} {F : Nat → Nat} (hF : ∀ z, F z < 2 ^ w) (hy : y = x + 1) :
    Fld w (Nat.lor (F x) (Nat.shiftLeft (F y) w)) (fun i => if i < 2 then F (x + i) else 0) := by
  have h := fld_double (F := F) (x := x) (y := y) (c := 1) (fld_single (x := x) (hF x))
    (fld_single (x := y) (hF y)) hy
  rw [Nat.mul_one] at h
  exact h

private theorem fld_pmkH (w p q : Nat) : ∀ d lo, Fld w (pmkH w (mask w) p q d lo)
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

private theorem fld_pmkH8 (w p q : Nat) : ∀ d lo, Fld w (pmkH8 w (mask w) p q d lo)
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

private theorem strictN_eqP(y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private theorem strictB_eqP(y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem iteT{α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by
  simp [h]

private theorem iteF{α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by
  simp [h]

private theorem false_of_beq{a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e
  subst e
  rw [Nat.beq_refl] at h
  exact Bool.noConfusion h

private noncomputable def pcR(n w m p q : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih b rem => nIf(Nat.beq rem (nat_lit 0), nat_lit 0,
      nIf(Nat.beq (Nat.land rem (nat_lit 1)) (nat_lit 0), ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)),
        strictN (Nat.sub n (Nat.shiftLeft rem b)) (fun lo =>
          Nat.lor (Nat.shiftLeft (nIf(Nat.blt b (nat_lit 3), pmkH w m p q b lo, pmkH8 w m p q (Nat.sub b (nat_lit 3)) lo))
              (Nat.mul w lo))
            (ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)))))))

private theorem pcomp_eq_pcR(n w m p q : Nat) : pcomp n w m p q = pcR n w m p q 32 0 n := rfl

private theorem pcR_succ(n w m p q k b rem : Nat) : pcR n w m p q (k + 1) b rem =
    nIf(Nat.beq rem (nat_lit 0), nat_lit 0,
      nIf(Nat.beq (Nat.land rem (nat_lit 1)) (nat_lit 0), pcR n w m p q k (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)),
        strictN (Nat.sub n (Nat.shiftLeft rem b)) (fun lo =>
          Nat.lor (Nat.shiftLeft (nIf(Nat.blt b (nat_lit 3), pmkH w m p q b lo, pmkH8 w m p q (Nat.sub b (nat_lit 3)) lo))
              (Nat.mul w lo))
            (pcR n w m p q k (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)))))) := rfl

private theorem fld_blk (w p q b lo : Nat) :
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

private theorem mod_two_pow_mono(n a k : Nat) : n % 2 ^ a ≤ n % 2 ^ (a + k) := by
  have h := Nat.mod_mod_of_dvd n (Nat.pow_dvd_pow 2 (Nat.le_add_right a k))
  rw [← h]
  exact Nat.mod_le _ _

private theorem fld_pcR (n w p q : Nat) : ∀ k b rem, rem = n / 2 ^ b →
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
        Nat.mod_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))
      refine fld_congr (fld_zero w) ?_
      intro i
      have h : ¬ (n % 2 ^ b ≤ i ∧ i < n % 2 ^ (b + (k + 1))) := by
        rw [e1, e2]
        omega
      simp only [h, ↓reduceIte]

private theorem pg_pcomp{n w p q i : Nat} (hn : n < 2 ^ 32) (hi : i < n) :
    pg w (mask w) (pcomp n w (mask w) p q) i = pg w (mask w) p (pg w (mask w) q i) := by
  have h := fld_pcR n w p q 32 0 n (by simp)
  rw [pcomp_eq_pcR, pg_of_fld h]
  · have e : n % 2 ^ (0 + 32) = n := Nat.mod_eq_of_lt (by simpa using hn)
    have c : n % 2 ^ 0 ≤ i ∧ i < n % 2 ^ (0 + 32) := by
      rw [e]
      simp only [Nat.pow_zero, Nat.mod_one]
      omega
    simp only [c, and_self, ↓reduceIte]
  · split
    · exact pg_lt _ _ _
    · exact Nat.two_pow_pos w

private theorem all_iffP{n : Nat} {f : Nat → Bool} :
    (Nat.all n fun i _ => f i) = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.all_succ, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h1 i h
      · subst h
        exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

private theorem unpack_get{n w p i : Nat} (hi : i < n) : (unpack n w p)[i]! = pg w (mask w) p i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

private theorem unpack_size(n w p : Nat) : (unpack n w p).size = n := by
  simp [unpack]

private theorem unpack_getElem{n w p i : Nat} (h : i < (unpack n w p).size) :
    (unpack n w p)[i] = pg w (mask w) p i := by
  simp [unpack]

private theorem compA_getElem{n i : Nat} {t u : Array Nat} (h : i < (compA n t u).size) :
    (compA n t u)[i] = t[u[i]!]! := by
  simp [compA]

private theorem idA_getElem{n i : Nat} (h : i < (idA n).size) : (idA n)[i] = i := by
  simp [idA]

private theorem canon_facts{n w m nw p : Nat} (hp : canonK n w m nw p = true) :
    n < 16777216 ∧ n + 1 < 2 ^ w ∧ p >>> nw = 0 ∧ ∀ i < n, pg w m p i < n := by
  unfold canonK szOK at hp
  simp only [bAnd_iff] at hp
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  refine ⟨by simpa [Nat.blt_eq] using h1, ?_, by simpa using h3, fun i hi => ?_⟩
  · simpa [Nat.blt_eq, Nat.shiftLeft_eq] using h2
  · simpa [Nat.blt_eq] using allN_spec h4 i hi

private theorem eq_of_fields{n w p q : Nat} (hw : 0 < w) (hp : p >>> (n * w) = 0)
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

private theorem foldl_scatter{n : Nat} {t : Array Nat} {R : Nat → Nat}
    (ht : ∀ i < n, t[i]! < n ∧ R t[i]! = i) : ∀ k ≤ n,
    (List.foldl (fun b a => b.setIfInBounds t[a]! a) (Array.replicate n 0) (List.range' 0 k)).size = n ∧
    ∀ i < k, (List.foldl (fun b a => b.setIfInBounds t[a]! a) (Array.replicate n 0)
      (List.range' 0 k))[t[i]!]! = i := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨hs, hv⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul]
    refine ⟨by simp [hs], fun i hi => ?_⟩
    have htk := ht k (by omega)
    have hti := ht i (by omega)
    rw [getElem!_pos _ _ (by simp [hs]; exact hti.1),
      Array.getElem_setIfInBounds (by rw [hs]; exact hti.1)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · have hne : t[k]! ≠ t[i]! := by
        intro e
        have := htk.2
        rw [e, hti.2] at this
        omega
      simp only [hne, ↓reduceIte]
      rw [← getElem!_pos _ _ (by rw [hs]; exact hti.1)]
      exact hv i h
    · subst h
      simp

private theorem szOK_facts {n w : Nat} (h : szOK n w = true) : n < 16777216 ∧ n + 1 < 2 ^ w := by
  unfold szOK at h
  simp only [bAnd_iff] at h
  exact ⟨by simpa [Nat.blt_eq] using h.1, by simpa [Nat.blt_eq, Nat.shiftLeft_eq] using h.2⟩

private theorem w_pos {n w : Nat} (hw : n + 1 < 2 ^ w) : 0 < w := by
  rcases Nat.eq_zero_or_pos w with h0 | h0
  · subst h0
    simp at hw
  · exact h0

private theorem compA_unpack {n w p q : Nat} (hn : n < 2 ^ 32)
    (hq : ∀ i < n, pg w (mask w) q i < n) :
    compA n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) := by
  apply Array.ext
  · simp [compA, unpack_size]
  · intro i h1 _
    have hi : i < n := by simpa [compA] using h1
    rw [compA_getElem, unpack_get hi, unpack_get (hq i hi), unpack_getElem, pg_pcomp hn hi]

private theorem eqA_self (n : Nat) (t : Array Nat) : eqA n t t = true := by
  unfold eqA allLt
  rw [all_iffP]
  intro i _
  simp

private theorem eqA_false {n w p q : Nat} (hw : 0 < w) (hp : p >>> (n * w) = 0)
    (hq : q >>> (n * w) = 0) (hne : p ≠ q) : eqA n (unpack n w p) (unpack n w q) = false := by
  apply Bool.eq_false_iff.2
  intro he
  unfold eqA allLt at he
  rw [all_iffP] at he
  apply hne
  refine eq_of_fields hw hp hq (fun i hi => ?_)
  have := he i hi
  rw [unpack_get hi, unpack_get hi] at this
  simpa using this

private theorem fld_pmkT (n w : Nat) (f : Nat → Nat) (hf : ∀ x < n, f x < 2 ^ w) : ∀ d lo,
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

private noncomputable def clogR (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun _ ih => nIf(Nat.blt (Nat.shiftLeft (nat_lit 1) ih) n, Nat.succ ih, ih))

private theorem clogR_spec (n : Nat) : ∀ k, clogR n k = k ∨ n ≤ 2 ^ clogR n k
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

private theorem clog_spec {n : Nat} (hn : n < 16777216) : n ≤ 2 ^ clog n := by
  have e : clog n = clogR n 24 := rfl
  rw [e]
  rcases clogR_spec n 24 with h | h
  · rw [h]
    have : (2 : Nat) ^ 24 = 16777216 := rfl
    omega
  · exact h

private theorem fld_pidn {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
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

private theorem pg_pidn {n w i : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (hi : i < n) :
    pg w (mask w) (pidn n w) i = i := by
  rw [pg_of_fld (fld_pidn hn hw) (by simp only [hi, ↓reduceIte]; omega)]
  simp [hi]

private theorem unpack_pidn {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    unpack n w (pidn n w) = idA n := by
  apply Array.ext
  · simp [unpack_size, idA]
  · intro i h1 _
    have hi : i < n := by simpa [unpack_size] using h1
    rw [unpack_getElem, idA_getElem, pg_pidn hn hw hi]

private theorem shr_zero_of_fld {n w X : Nat} {g : Nat → Nat} (hw : 0 < w) (hX : Fld w X g)
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

private theorem pidn_shr {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    pidn n w >>> (n * w) = 0 :=
  shr_zero_of_fld (w_pos hw) (fld_pidn hn hw) (fun i hi => by
    have : ¬ i < n := by omega
    simp [this])

private theorem perm_facts {n w p r : Nat} (h : permOK n w (mask w) (n * w) p r = true) :
    (∀ i < n, pg w (mask w) p i < n ∧ pg w (mask w) r (pg w (mask w) p i) = i) ∧
      ∀ j < n, ∃ i < n, pg w (mask w) p i = j := by
  unfold permOK at h
  simp only [bAnd_iff] at h
  obtain ⟨-, -, ha⟩ := h
  have hpr : ∀ i < n, pg w (mask w) p i < n ∧ pg w (mask w) r (pg w (mask w) p i) = i := by
    intro i hi
    have := allN_spec ha i hi
    rw [strictB_eqP] at this
    simp only [bAnd_iff] at this
    exact ⟨by simpa [Nat.blt_eq] using this.1, Nat.eq_of_beq_eq_true this.2⟩
  refine ⟨hpr, fun j hj => ?_⟩
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n) (t := Finset.range n)
    (fun a _ => pg w (mask w) p a) (fun a ha => by simpa using (hpr a (by simpa using ha)).1)
    (fun a₁ a₂ h₁ h₂ e => by
      have e1 := (hpr a₁ (by simpa using h₁)).2
      have e2 := (hpr a₂ (by simpa using h₂)).2
      have e' : pg w (mask w) p a₁ = pg w (mask w) p a₂ := e
      rw [e'] at e1
      omega) le_rfl
  obtain ⟨i, hi, e⟩ := hsurj j (by simpa using hj)
  exact ⟨i, by simpa using hi, e.symm⟩

private theorem perm_inv_lt {n w p r : Nat} (h : permOK n w (mask w) (n * w) p r = true) :
    ∀ j < n, pg w (mask w) r j < n := by
  obtain ⟨hpr, hs⟩ := perm_facts h
  intro j hj
  obtain ⟨i, hi, e⟩ := hs j hj
  rw [← e, (hpr i hi).2]
  exact hi

private theorem invCand_unpack {n w p r : Nat} (h : permOK n w (mask w) (n * w) p r = true) :
    invCand n (unpack n w p) = unpack n w r := by
  obtain ⟨hpr, hsurj⟩ := perm_facts h
  have ht : ∀ i < n, (unpack n w p)[i]! < n ∧ pg w (mask w) r (unpack n w p)[i]! = i := by
    intro i hi
    rw [unpack_get hi]
    exact hpr i hi
  obtain ⟨hs, hv⟩ := foldl_scatter ht n le_rfl
  have e : invCand n (unpack n w p) = List.foldl (fun b a => b.setIfInBounds (unpack n w p)[a]! a)
      (Array.replicate n 0) (List.range' 0 n) := by
    simp [invCand, Id.run]
    rfl
  rw [e]
  apply Array.ext
  · rw [hs, unpack_size]
  · intro j h1 h2
    have hj : j < n := by simpa [unpack_size] using h2
    obtain ⟨i, hi', e⟩ := hsurj j hj
    have := hv i hi'
    rw [unpack_get hi', e, getElem!_pos _ _ (by rw [hs]; exact hj)] at this
    rw [this, unpack_getElem, ← e, (hpr i hi').2]

private noncomputable def letK (S SI : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
    SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))

private theorem letK_even {S SI : Nat → Nat} {c : Nat} (hc : c % 2 = 0) :
    letK S SI c = S (c / 2 - 1) := by
  have e : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  unfold letK
  rw [e, hc, shr_eq, Nat.pow_one]
  rfl

private theorem letK_odd {S SI : Nat → Nat} {c : Nat} (hc : c % 2 = 1) :
    letK S SI c = SI (c / 2 - 1) := by
  have e : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  unfold letK
  rw [e, hc, shr_eq, Nat.pow_one]
  rfl

private theorem wordK_cons (n w m idn : Nat) (S SI : Nat → Nat) (z : Int) (wd : List Int) :
    wordK n w m idn S SI (z :: wd) = pcomp n w m (letK S SI (icode z)) (wordK n w m idn S SI wd) := by
  change strictN (wordK n w m idn S SI wd)
    (fun T => strictN (icode z) (fun c => pcomp n w m (letK S SI c) T)) = _
  simp only [strictN_eqP]

private theorem lettersK_cons (j : Nat) (z : Int) (wd : List Int) :
    lettersK j (z :: wd) = bAnd(Nat.blt (nat_lit 0) (icode z),
      bAnd(Nat.ble (Nat.shiftRight (icode z) (nat_lit 1)) j, lettersK j wd)) :=
  strictB_eqP (icode z) (fun c => bAnd(Nat.blt (nat_lit 0) c,
    bAnd(Nat.ble (Nat.shiftRight c (nat_lit 1)) j, lettersK j wd)))

private theorem icode_ofNat (k : Nat) : icode (Int.ofNat k) = k + k := rfl

private theorem icode_negSucc (k : Nat) : icode (Int.negSucc k) = k + 1 + (k + 1) + 1 := rfl

private theorem letter_ok {j : Nat} {z : Int} (h1 : Nat.blt (nat_lit 0) (icode z) = true)
    (h2 : Nat.ble (Nat.shiftRight (icode z) (nat_lit 1)) j = true) : z ≠ 0 ∧ z.natAbs ≤ j := by
  have h1' := Nat.blt_eq.mp h1
  have h2' := Nat.ble_eq.mp h2
  rw [shr_eq, Nat.pow_one] at h2'
  cases z with
  | ofNat k =>
    rw [icode_ofNat] at h1' h2'
    have hk : k ≠ 0 := by omega
    have ea : (Int.ofNat k).natAbs = k := rfl
    refine ⟨fun e => hk (by simpa using e), ?_⟩
    rw [ea]
    omega
  | negSucc k =>
    rw [icode_negSucc] at h2'
    have ea : (Int.negSucc k).natAbs = k + 1 := rfl
    refine ⟨Int.negSucc_ne_zero k, ?_⟩
    rw [ea]
    omega

private theorem lettersOK_of {j : Nat} : ∀ {wd : List Int}, lettersK j wd = true →
    lettersOK j wd = true
  | [], _ => rfl
  | z :: wd, h => by
    rw [lettersK_cons] at h
    simp only [bAnd_iff] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hz := letter_ok h1 h2
    have ih := lettersOK_of h3
    unfold lettersOK at ih ⊢
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨by simpa using hz, ih⟩

private theorem map_get! {S : Array (Array Nat)} {f : Array Nat → Array Nat} {k : Nat}
    (hk : k < S.size) : (S.map f)[k]! = f S[k]! := by
  rw [getElem!_pos (S.map f) k (by simpa using hk), Array.getElem_map, getElem!_pos S k hk]

private theorem letter_sound {n w kS : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}
    (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hperm : ∀ j < kS, permOK n w (mask w) (n * w) (PS j) (PSI j) = true) {z : Int}
    (h1 : Nat.blt (nat_lit 0) (icode z) = true)
    (h2 : Nat.ble (Nat.shiftRight (icode z) (nat_lit 1)) kS = true) :
    unpack n w (letK PS PSI (icode z)) = letterA S (rawInvs n S) z ∧
      ∀ i < n, pg w (mask w) (letK PS PSI (icode z)) i < n := by
  have h1' := Nat.blt_eq.mp h1
  have h2' := Nat.ble_eq.mp h2
  rw [shr_eq, Nat.pow_one] at h2'
  cases z with
  | ofNat k =>
    rw [icode_ofNat] at h1' h2'
    have hk : k + k = icode (Int.ofNat k) := rfl
    have hL : letK PS PSI (icode (Int.ofNat k)) = PS (k - 1) := by
      rw [← hk, letK_even (by omega)]
      congr 1
      omega
    have hj : k - 1 < kS := by omega
    have hk0 : 0 < k := by omega
    have h0 : (0 : Int) < Int.ofNat k := Int.ofNat_lt.mpr hk0
    have et : (Int.ofNat k).toNat = k := rfl
    rw [hL]
    refine ⟨?_, fun i hi => ((perm_facts (hperm _ hj)).1 i hi).1⟩
    unfold letterA
    rw [iteT h0, et, hS.2 _ hj]
  | negSucc k =>
    rw [icode_negSucc] at h2'
    have hk : k + 1 + (k + 1) + 1 = icode (Int.negSucc k) := rfl
    have hL : letK PS PSI (icode (Int.negSucc k)) = PSI k := by
      rw [← hk, letK_odd (by omega)]
      congr 1
      omega
    have hj : k < kS := by omega
    have h0 : ¬ (0 : Int) < Int.negSucc k := Int.not_lt.mpr (Int.le_of_lt (Int.negSucc_lt_zero k))
    have et : (-Int.negSucc k).toNat = k + 1 := rfl
    rw [hL]
    refine ⟨?_, perm_inv_lt (hperm _ hj)⟩
    unfold letterA
    rw [iteF h0, et, Nat.add_sub_cancel, rawInvs, map_get! (by rw [hS.1]; exact hj), hS.2 _ hj,
      invCand_unpack (hperm _ hj)]

private noncomputable def fixR (w m p : Nat) : Nat → List Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => List Nat → Nat → Bool)
    (fun L _ => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
    (fun _ ih L i => bIf(Nat.beq (pg w m p i) i,
      List.rec (motive := fun _ => Bool) false (fun x xs _ => bAnd(Nat.beq x i, ih xs (Nat.succ i))) L,
      ih L (Nat.succ i)))

private theorem fixR_spec (w m p : Nat) : ∀ k L i, fixR w m p k L i = true →
    (List.range' i k).filter (fun q => pg w m p q == q) = L
  | 0, L, i, h => by
    cases L with
    | nil => rfl
    | cons x xs =>
      have h' : false = true := h
      exact absurd h' Bool.false_ne_true
  | k + 1, L, i, h => by
    rw [List.range'_succ, List.filter_cons]
    cases hb : Nat.beq (pg w m p i) i
    · have h' : fixR w m p k L (Nat.succ i) = true := by
        have e : fixR w m p (k + 1) L i = Bool.rec (motive := fun _ => Bool)
            (fixR w m p k L (Nat.succ i))
            (List.rec (motive := fun _ => Bool) false
              (fun x xs _ => bAnd(Nat.beq x i, fixR w m p k xs (Nat.succ i))) L)
            (Nat.beq (pg w m p i) i) := rfl
        rw [e, hb] at h
        exact h
      have hne : pg w m p i ≠ i := false_of_beq hb
      have hf : (pg w m p i == i) = false := by simpa using hne
      rw [hf]
      exact fixR_spec w m p k L (i + 1) h'
    · have e : fixR w m p (k + 1) L i = Bool.rec (motive := fun _ => Bool)
          (fixR w m p k L (Nat.succ i))
          (List.rec (motive := fun _ => Bool) false
            (fun x xs _ => bAnd(Nat.beq x i, fixR w m p k xs (Nat.succ i))) L)
          (Nat.beq (pg w m p i) i) := rfl
      rw [e, hb] at h
      have heq : pg w m p i = i := Nat.eq_of_beq_eq_true hb
      have ht : (pg w m p i == i) = true := by simpa using heq
      rw [ht]
      cases L with
      | nil =>
        have h' : false = true := h
        exact absurd h' Bool.false_ne_true
      | cons x xs =>
        have h' : bAnd(Nat.beq x i, fixR w m p k xs (Nat.succ i)) = true := h
        rw [bAnd_iff] at h'
        rw [Nat.eq_of_beq_eq_true h'.1]
        simp only [↓reduceIte]
        rw [fixR_spec w m p k xs (i + 1) h'.2]

theorem commK_sound {n w p q : Nat} (h : commK n w (mask w) (n * w) p q = true) :
    commutesA n (unpack n w p) (unpack n w q) = true := by
  unfold commK at h
  simp only [bAnd_iff] at h
  obtain ⟨hp, hq, he⟩ := h
  obtain ⟨hn, -, -, hp4⟩ := canon_facts hp
  obtain ⟨-, -, -, hq4⟩ := canon_facts hq
  unfold commutesA
  rw [compA_unpack (by omega) hq4, compA_unpack (by omega) hp4, Nat.eq_of_beq_eq_true he]
  exact eqA_self _ _

theorem sqIdK_sound {n w p : Nat} (h : sqIdK n w (mask w) (n * w) (pidn n w) p = true) :
    eqA n (compA n (unpack n w p) (unpack n w p)) (idA n) = true := by
  unfold sqIdK at h
  simp only [bAnd_iff] at h
  obtain ⟨hp, he⟩ := h
  obtain ⟨hn, hw, -, hp4⟩ := canon_facts hp
  rw [compA_unpack (by omega) hp4, Nat.eq_of_beq_eq_true he, unpack_pidn hn hw]
  exact eqA_self _ _

theorem neIdK_sound {n w p : Nat} (h : neIdK n w (mask w) (n * w) (pidn n w) p = true) :
    eqA n (unpack n w p) (idA n) = false := by
  unfold neIdK at h
  simp only [bAnd_iff] at h
  obtain ⟨hp, hne⟩ := h
  obtain ⟨hn, hw, hp0, -⟩ := canon_facts hp
  rw [← unpack_pidn hn hw]
  refine eqA_false (w_pos hw) hp0 (pidn_shr hn hw) ?_
  intro e
  rw [e, Nat.beq_refl] at hne
  exact Bool.false_ne_true hne

private theorem commutes_unpack {n w g s : Nat} (hn : n < 2 ^ 32) (hw : 0 < w)
    (hg : ∀ i < n, pg w (mask w) g i < n) (hs : ∀ i < n, pg w (mask w) s i < n) :
    commutesA n (unpack n w g) (unpack n w s) =
      Nat.beq (pcomp n w (mask w) g s) (pcomp n w (mask w) s g) := by
  unfold commutesA
  rw [compA_unpack hn hs, compA_unpack hn hg]
  cases e : Nat.beq (pcomp n w (mask w) g s) (pcomp n w (mask w) s g)
  · exact eqA_false hw (PackFld.pcomp_shr hn hw) (PackFld.pcomp_shr hn hw)
      (fun he => by rw [he, Nat.beq_refl] at e; exact absurd e (by decide))
  · rw [Nat.eq_of_beq_eq_true e]
    exact eqA_self _ _

private theorem center_step {n w kG z G : Nat} {PS : Nat → Nat} {S : Array (Array Nat)}
    (hn : n < 16777216) (hw' : n + 1 < 2 ^ w) (hGr : ∀ i < n, pg w (mask w) G i < n)
    (hkG : kG ≤ S.size) (hSk : ∀ k < kG, S[k]! = unpack n w (PS k))
    (hPSr : ∀ k < kG, ∀ i < n, pg w (mask w) (PS k) i < n)
    (hk : Bool.rec (motive := fun _ => Bool) true
      (Bool.rec (motive := fun _ => Bool) (Nat.beq G z) true (Nat.beq G (pidn n w)))
      (allN kG fun k => Nat.beq (pcomp n w (mask w) G (PS k)) (pcomp n w (mask w) (PS k) G)) =
        true) :
    (!(Nat.all (S.extract 0 kG).size fun k _ =>
        commutesA n (unpack n w G) (S.extract 0 kG)[k]!) ||
      eqA n (unpack n w G) (idA n) || eqA n (unpack n w G) (unpack n w z)) = true := by
  have hw : 0 < w := w_pos hw'
  have hsz : (S.extract 0 kG).size = kG := by simp; omega
  have hget : ∀ k < kG, (S.extract 0 kG)[k]! = unpack n w (PS k) := by
    intro k hk
    rw [getElem!_pos _ k (by rw [hsz]; exact hk), Array.getElem_extract]
    simp only [Nat.zero_add]
    rw [← getElem!_pos S k (by omega)]
    exact hSk k hk
  cases hall : allN kG fun k => Nat.beq (pcomp n w (mask w) G (PS k)) (pcomp n w (mask w) (PS k) G)
  · have hA : (Nat.all (S.extract 0 kG).size fun k _ =>
        commutesA n (unpack n w G) (S.extract 0 kG)[k]!) = false := by
      apply Bool.eq_false_iff.2
      intro H
      rw [all_iffP] at H
      have : allN kG (fun k => Nat.beq (pcomp n w (mask w) G (PS k))
          (pcomp n w (mask w) (PS k) G)) = true := PackFld.allN_of_forall fun k hk => by
        rw [← commutes_unpack (by omega) hw hGr (hPSr k hk), ← hget k hk]
        exact H k (by rw [hsz]; exact hk)
      rw [hall] at this
      exact Bool.false_ne_true this
    rw [hA]
    rfl
  · rw [hall] at hk
    have hk2 : Bool.rec (motive := fun _ => Bool) (Nat.beq G z) true (Nat.beq G (pidn n w)) =
      true := hk
    cases e : Nat.beq G (pidn n w)
    · rw [e] at hk2
      have hz : G = z := Nat.eq_of_beq_eq_true hk2
      rw [hz, eqA_self, Bool.or_true]
    · have hi : G = pidn n w := Nat.eq_of_beq_eq_true e
      rw [hi, unpack_pidn hn hw', eqA_self, Bool.or_true, Bool.true_or]

theorem center3K_sound {n w kS kG BP z : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds n w PS kS 3 BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hG : kG ≤ kS)
    (_hz : canonK n w (mask w) (n * w) z = true)
    (h : center3K n w (mask w) (n * w) (pidn n w) PS LR TR kG z = true) :
    centerCheck3 n (rawLevels n S base) (S.extract 0 kG) (unpack n w z) = true := by
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have hn : n < 16777216 := by have := hb.2.2.1; omega
  have hn32 : n < 2 ^ 32 := by omega
  have hw' : n + 1 < 2 ^ w := hb.2.1
  have hw : 0 < w := w_pos hw'
  have hS : S.size = kS := hb.2.2.2.1
  have hSk : ∀ k < kS, S[k]! = unpack n w (PS k) := hb.2.2.2.2.1
  have hPSr : ∀ k < kS, ∀ i < n, pg w (mask w) (PS k) i < n := fun k hk i hi =>
    Nat.blt_eq.mp (allN_spec (range_of_permOK (allN_spec hp k hk)) i hi)

  have hlev : ∀ i < 3, (rawLevels n S base)[i]!.pts.size = rcnt (LR i) ∧
      ∀ k < rcnt (LR i), (∀ x < n, pg w (mask w) (TR (roff n (n * w) (LR i) + k)) x < n) ∧
        ∀ x < n, ((rawLevels n S base)[i]!.tr[k]!)[x]! =
          pg w (mask w) (TR (roff n (n * w) (LR i) + k)) x := by
    intro i hi
    obtain ⟨A, P⟩ := Raw.Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
    refine ⟨A.cnt.symm, fun k hk => ⟨fun x hx => ?_, fun x hx => ?_⟩⟩
    · rw [(P k hk).1 ⟨x, hx⟩]
      exact Fin.is_lt _
    · have R := (A.tr k (by rw [← A.cnt]; exact hk)).1 ⟨x, hx⟩
      rw [(P k hk).1 ⟨x, hx⟩]
      exact R
  obtain ⟨c0, T0⟩ := hlev 0 (by omega)
  obtain ⟨c1, T1⟩ := hlev 1 (by omega)
  obtain ⟨c2, T2⟩ := hlev 2 (by omega)
  have cget : ∀ {t u : Array Nat} {j : Nat}, j < n → (compA n t u)[j]! = t[u[j]!]! := by
    intro t u j hj
    rw [getElem!_pos _ j (by simp [compA]; exact hj)]
    exact compA_getElem _
  unfold center3K at h
  simp only [strictB_eqP] at h
  unfold centerCheck3 allLt
  rw [all_iffP]
  intro a ha
  rw [all_iffP]
  intro b hb'
  rw [all_iffP]
  intro c hc
  rw [c0] at ha
  rw [c1] at hb'
  rw [c2] at hc
  have hk := allN_spec (allN_spec (allN_spec h a ha) b hb') c hc
  obtain ⟨ra, ea⟩ := T0 a ha
  obtain ⟨rb, eb⟩ := T1 b hb'
  obtain ⟨rc, ec⟩ := T2 c hc
  have eg : compA n (compA n (rawLevels n S base)[0]!.tr[a]! (rawLevels n S base)[1]!.tr[b]!)
      (rawLevels n S base)[2]!.tr[c]! = unpack n w (pcomp n w (mask w)
        (pcomp n w (mask w) (TR (roff n (n * w) (LR 0) + a)) (TR (roff n (n * w) (LR 1) + b)))
        (TR (roff n (n * w) (LR 2) + c))) := by
    apply Array.ext
    · simp [compA, unpack_size]
    · intro i h1 _
      have hi : i < n := by simpa [compA] using h1
      rw [← getElem!_pos _ i h1, ← getElem!_pos _ i (by simpa [unpack_size] using hi), cget hi,
        ec i hi, cget (rc i hi), eb _ (rc i hi), ea _ (rb _ (rc i hi)), unpack_get hi,
        pg_pcomp hn32 hi, pg_pcomp hn32 (rc i hi)]
  have hGr : ∀ i < n, pg w (mask w) (pcomp n w (mask w)
      (pcomp n w (mask w) (TR (roff n (n * w) (LR 0) + a)) (TR (roff n (n * w) (LR 1) + b)))
      (TR (roff n (n * w) (LR 2) + c))) i < n := fun i hi => by
    rw [pg_pcomp hn32 hi, pg_pcomp hn32 (rc i hi)]
    exact ra _ (rb _ (rc i hi))
  dsimp only
  rw [eg]
  exact center_step hn hw' hGr (by omega)
    (fun k hk => hSk k (by omega)) (fun k hk => hPSr k (by omega)) hk

theorem compEqK_sound {n w p q r : Nat} (h : compEqK n w (mask w) (n * w) p q r = true) :
    compA n (unpack n w p) (unpack n w q) = unpack n w r := by
  unfold compEqK at h
  simp only [bAnd_iff] at h
  obtain ⟨hp, hq, hr⟩ := h
  have hr' : pcomp n w (mask w) p q = r := Nat.eq_of_beq_eq_true hr
  obtain ⟨hn, -, -, -⟩ := canon_facts hp
  obtain ⟨-, -, -, hq4⟩ := canon_facts hq
  apply Array.ext
  · simp [compA, unpack_size]
  · intro i h1 _
    have hi : i < n := by simpa [compA] using h1
    rw [compA_getElem, unpack_get hi, unpack_get (hq4 i hi), unpack_getElem, ← hr',
      pg_pcomp (by omega) hi]

theorem invEqK_sound {n w p r : Nat} (h : invEqK n w (mask w) (n * w) p r = true) :
    invCand n (unpack n w p) = unpack n w r ∧ isInvA n (unpack n w p) (unpack n w r) = true := by
  have hpr := (perm_facts h).1
  have ht : ∀ i < n, (unpack n w p)[i]! < n ∧ pg w (mask w) r (unpack n w p)[i]! = i := by
    intro i hi
    rw [unpack_get hi]
    exact hpr i hi
  refine ⟨invCand_unpack h, ?_⟩
  · unfold isInvA allLt
    rw [all_iffP]
    intro i hi
    have h1 := ht i hi
    rw [unpack_get h1.1]
    simp [h1.1, h1.2]

theorem powEqK_sound {n w p e r : Nat}
    (h : powEqK n w (mask w) (n * w) (pidn n w) p e r = true) :
    CFSG.Sporadic.Schreier.Co3.co3PowA n (unpack n w p) e = unpack n w r := by
  unfold powEqK at h
  simp only [bAnd_iff] at h
  obtain ⟨hp, he⟩ := h
  obtain ⟨hn, hw, -, hp4⟩ := canon_facts hp
  rw [← Nat.eq_of_beq_eq_true he]
  have key : ∀ k, CFSG.Sporadic.Schreier.Co3.co3PowA n (unpack n w p) k =
      unpack n w (ppow n w (mask w) (pidn n w) p k) ∧
      ∀ i < n, pg w (mask w) (ppow n w (mask w) (pidn n w) p k) i < n := by
    intro k
    induction k with
    | zero =>
      refine ⟨(unpack_pidn hn hw).symm, fun i hi => ?_⟩
      have e0 : ppow n w (mask w) (pidn n w) p 0 = pidn n w := rfl
      rw [e0, pg_pidn hn hw hi]
      exact hi
    | succ k ih =>
      have e1 : ppow n w (mask w) (pidn n w) p (k + 1) =
          pcomp n w (mask w) p (ppow n w (mask w) (pidn n w) p k) :=
        strictN_eqP (ppow n w (mask w) (pidn n w) p k) (fun q => pcomp n w (mask w) p q)
      have e2 : CFSG.Sporadic.Schreier.Co3.co3PowA n (unpack n w p) (k + 1) =
          compA n (unpack n w p) (CFSG.Sporadic.Schreier.Co3.co3PowA n (unpack n w p) k) := rfl
      refine ⟨?_, fun i hi => ?_⟩
      · rw [e2, ih.1, compA_unpack (by omega) ih.2, e1]
      · rw [e1, pg_pcomp (by omega) hi]
        exact hp4 _ (ih.2 i hi)
  exact (key e).1

theorem eqK_sound {n w p q : Nat} (h : eqK p q = true) :
    eqA n (unpack n w p) (unpack n w q) = true := by
  have e : p = q := Nat.eq_of_beq_eq_true h
  subst e
  unfold eqA allLt
  rw [all_iffP]
  intro i _
  simp

theorem neK_sound {n w p q : Nat} (h : neK n w (mask w) (n * w) p q = true) :
    eqA n (unpack n w p) (unpack n w q) = false := by
  unfold neK at h
  simp only [bAnd_iff] at h
  obtain ⟨hp, hq, hne⟩ := h
  obtain ⟨-, hw, hp0, -⟩ := canon_facts hp
  obtain ⟨-, -, hq0, -⟩ := canon_facts hq
  have hpq : p ≠ q := by
    intro e
    subst e
    have : Nat.beq p p = true := Nat.beq_refl p
    rw [this] at hne
    exact Bool.false_ne_true hne
  have hw0 : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · subst h0
      simp at hw
    · exact h0
  apply Bool.eq_false_iff.2
  intro he
  unfold eqA allLt at he
  rw [all_iffP] at he
  apply hpq
  refine eq_of_fields hw0 hp0 hq0 (fun i hi => ?_)
  have := he i hi
  rw [unpack_get hi, unpack_get hi] at this
  simpa using this

theorem wordEqK_sound {n w kS r : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}
    {wd : List Int} (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (h : wordEqK n w (mask w) (pidn n w) PS PSI kS wd r = true) :
    wordA n S (rawInvs n S) wd = unpack n w r ∧ lettersOK kS wd = true := by
  unfold wordEqK at h
  simp only [bAnd_iff] at h
  obtain ⟨hsz, hl, hr⟩ := h
  obtain ⟨hn, hw⟩ := szOK_facts hsz
  have hperm : ∀ j < kS, permOK n w (mask w) (n * w) (PS j) (PSI j) = true :=
    fun j hj => allN_spec hp j hj
  refine ⟨?_, lettersOK_of hl⟩
  rw [← Nat.eq_of_beq_eq_true hr]
  have key : ∀ wd : List Int, lettersK kS wd = true →
      wordA n S (rawInvs n S) wd = unpack n w (wordK n w (mask w) (pidn n w) PS PSI wd) ∧
      ∀ i < n, pg w (mask w) (wordK n w (mask w) (pidn n w) PS PSI wd) i < n := by
    intro wd
    induction wd with
    | nil =>
      intro _
      refine ⟨(unpack_pidn hn hw).symm, fun i hi => ?_⟩
      have e0 : wordK n w (mask w) (pidn n w) PS PSI [] = pidn n w := rfl
      rw [e0, pg_pidn hn hw hi]
      exact hi
    | cons z wd ih =>
      intro hl
      rw [lettersK_cons] at hl
      simp only [bAnd_iff] at hl
      obtain ⟨h1, h2, h3⟩ := hl
      obtain ⟨ih1, ih2⟩ := ih h3
      obtain ⟨hL1, hL2⟩ := letter_sound hS hperm h1 h2
      have e2 : wordA n S (rawInvs n S) (z :: wd) =
          compA n (letterA S (rawInvs n S) z) (wordA n S (rawInvs n S) wd) := rfl
      rw [wordK_cons]
      refine ⟨?_, fun i hi => ?_⟩
      · rw [e2, ih1, ← hL1, compA_unpack (by omega) ih2]
      · rw [pg_pcomp (by omega) hi]
        exact hL2 _ (ih2 i hi)
  exact (key wd hl).1

theorem idK_sound {n w : Nat} (h : idK n w (mask w) = true) : unpack n w (pidn n w) = idA n := by
  unfold idK at h
  apply Array.ext
  · simp [unpack_size, idA]
  · intro i h1 _
    have hi : i < n := by simpa [unpack_size] using h1
    rw [unpack_getElem, idA_getElem]
    exact Nat.eq_of_beq_eq_true (allN_spec h i hi)

theorem lettersK_sound {j : Nat} {wd : List Int} (h : lettersK j wd = true) :
    lettersOK j wd = true :=
  lettersOK_of h

theorem fixedK_sound {n w p : Nat} {L : List Nat} (h : fixedK n w (mask w) p L = true) :
    CFSG.Certificates.Native.fixedList n (unpack n w p) = L := by
  have hs := fixR_spec w (mask w) p n L 0 h
  rw [← List.range_eq_range'] at hs
  rw [← hs]
  unfold CFSG.Certificates.Native.fixedList
  apply List.filter_congr
  intro x hx
  rw [unpack_get (List.mem_range.mp hx)]

end CFSG.KS.Prim

end
