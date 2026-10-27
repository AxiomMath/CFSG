module

public import Certificates.Data.Kernel.Misc.A5Norm
public import Certificates.Data.A5GL42Norm
public import CFSG.Certificates.Kernel.Misc.Sp4CenSound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Misc.A5Norm

open Matrix CFSG.KD.A5Norm CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4
open Certificates.A5GL42

def PlaneOK (P : ℕ → ℕ) (t : ℕ) : Prop :=
  (∀ q, ∀ c < 65536, (P q).testBit c = c.testBit q) ∧ ∀ c < 65536, t.testBit c = true

theorem bitB_eq (x q : ℕ) : bitB x q = x.testBit q := by
  unfold bitB
  change Nat.beq ((x >>> q) &&& 1) 1 = _
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ q) with h | h <;> rw [h] <;> rfl

theorem testBit_shl1 (a c : ℕ) : (Nat.shiftLeft 1 a).testBit c = decide (a = c) := by
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

theorem selP_bit (b : Bool) (p c : ℕ) : (selP b p).testBit c = (b && p.testBit c) := by
  cases b
  · change Nat.testBit 0 c = _
    simp
  · rfl

theorem dP_bit {P : ℕ → ℕ} {t : ℕ} (hP : PlaneOK P t) {c : ℕ} (hc : c < 65536) (x y : ℕ) {i j : ℕ}
    (hi : i < 4) (hj : j < 4) :
    (dP P x y i j).testBit c = ((mul4F c x).testBit (4 * i + j) ^^ (mul4F y c).testBit (4 * i + j)) := by
  rw [mul4F_bit _ _ hi hj, mul4F_bit _ _ hi hj]
  unfold dP
  rw [CFSG.KC.Misc.GL4.letN_eq]
  simp only [Nat.xor_eq, Nat.testBit_xor, selP_bit, bitB_eq, Nat.add_eq, Nat.mul_eq, hP.1 _ c hc]
  have e0 : 4 * i + 0 = 4 * i := by omega
  have e1 : 4 * 0 + j = j := by omega
  have e2 : 4 * 1 + j = 4 + j := by omega
  have e3 : 4 * 2 + j = 8 + j := by omega
  have e4 : 4 * 3 + j = 12 + j := by omega
  rw [e0, e1, e2, e3, e4]
  simp only [Bool.and_comm (x.testBit _), Bool.xor_assoc]

theorem dAcc_bit {P : ℕ → ℕ} {t : ℕ} (hP : PlaneOK P t) {c : ℕ} (hc : c < 65536) (x y : ℕ) :
    ∀ n ≤ 16, (dAcc P x y n).testBit c = true ↔
      ∃ q < n, (mul4F c x).testBit q ≠ (mul4F y c).testBit q
  | 0, _ => by
    change Nat.testBit 0 c = true ↔ _
    simp
  | n + 1, hn => by
    have ih := dAcc_bit hP hc x y n (by omega)
    change (Nat.lor (dAcc P x y n) (dP P x y (n / 4) (n % 4))).testBit c = true ↔ _
    have hq : 4 * (n / 4) + n % 4 = n := Nat.div_add_mod n 4
    rw [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true, ih,
      dP_bit hP hc x y (by omega) (Nat.mod_lt _ (by norm_num)), hq]
    constructor
    · rintro (⟨q, hq', h⟩ | h)
      · exact ⟨q, by omega, h⟩
      · refine ⟨n, by omega, ?_⟩
        revert h
        cases (mul4F c x).testBit n <;> cases (mul4F y c).testBit n <;> simp
    · rintro ⟨q, hq', h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq' with hq' | rfl
      · exact Or.inl ⟨q, hq', h⟩
      · right
        revert h
        cases (mul4F c x).testBit q <;> cases (mul4F y c).testBit q <;> simp

theorem eqP_bit {P : ℕ → ℕ} {t : ℕ} (hP : PlaneOK P t) {c : ℕ} (hc : c < 65536) (x y : ℕ) :
    (eqP P t x y).testBit c = true ↔ mul4F c x = mul4F y c := by
  unfold eqP
  rw [Nat.xor_eq, Nat.testBit_xor, hP.2 c hc]
  have h := dAcc_bit hP hc x y 16 le_rfl
  constructor
  · intro h1
    refine Nat.eq_of_testBit_eq fun q => ?_
    by_cases hq : q < 16
    · by_contra hne
      have : (dAcc P x y 16).testBit c = true := h.2 ⟨q, hq, hne⟩
      rw [this] at h1
      exact absurd h1 (by decide)
    · rw [testBit_ge16 (mul4F_lt _ _) (by omega), testBit_ge16 (mul4F_lt _ _) (by omega)]
  · intro he
    have : (dAcc P x y 16).testBit c = false := by
      rw [Bool.eq_false_iff]
      intro h2
      obtain ⟨q, _, hq⟩ := h.1 h2
      exact hq (by rw [he])
    rw [this]
    rfl

theorem orL_bit (f : ℕ → ℕ) (c : ℕ) :
    ∀ l : List ℕ, (orL l f).testBit c = true ↔ ∃ a ∈ l, (f a).testBit c = true
  | [] => by
    change Nat.testBit 0 c = true ↔ _
    simp
  | a :: l => by
    change (Nat.lor (f a) (orL l f)).testBit c = true ↔ _
    rw [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true, orL_bit f c l]
    simp

theorem orN_bit (f : ℕ → ℕ) (c : ℕ) :
    ∀ m, (orN m f).testBit c = true ↔ ∃ u < m, (f u).testBit c = true
  | 0 => by
    change Nat.testBit 0 c = true ↔ _
    simp
  | m + 1 => by
    change (Nat.lor (orN m f) (f m)).testBit c = true ↔ _
    rw [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true, orN_bit f c m]
    constructor
    · rintro (⟨u, hu, h⟩ | h)
      · exact ⟨u, by omega, h⟩
      · exact ⟨m, by omega, h⟩
    · rintro ⟨u, hu, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
      · exact Or.inl ⟨u, hu, h⟩
      · exact Or.inr h

theorem mul4F_zero (c : ℕ) : mul4F 0 c = 0 := by
  refine Nat.eq_of_testBit_eq fun q => ?_
  by_cases hq : q < 16
  · have e : 4 * (q / 4) + q % 4 = q := Nat.div_add_mod q 4
    rw [← e, mul4F_bit _ _ (by omega) (Nat.mod_lt _ (by norm_num))]
    simp
  · rw [testBit_ge16 (mul4F_lt _ _) (by omega)]
    simp

theorem injP_bit {P : ℕ → ℕ} {t : ℕ} (hP : PlaneOK P t) {c : ℕ} (hc : c < 65536) :
    (injP P t).testBit c = true ↔ ∀ u < 15, mul4F c (colC (u + 1)) ≠ 0 := by
  unfold injP
  rw [Nat.xor_eq, Nat.testBit_xor, hP.2 c hc]
  have h := orN_bit (fun u => eqP P t (colC (Nat.succ u)) 0) c 15
  simp only [eqP_bit hP hc, mul4F_zero] at h
  constructor
  · intro h1 u hu he
    have : (orN 15 fun u => eqP P t (colC (Nat.succ u)) 0).testBit c = true := h.2 ⟨u, hu, he⟩
    rw [this] at h1
    exact absurd h1 (by decide)
  · intro h1
    have : (orN 15 fun u => eqP P t (colC (Nat.succ u)) 0).testBit c = false := by
      rw [Bool.eq_false_iff]
      intro h2
      obtain ⟨u, hu, he⟩ := h.1 h2
      exact h1 u hu he
    rw [this]
    rfl

theorem bitsL_bit (c : ℕ) : ∀ l : List ℕ, (bitsL l).testBit c = true ↔ c ∈ l
  | [] => by
    change Nat.testBit 0 c = true ↔ _
    simp
  | a :: l => by
    change (Nat.lor (Nat.shiftLeft 1 a) (bitsL l)).testBit c = true ↔ _
    rw [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true, bitsL_bit c l, Nat.shiftLeft_eq',
      Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
    simp only [decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

theorem memB_iff (S c : ℕ) : memB S c = true ↔ S.testBit c = true := by
  unfold memB
  rw [Nat.blt_eq, Nat.land_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]
  constructor
  · intro h
    by_contra hb
    have h0 : S &&& 2 ^ c = 0 := Nat.eq_of_testBit_eq fun i => by
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hi : c = i
      · subst hi
        simpa using hb
      · simp [hi]
    omega
  · intro h
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have := congrArg (fun n => n.testBit c) h0
    simp [Nat.testBit_and, h, Nat.testBit_two_pow] at this

theorem subP_sound {t X S c : ℕ} (h : subP t X S = true) (hX : X.testBit c = true)
    (ht : t.testBit c = true) : S.testBit c = true := by
  unfold subP at h
  have h0 : X &&& (t ^^^ S) = 0 := Nat.eq_of_beq_eq_true h
  have := congrArg (fun n => n.testBit c) h0
  simp only [Nat.testBit_and, Nat.testBit_xor, hX, ht, Nat.zero_testBit] at this
  revert this
  cases S.testBit c <;> simp

theorem withP_eq (k : (ℕ → ℕ) → ℕ → Bool) : withP k =
    k (fun q => lAt [CFSG.KC.F4M3B.pln 0 16, CFSG.KC.F4M3B.pln 1 16, CFSG.KC.F4M3B.pln 2 16,
      CFSG.KC.F4M3B.pln 3 16, CFSG.KC.F4M3B.pln 4 16, CFSG.KC.F4M3B.pln 5 16,
      CFSG.KC.F4M3B.pln 6 16, CFSG.KC.F4M3B.pln 7 16, CFSG.KC.F4M3B.pln 8 16,
      CFSG.KC.F4M3B.pln 9 16, CFSG.KC.F4M3B.pln 10 16, CFSG.KC.F4M3B.pln 11 16,
      CFSG.KC.F4M3B.pln 12 16, CFSG.KC.F4M3B.pln 13 16, CFSG.KC.F4M3B.pln 14 16,
      CFSG.KC.F4M3B.pln 15 16] q) (Nat.sub (Nat.pow 2 (Nat.pow 2 16)) 1) := by
  simp only [withP, CFSG.KC.F4M3B.frc_eq]

theorem planeOK_withP : PlaneOK
    (fun q => lAt [CFSG.KC.F4M3B.pln 0 16, CFSG.KC.F4M3B.pln 1 16, CFSG.KC.F4M3B.pln 2 16,
      CFSG.KC.F4M3B.pln 3 16, CFSG.KC.F4M3B.pln 4 16, CFSG.KC.F4M3B.pln 5 16,
      CFSG.KC.F4M3B.pln 6 16, CFSG.KC.F4M3B.pln 7 16, CFSG.KC.F4M3B.pln 8 16,
      CFSG.KC.F4M3B.pln 9 16, CFSG.KC.F4M3B.pln 10 16, CFSG.KC.F4M3B.pln 11 16,
      CFSG.KC.F4M3B.pln 12 16, CFSG.KC.F4M3B.pln 13 16, CFSG.KC.F4M3B.pln 14 16,
      CFSG.KC.F4M3B.pln 15 16] q) (Nat.sub (Nat.pow 2 (Nat.pow 2 16)) 1) := by
  refine ⟨fun q c hc => ?_, fun c hc => CFSG.KC.Misc.Sp4Cen.ones_bit hc⟩
  beta_reduce
  rw [lAt_eq]
  by_cases hq : q < 16
  · have e : ∀ q < 16, (([CFSG.KC.F4M3B.pln 0 16, CFSG.KC.F4M3B.pln 1 16, CFSG.KC.F4M3B.pln 2 16,
        CFSG.KC.F4M3B.pln 3 16, CFSG.KC.F4M3B.pln 4 16, CFSG.KC.F4M3B.pln 5 16,
        CFSG.KC.F4M3B.pln 6 16, CFSG.KC.F4M3B.pln 7 16, CFSG.KC.F4M3B.pln 8 16,
        CFSG.KC.F4M3B.pln 9 16, CFSG.KC.F4M3B.pln 10 16, CFSG.KC.F4M3B.pln 11 16,
        CFSG.KC.F4M3B.pln 12 16, CFSG.KC.F4M3B.pln 13 16, CFSG.KC.F4M3B.pln 14 16,
        CFSG.KC.F4M3B.pln 15 16] : List ℕ).getD q 0) = CFSG.KC.F4M3B.pln q 16 := by
      intro q hq
      interval_cases q <;> simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [e q hq, CFSG.KC.Misc.Sp4Cen.pln16_bit, decide_eq_true hc, Bool.true_and]
  · rw [List.getD_eq_default _ _ (by simp; omega), testBit_ge16 hc (by omega)]
    simp

theorem mem_iff {cs : List ℕ} (hlt : ∀ c ∈ cs, c < 65536) (g : Mat4) :
    g ∈ (cs.map ofCode).toFinset ↔ code4 g ∈ cs := by
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rwa [code4_ofCode (hlt c hc)]
  · intro h
    exact ⟨_, h, ofCode_code4 g⟩

theorem ofCode_mem {cs : List ℕ} {c : ℕ} (hc : c ∈ cs) : ofCode c ∈ (cs.map ofCode).toFinset := by
  simp only [List.mem_toFinset, List.mem_map]
  exact ⟨c, hc, rfl⟩

theorem incF_spec : ∀ (l : List ℕ) (p : ℕ), incF l p = true → (∀ x ∈ l, p < x) ∧ l.Nodup
  | [], _, _ => by simp
  | a :: l, p, h => by
    change andB (Nat.blt p a) (incF l a) = true at h
    rw [andB_iff, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := incF_spec l a h.2
    refine ⟨fun x hx => ?_, List.nodup_cons.2 ⟨fun ha => absurd (h1 a ha) (lt_irrefl a), h2⟩⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (h1 x hx)

theorem incL_nodup : ∀ l : List ℕ, incL l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    obtain ⟨h1, h2⟩ := incF_spec l a h
    exact List.nodup_cons.2 ⟨fun ha => absurd (h1 a ha) (lt_irrefl a), h2⟩

theorem card_eq {cs : List ℕ} (hlt : ∀ c ∈ cs, c < 65536) (hinc : incL cs = true) :
    (cs.map ofCode).toFinset.card = cs.length := by
  rw [List.toFinset_card_of_nodup, List.length_map]
  exact (incL_nodup cs hinc).map_on fun a ha b hb e => ofCode_inj (hlt a ha) (hlt b hb) e

structure GrpFacts (cs : List ℕ) : Prop where
  lt : ∀ c ∈ cs, c < 65536
  inc : incL cs = true
  one : id4 ∈ cs
  mul : ∀ x ∈ cs, ∀ y ∈ cs, mul4F x y ∈ cs
  inv : ∀ x ∈ cs, ∃ y ∈ cs, mul4F x y = id4

theorem grpFacts_of {cs : List ℕ} (h : grpC cs = true) : GrpFacts cs := by
  unfold grpC at h
  rw [letB_eq] at h
  simp only [andB_iff, allL_iff, anyL_iff, Nat.blt_eq, CFSG.KC.Misc.GL4.memN_iff', memB_iff,
    bitsL_bit, Nat.beq_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem grp_mem {cs : List ℕ} (h : GrpFacts cs) (g : Mat4) :
    g ∈ (cs.map ofCode).toFinset ↔ code4 g ∈ cs := mem_iff h.lt g

theorem grp_one {cs : List ℕ} (h : GrpFacts cs) : (1 : Mat4) ∈ (cs.map ofCode).toFinset := by
  rw [← ofCode_id4]
  exact ofCode_mem h.one

theorem grp_mul {cs : List ℕ} (h : GrpFacts cs) :
    ∀ x ∈ (cs.map ofCode).toFinset, ∀ y ∈ (cs.map ofCode).toFinset,
      x * y ∈ (cs.map ofCode).toFinset := by
  intro x hx y hy
  rw [grp_mem h] at hx hy ⊢
  rw [code4_mul]
  exact h.mul _ hx _ hy

theorem grp_inv {cs : List ℕ} (h : GrpFacts cs) :
    ∀ x ∈ (cs.map ofCode).toFinset, ∃ y ∈ (cs.map ofCode).toFinset, x * y = 1 := by
  intro x hx
  rw [grp_mem h] at hx
  obtain ⟨y, hy, e⟩ := h.inv _ hx
  refine ⟨ofCode y, ofCode_mem hy, ?_⟩
  rw [← ofCode_code4 x, ← mul4F_ofCode, e, ofCode_id4]

theorem complete_of {hs cs : List ℕ} {a b : ℕ} {P : ℕ → ℕ} {t : ℕ} (hP : PlaneOK P t)
    (hhs : ∀ c ∈ hs, c < 65536) (ha : a ∈ hs) (hb : b ∈ hs) (h : compC hs cs a b P t = true) :
    ∀ g : Mat4, (∃ g' : Mat4, g * g' = 1) →
      (∀ h ∈ (hs.map ofCode).toFinset, ∃ h' ∈ (hs.map ofCode).toFinset, g * h = h' * g) →
        code4 g ∈ cs := by
  intro g ⟨g', hg'⟩ hn
  have hc := code4_lt g
  have hinj : ∀ u < 15, mul4F (code4 g) (colC (u + 1)) ≠ 0 := by
    intro u hu he
    have h1 : g' * g = 1 := mul_eq_one_comm.1 hg'
    have hz : colC 0 = 0 := by decide
    rw [← hz] at he
    have h2 := congrArg ofCode he
    rw [mul4F_ofCode, ofCode_code4, colC_ofCode _ (by omega), colC_ofCode 0 (by omega),
      mul_colM] at h2
    have h3 : vecOfCode 0 = 0 := by
      funext i
      simp [vecOfCode]
    have h4 := colM_inj h2
    rw [h3] at h4
    have h5 : vecOfCode (u + 1) = 0 := by
      rw [← one_mulVec (vecOfCode (u + 1)), ← h1, ← mulVec_mulVec, h4, mulVec_zero]
    have h6 : ∀ u < 15, vecOfCode (u + 1) ≠ 0 := by decide
    exact h6 u hu h5
  have hgen : ∀ x ∈ hs, ∃ y ∈ hs, mul4F (code4 g) x = mul4F y (code4 g) := by
    intro x hx
    obtain ⟨h', hh', e⟩ := hn (ofCode x) (ofCode_mem hx)
    rw [mem_iff hhs] at hh'
    refine ⟨code4 h', hh', ?_⟩
    have := congrArg code4 e
    rwa [code4_mul, code4_mul, code4_ofCode (hhs x hx)] at this
  unfold compC at h
  have hbit := subP_sound h (by
    rw [Nat.land_eq, Nat.land_eq, Nat.testBit_and, Nat.testBit_and, (injP_bit hP hc).2 hinj]
    have hA : (orL hs fun y => eqP P t a y).testBit (code4 g) = true := by
      rw [orL_bit]
      obtain ⟨y, hy, e⟩ := hgen a ha
      exact ⟨y, hy, (eqP_bit hP hc a y).2 e⟩
    have hB : (orL hs fun y => eqP P t b y).testBit (code4 g) = true := by
      rw [orL_bit]
      obtain ⟨y, hy, e⟩ := hgen b hb
      exact ⟨y, hy, (eqP_bit hP hc b y).2 e⟩
    rw [hA, hB]
    rfl) (hP.2 _ hc)
  exact (bitsL_bit _ cs).1 hbit

theorem normFacts_of {hs cs ts : List ℕ} {a b : ℕ} {P : ℕ → ℕ} {t : ℕ} (hP : PlaneOK P t)
    (hhs : ∀ c ∈ hs, c < 65536) (ha : a ∈ hs) (hb : b ∈ hs) (hcomp : compC hs cs a b P t = true)
    (hg : grpC cs = true) (hcard : cs.length % 16 = 8) (ht : grpC ts = true) (hts : subC ts cs = true)
    (htcard : ts.length = 8) (hfree : freeC cs ts = true) :
    NormFacts (hs.map ofCode).toFinset (cs.map ofCode).toFinset (ts.map ofCode).toFinset := by
  have G := grpFacts_of hg
  have T := grpFacts_of ht
  unfold subC at hts
  rw [allL_iff] at hts
  simp only [CFSG.KC.Misc.GL4.memN_iff'] at hts
  refine ⟨grp_one G, grp_mul G, grp_inv G, ?_, ?_, ?_, grp_one T, grp_mul T, grp_inv T, ?_, ?_⟩
  · rw [card_eq G.lt G.inc]
    exact hcard
  · intro g hinv hn
    rw [grp_mem G]
    exact complete_of hP hhs ha hb hcomp g hinv hn
  · intro x hx
    rw [grp_mem T] at hx
    rw [grp_mem G]
    exact hts _ hx
  · rw [card_eq T.lt T.inc]
    exact htcard
  · intro d hd hd1 hd3
    rw [grp_mem G] at hd
    unfold freeC at hfree
    rw [allL_iff] at hfree
    have e := hfree _ hd
    simp only [orB_iff, notB_iff, anyL_iff, allL_iff, Nat.beq_eq] at e
    rcases e with e | e | ⟨tc, htc, e⟩
    · exact absurd (by rw [← ofCode_code4 d, e, ofCode_id4]) hd1
    · exact absurd (by rw [← code4_mul, ← code4_mul, hd3, code4_one]) e
    · refine ⟨ofCode tc, ofCode_mem htc, fun t' ht' et => ?_⟩
      rw [grp_mem T] at ht'
      apply e _ ht'
      have := congrArg code4 et
      rwa [code4_mul, code4_mul, code4_ofCode (T.lt tc htc)] at this

theorem noInv_of {hs : List ℕ} {a b : ℕ} {P : ℕ → ℕ} {t : ℕ} (hP : PlaneOK P t)
    (hhs : ∀ c ∈ hs, c < 65536) (ha : a ∈ hs) (hb : b ∈ hs) (h : centC a b P t = true) :
    NoInvCent (hs.map ofCode).toFinset := by
  intro g hgg hcomm
  have hc := code4_lt g
  have hcm : ∀ x ∈ hs, mul4F (code4 g) x = mul4F x (code4 g) := by
    intro x hx
    have := congrArg code4 (hcomm (ofCode x) (ofCode_mem hx))
    rwa [code4_mul, code4_mul, code4_ofCode (hhs x hx)] at this
  unfold centC at h
  have hbit := subP_sound h (by
    rw [Nat.land_eq, Nat.land_eq, Nat.testBit_and, Nat.testBit_and,
      (CFSG.KC.Misc.Sp4Cen.sqPlane_bit hc).2 (by rw [← code4_mul, hgg, code4_one]),
      (eqP_bit hP hc a a).2 (hcm a ha), (eqP_bit hP hc b b).2 (hcm b hb)]
    rfl) (hP.2 _ hc)
  rw [testBit_shl1, decide_eq_true_eq] at hbit
  rw [← ofCode_code4 g, ← hbit, ofCode_id4]

theorem fixZero_of {hs : List ℕ} {a b : ℕ} (hhs : ∀ c ∈ hs, c < 65536) (ha : a ∈ hs)
    (hb : b ∈ hs) (h : fixC a b = true) : FixZero (hs.map ofCode).toFinset := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := vec_surj v
  unfold fixC at h
  rw [allN_iff] at h
  have e := h u hu
  rw [impB_iff, andB_iff, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq] at e
  have hfix : ∀ x ∈ hs, mul4F x (colC u) = colC u := by
    intro x hx
    apply ofCode_inj (mul4F_lt _ _) (colC_lt u hu)
    rw [mul4F_ofCode, colC_ofCode u hu, mul_colM, hv _ (ofCode_mem hx)]
  have hu0 := e ⟨hfix a ha, hfix b hb⟩
  subst hu0
  decide

theorem trans_of {hs us : List ℕ} {v0 : ℕ} (hhs : ∀ c ∈ hs, c < 65536) (hus : ∀ u ∈ us, u < 16)
    (hv0 : v0 < 16) (h : transC hs us v0 = true) :
    ∀ v ∈ (us.map vecOfCode).toFinset, ∃ g ∈ (hs.map ofCode).toFinset, g *ᵥ vecOfCode v0 = v := by
  intro v hv
  simp only [List.mem_toFinset, List.mem_map] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  unfold transC at h
  rw [allL_iff] at h
  obtain ⟨c, hc, e⟩ := (anyL_iff _ _).1 (h u hu)
  rw [Nat.beq_eq] at e
  refine ⟨ofCode c, ofCode_mem hc, colM_inj ?_⟩
  rw [← mul_colM, ← colC_ofCode v0 hv0, ← mul4F_ofCode, e, colC_ofCode u (hus u hu)]

theorem vec_xor (u v : ℕ) : vecOfCode (u ^^^ v) = vecOfCode u + vecOfCode v := by
  funext i
  simp only [vecOfCode, Pi.add_apply, Nat.testBit_xor]
  cases u.testBit i <;> cases v.testBit i <;> decide

theorem mem_vec {L : List ℕ} (hL : ∀ x ∈ L, x < 16) {u : ℕ} (hu : u < 16) :
    vecOfCode u ∈ (L.map vecOfCode).toFinset ↔ u ∈ L := by
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨x, hx, e⟩
    rwa [vec_inj x (hL x hx) u hu e] at hx
  · intro h
    exact ⟨u, h, rfl⟩

theorem qab_code (a b : ZMod 2) {u : ℕ} (hu : u < 16) : Qab a b (vecOfCode u) =
    if u ∈ ([1, 2, 3, 4, 5, 6, 8, 9, 10, 12] : List ℕ) then a
    else if u ∈ ([7, 11, 13, 14, 15] : List ℕ) then b else 0 := by
  unfold Qab O1 O2
  simp only [mem_vec (L := [1, 2, 3, 4, 5, 6, 8, 9, 10, 12]) (by decide) hu,
    mem_vec (L := [7, 11, 13, 14, 15]) (by decide) hu]

theorem unique_of : ∀ a b : ZMod 2, ThirdDiff (Qab a b) → NonAdd (Qab a b) → a = 1 ∧ b = 0 := by
  intro a b h1 h2
  have h := h1 (vecOfCode 1) (vecOfCode 2) (vecOfCode 4)
  simp only [← vec_xor, Nat.reduceXor] at h
  rw [qab_code a b (u := 7) (by decide), qab_code a b (u := 3) (by decide),
    qab_code a b (u := 5) (by decide), qab_code a b (u := 6) (by decide),
    qab_code a b (u := 1) (by decide), qab_code a b (u := 2) (by decide),
    qab_code a b (u := 4) (by decide)] at h
  have hab : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hab a with rfl | rfl <;> rcases hab b with rfl | rfl
  · exfalso
    obtain ⟨u, w, hw⟩ := h2
    simp [Qab] at hw
  · exfalso
    revert h
    decide
  · exact ⟨rfl, rfl⟩
  · exfalso
    revert h
    decide

end CFSG.KC.Misc.A5Norm

end
