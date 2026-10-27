module

public import CFSG.Certificates.Kernel.KStep.Native
public import CFSG.Certificates.Kernel.KStep.Laws
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
public import Certificates.Data.Kernel.KDense.LetterOK
public import Certificates.Data.Kernel.KDense.Plan
public import Certificates.Data.Kernel.KDenseP.Chunk
public import Certificates.Data.Kernel.KDenseP.MonoBind

public section

namespace CFSG.KC.KStep

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP
open CFSG.Monster.AxisCount CFSG.Monster.B.Rep4371.Native CFSG.KC.MonsterConv.Perm

namespace XiAux

theorem testBit_ones (W q : ℕ) : (ones W).testBit q = decide (q < W) := by
  rw [Benes.ones_eq, Nat.testBit_two_pow_sub_one]

theorem SX_eq : SX = 2 ^ 17 := rfl

theorem SA_eq : SA = 2 ^ 10 := rfl

theorem SA_1024 : SA = 1024 := rfl

theorem SX_131072 : SX = 131072 := rfl

theorem idPlane_SX {b : ℕ} (hb : b < 17) (p : ℕ) :
    (idPlane SX b).testBit p = (decide (p < SX) && p.testBit b) :=
  Benes.idPlane_testBit (k := 17) hb p

theorem idPlane_SA {b : ℕ} (hb : b < 10) (p : ℕ) :
    (idPlane SA b).testBit p = (decide (p < SA) && p.testBit b) :=
  Benes.idPlane_testBit (k := 10) hb p

theorem tbd (x b : ℕ) : x.testBit b = decide (x / 2 ^ b % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq

theorem valA_small : ∀ p < 1024, valA.testBit p = decide (p % 32 < 24 ∧ p / 32 < 24) := by
  decide +kernel

theorem valA_lt' : valA < 2 ^ 1024 := by decide +kernel

theorem testBit_valA (p : ℕ) : valA.testBit p = decide (p < 1024 ∧ p % 32 < 24 ∧ p / 32 < 24) := by
  by_cases hp : p < 1024
  · rw [valA_small p hp]
    simp [hp]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le valA_lt' (Nat.pow_le_pow_right (by decide)
      (by omega)))]
    simp [hp]

theorem testBit_valW (p : ℕ) : valW.testBit p = decide (p < 131072 ∧ p % 32 < 24) := by
  change (ones SX ^^^ (idPlane SX 3 &&& idPlane SX 4)).testBit p = _
  rw [Nat.testBit_xor, Nat.testBit_and, testBit_ones, idPlane_SX (by decide), idPlane_SX (by decide)]
  have h3 : p.testBit 3 = (p % 32).testBit 3 := by
    rw [(by rfl : (32 : ℕ) = 2 ^ 5), Nat.testBit_mod_two_pow]; rfl
  have h4 : p.testBit 4 = (p % 32).testBit 4 := by
    rw [(by rfl : (32 : ℕ) = 2 ^ 5), Nat.testBit_mod_two_pow]; rfl
  have hm : ∀ x < 32, (x.testBit 3 && x.testBit 4) = decide (24 ≤ x) := by decide
  rw [h3, h4]
  by_cases hp : p < SX
  · rw [decide_eq_true hp, Bool.true_and, Bool.true_and, hm _ (Nat.mod_lt _ (by decide))]
    have e : decide (p < 131072 ∧ p % 32 < 24) = !decide (24 ≤ p % 32) := by
      by_cases h : 24 ≤ p % 32
      · simp [h]
      · simp [h]
        exact ⟨hp, by omega⟩
    rw [e]
    cases decide (24 ≤ p % 32) <;> rfl
  · have : ¬ p < 131072 := hp
    simp [hp, this]

theorem lt_of_tb {x S : ℕ} (h : ∀ i, x.testBit i = true → i < S) : x < 2 ^ S :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    cases e : x.testBit i
    · rfl
    · exact absurd (h i e) (by omega)

theorem valA_lt : valA < 2 ^ SA := lt_of_tb fun i hi => by
  rw [testBit_valA] at hi
  simp only [decide_eq_true_eq] at hi
  exact hi.1

theorem valW_lt : valW < 2 ^ SX := lt_of_tb fun i hi => by
  rw [testBit_valW] at hi
  simp only [decide_eq_true_eq] at hi
  exact hi.1

theorem dmod (x : ℕ) : decide (x % 2 = 1) = !decide (x % 2 = 0) := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem testBit_clr_SA {b : ℕ} (hb : b < 10) (p : ℕ) :
    (clr SA b).testBit p = decide (p < 1024 ∧ p / 2 ^ b % 2 = 0) := by
  change (ones SA ^^^ idPlane SA b).testBit p = _
  rw [Nat.testBit_xor, testBit_ones, idPlane_SA hb, tbd, dmod, (rfl : SA = 1024)]
  generalize p / 2 ^ b % 2 = z
  by_cases h0 : p < 1024 <;> by_cases h1 : z = 0 <;> simp [h0, h1] <;>
    first | exact h0 | exact Nat.le_of_not_lt h0

theorem testBit_idPlane_SA {b : ℕ} (hb : b < 10) (p : ℕ) :
    (idPlane SA b).testBit p = decide (p < 1024 ∧ p / 2 ^ b % 2 = 1) := by
  rw [idPlane_SA hb, tbd, (rfl : SA = 1024)]
  generalize p / 2 ^ b % 2 = z
  by_cases h0 : p < 1024 <;> by_cases h1 : z = 1 <;> simp [h0, h1] <;>
    first | exact h0 | exact Nat.le_of_not_lt h0

theorem testBit_clr_SX {b : ℕ} (hb : b < 17) (p : ℕ) :
    (clr SX b).testBit p = decide (p < 131072 ∧ p / 2 ^ b % 2 = 0) := by
  change (ones SX ^^^ idPlane SX b).testBit p = _
  rw [Nat.testBit_xor, testBit_ones, idPlane_SX hb, tbd, dmod, (rfl : SX = 131072)]
  generalize p / 2 ^ b % 2 = z
  by_cases h0 : p < 131072 <;> by_cases h1 : z = 0 <;> simp [h0, h1] <;>
    first | exact h0 | exact Nat.le_of_not_lt h0

theorem testBit_idPlane_SX {b : ℕ} (hb : b < 17) (p : ℕ) :
    (idPlane SX b).testBit p = decide (p < 131072 ∧ p / 2 ^ b % 2 = 1) := by
  rw [idPlane_SX hb, tbd, (rfl : SX = 131072)]
  generalize p / 2 ^ b % 2 = z
  by_cases h0 : p < 131072 <;> by_cases h1 : z = 1 <;> simp [h0, h1] <;>
    first | exact h0 | exact Nat.le_of_not_lt h0

variable {M : ℕ} {h : ZMod M}

theorem two_hN {np : ℕ} (hnp : 1 ≤ np) : 2 * hN np = 1 := by
  unfold hN
  rw [← pow_succ', Nat.sub_add_cancel hnp]
  have h0 : ((2 ^ np - 1 : ℕ) : ZMod (2 ^ np - 1)) = 0 := ZMod.natCast_self _
  rw [Nat.cast_sub Nat.one_le_two_pow] at h0
  push_cast at h0
  exact sub_eq_zero.mp h0

theorem sgnI_mul (b : Bool) (x : ZMod M) : ((sgnI b : ℤ) : ZMod M) * x = if b then -x else x := by
  cases b <;> simp [sgnI]

@[expose] def c4z (w u : ℕ) : ℤ := c4N w u / 32

@[expose] def Cl (S R b : ℕ) : Prop :=
  ∀ q < S, R.testBit q = true → q.testBit b = false → R.testBit (q + 2 ^ b) = true

variable {np : ℕ} {O : POps}

theorem blk4 (hO : PLaw np O) {k S b0 b1 R d M0 M1 x : ℕ} (hS : S = 2 ^ k) (hb0 : b0 < k)
    (hb1 : b1 < k) (hR : R < 2 ^ S) (hc0 : Cl S R b0) (hc1 : Cl S R b1) (hM0 : M0 < 2 ^ S)
    (hv : Benes.ValidIn S d M1) (hx : Bd np S x) (P : ℕ → ℕ) (e1 : P 1 = P 0 + 2 ^ b0)
    (e2 : P 2 = P 0 + 2 ^ b1) (e3 : P 3 = P 0 + 2 ^ b0 + 2 ^ b1) (hP : P 3 < S)
    (t00 : (P 0).testBit b0 = false) (t01 : (P 0).testBit b1 = false)
    (t10 : (P 1).testBit b0 = true) (t11 : (P 1).testBit b1 = false)
    (t20 : (P 2).testBit b0 = false) (t21 : (P 2).testBit b1 = true)
    (t30 : (P 3).testBit b0 = true) (t31 : (P 3).testBit b1 = true)
    (r0 : R.testBit (P 0) = true) (r1 : R.testBit (P 1) = true) (r2 : R.testBit (P 2) = true)
    (r3 : R.testBit (P 3) = true)
    (s0 : Benes.swp d M1 (P 0) = P 0) (s1 : Benes.swp d M1 (P 1) = P 2)
    (s2 : Benes.swp d M1 (P 2) = P 1) (s3 : Benes.swp d M1 (P 3) = P 3)
    (n0 : M0.testBit (P 0) = true) (n1 : M0.testBit (P 1) = false) (n2 : M0.testBit (P 2) = false)
    (n3 : M0.testBit (P 3) = false) :
    ∀ u < 4, resPN np S (dsw d (O.rep S M1) (O.bfly S b1 R (O.bfly S b0 R (O.neg S M0 x)))) (P u) =
      ∑ w ∈ Finset.range 4, ((c4z w u : ℤ) : ZMod (2 ^ np - 1)) * resPN np S x (P w) := by
  have y0b := hO.neg_bd hM0 hx
  have y1b := hO.bfly_bd hS hb0 hR y0b
  have y2b := hO.bfly_bd hS hb1 hR y1b
  have key : ∀ D0 D1 a0 a1 a2 a3 : ℕ, a1 = a0 + D0 → a2 = a0 + D1 → a3 = a0 + D0 + D1 → a3 < S →
      (a0 < S ∧ a1 < S ∧ a2 < S) ∧ (a1 - D0 = a0 ∧ a2 - D1 = a0 ∧ a3 - D1 = a1 ∧ a3 - D0 = a2) ∧
      (a0 + D0 = a1 ∧ a0 + D1 = a2 ∧ a1 + D1 = a3 ∧ a2 + D0 = a3) := by
    intros
    omega
  obtain ⟨⟨lt0, lt1, lt2⟩, ⟨q1, q2, q3, q3'⟩, ⟨q0, q0', q1', q2'⟩⟩ :=
    key (2 ^ b0) (2 ^ b1) (P 0) (P 1) (P 2) (P 3) e1 e2 e3 hP
  have z0 : ∀ u < 4, resPN np S (O.neg S M0 x) (P u) =
      if u = 0 then -resPN np S x (P u) else resPN np S x (P u) := by
    intro u hu
    rw [hO.neg_res hM0 hx (by interval_cases u <;> assumption)]
    interval_cases u <;> simp [n0, n1, n2, n3]
  have a0 := hO.bfly_res (x := O.neg S M0 x) hS hb0 hR hc0 y0b lt0
  have a1 := hO.bfly_res (x := O.neg S M0 x) hS hb0 hR hc0 y0b lt1
  have a2 := hO.bfly_res (x := O.neg S M0 x) hS hb0 hR hc0 y0b lt2
  have a3 := hO.bfly_res (x := O.neg S M0 x) hS hb0 hR hc0 y0b hP
  rw [r0, t00, q0] at a0
  rw [r1, t10, q1, r0] at a1
  rw [r2, t20, q2'] at a2
  rw [r3, t30, q3', r2] at a3
  simp only [Bool.not_eq_true', if_true, if_false, Bool.true_eq_false, reduceIte] at a0 a1 a2 a3
  have b0' := hO.bfly_res (x := O.bfly S b0 R (O.neg S M0 x)) hS hb1 hR hc1 y1b lt0
  have b1' := hO.bfly_res (x := O.bfly S b0 R (O.neg S M0 x)) hS hb1 hR hc1 y1b lt1
  have b2' := hO.bfly_res (x := O.bfly S b0 R (O.neg S M0 x)) hS hb1 hR hc1 y1b lt2
  have b3' := hO.bfly_res (x := O.bfly S b0 R (O.neg S M0 x)) hS hb1 hR hc1 y1b hP
  rw [r0, t01, q0'] at b0'
  rw [r1, t11, q1'] at b1'
  rw [r2, t21, q2, r0] at b2'
  rw [r3, t31, q3, r1] at b3'
  simp only [Bool.not_eq_true', if_true, if_false, Bool.true_eq_false, reduceIte] at b0' b1' b2' b3'
  have zz0 := z0 0 (by decide)
  have zz1 := z0 1 (by decide)
  have zz2 := z0 2 (by decide)
  have zz3 := z0 3 (by decide)
  simp only [if_true, if_false, reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero] at zz0 zz1 zz2 zz3
  intro u hu
  have hd : ∀ p < S, resPN np S (dsw d (O.rep S M1) (O.bfly S b1 R (O.bfly S b0 R (O.neg S M0 x)))) p =
      resPN np S (O.bfly S b1 R (O.bfly S b0 R (O.neg S M0 x))) (Benes.swp d M1 p) :=
    fun p hp => res_dsw_rep hO hv y2b hp
  interval_cases u
  · rw [hd _ lt0, s0, b0', a0, a2, zz0, zz1, zz2, zz3]
    simp [Finset.sum_range_succ, c4z, c4N]
    ring
  · rw [hd _ lt1, s1, b2', a0, a2, zz0, zz1, zz2, zz3]
    simp [Finset.sum_range_succ, c4z, c4N]
    ring
  · rw [hd _ lt2, s2, b1', a1, a3, zz0, zz1, zz2, zz3]
    simp [Finset.sum_range_succ, c4z, c4N]
    ring
  · rw [hd _ hP, s3, b3', a1, a3, zz0, zz1, zz2, zz3]
    simp [Finset.sum_range_succ, c4z, c4N]
    ring

theorem blk_out (hO : PLaw np O) {k S b0 b1 R d M0 M1 x p : ℕ} (hS : S = 2 ^ k) (hb0 : b0 < k)
    (hb1 : b1 < k) (hR : R < 2 ^ S) (hc0 : Cl S R b0) (hc1 : Cl S R b1) (hM0 : M0 < 2 ^ S)
    (hv : Benes.ValidIn S d M1) (hx : Bd np S x) (hp : p < S) (hr : R.testBit p = false)
    (hs : Benes.swp d M1 p = p) (hn : M0.testBit p = false) :
    resPN np S (dsw d (O.rep S M1) (O.bfly S b1 R (O.bfly S b0 R (O.neg S M0 x)))) p =
      resPN np S x p := by
  have y0b := hO.neg_bd hM0 hx
  have y1b := hO.bfly_bd hS hb0 hR y0b
  have y2b := hO.bfly_bd hS hb1 hR y1b
  rw [res_dsw_rep hO hv y2b hp, hs, hO.bfly_res hS hb1 hR hc1 y1b hp, hr, if_pos rfl,
    hO.bfly_res hS hb0 hR hc0 y0b hp, hr, if_pos rfl, hO.neg_res hM0 hx hp, hn]
  rfl

theorem colxi_bd (hO : PLaw np O) {k S b0 b1 R d M0 M1 x : ℕ} (hS : S = 2 ^ k) (hb0 : b0 < k)
    (hb1 : b1 < k) (hR : R < 2 ^ S) (hM0 : M0 < 2 ^ S) (hv : Benes.ValidIn S d M1)
    (hx : Bd np S x) :
    Bd np S (dsw d (O.rep S M1) (O.bfly S b1 R (O.bfly S b0 R (O.neg S M0 x)))) :=
  bd_dsw_rep hO hv (hO.bfly_bd hS hb1 hR (hO.bfly_bd hS hb0 hR (hO.neg_bd hM0 hx)))

@[expose] noncomputable def m0 (S b0 b1 R : ℕ) : ℕ := Nat.land R (Nat.land (clr S b0) (clr S b1))

@[expose] noncomputable def m1 (S b0 b1 R : ℕ) : ℕ := Nat.land R (Nat.land (idPlane S b0) (clr S b1))

theorem colxiG_eq (S b0 b1 R x : ℕ) : colxiG O S b0 b1 R x =
    dsw (2 ^ b1 - 2 ^ b0) (O.rep S (m1 S b0 b1 R))
      (O.bfly S b1 R (O.bfly S b0 R (O.neg S (m0 S b0 b1 R) x))) := by
  unfold colxiG m0 m1
  simp only [Benes.nsub, Benes.nshl, Nat.one_shiftLeft]

theorem tb_m0A {b0 b1 : ℕ} (h0 : b0 < 10) (h1 : b1 < 10) (p : ℕ) : (m0 SA b0 b1 valA).testBit p =
    decide ((p < 1024 ∧ p % 32 < 24 ∧ p / 32 < 24) ∧ (p < 1024 ∧ p / 2 ^ b0 % 2 = 0) ∧
      (p < 1024 ∧ p / 2 ^ b1 % 2 = 0)) := by
  change (valA &&& (clr SA b0 &&& clr SA b1)).testBit p = _
  rw [Nat.testBit_and, Nat.testBit_and, testBit_valA, testBit_clr_SA h0, testBit_clr_SA h1]
  simp only [Bool.decide_and]

theorem tb_m1A {b0 b1 : ℕ} (h0 : b0 < 10) (h1 : b1 < 10) (p : ℕ) : (m1 SA b0 b1 valA).testBit p =
    decide ((p < 1024 ∧ p % 32 < 24 ∧ p / 32 < 24) ∧ (p < 1024 ∧ p / 2 ^ b0 % 2 = 1) ∧
      (p < 1024 ∧ p / 2 ^ b1 % 2 = 0)) := by
  change (valA &&& (idPlane SA b0 &&& clr SA b1)).testBit p = _
  rw [Nat.testBit_and, Nat.testBit_and, testBit_valA, testBit_idPlane_SA h0, testBit_clr_SA h1]
  simp only [Bool.decide_and]

theorem tb_m0W {b0 b1 : ℕ} (h0 : b0 < 17) (h1 : b1 < 17) (p : ℕ) : (m0 SX b0 b1 valW).testBit p =
    decide ((p < 131072 ∧ p % 32 < 24) ∧ (p < 131072 ∧ p / 2 ^ b0 % 2 = 0) ∧
      (p < 131072 ∧ p / 2 ^ b1 % 2 = 0)) := by
  change (valW &&& (clr SX b0 &&& clr SX b1)).testBit p = _
  rw [Nat.testBit_and, Nat.testBit_and, testBit_valW, testBit_clr_SX h0, testBit_clr_SX h1]
  simp only [Bool.decide_and]

theorem tb_m1W {b0 b1 : ℕ} (h0 : b0 < 17) (h1 : b1 < 17) (p : ℕ) : (m1 SX b0 b1 valW).testBit p =
    decide ((p < 131072 ∧ p % 32 < 24) ∧ (p < 131072 ∧ p / 2 ^ b0 % 2 = 1) ∧
      (p < 131072 ∧ p / 2 ^ b1 % 2 = 0)) := by
  change (valW &&& (idPlane SX b0 &&& clr SX b1)).testBit p = _
  rw [Nat.testBit_and, Nat.testBit_and, testBit_valW, testBit_idPlane_SX h0, testBit_clr_SX h1]
  simp only [Bool.decide_and]

theorem m_lt_of {S x : ℕ} (h : ∀ p, x.testBit p = true → p < S) : x < 2 ^ S := lt_of_tb h

macro "barith" : tactic => `(tactic| ((try simp only [testBit_valA, testBit_valW,
  tb_m0A (by decide : (0 : ℕ) < 10) (by decide : (1 : ℕ) < 10),
  tb_m1A (by decide : (0 : ℕ) < 10) (by decide : (1 : ℕ) < 10),
  tb_m0A (by decide : (5 : ℕ) < 10) (by decide : (6 : ℕ) < 10),
  tb_m1A (by decide : (5 : ℕ) < 10) (by decide : (6 : ℕ) < 10),
  tb_m0W (by decide : (0 : ℕ) < 17) (by decide : (1 : ℕ) < 17),
  tb_m1W (by decide : (0 : ℕ) < 17) (by decide : (1 : ℕ) < 17)] at *) <;>
  (try simp only [tbd, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow, Nat.pow_zero,
    Nat.div_one, Nat.reduceSub, SA_1024, SX_131072, Bool.decide_eq_true] at *) <;> omega))

theorem swp_eq {d m p q : ℕ} (h1 : m.testBit p = true → p + d = q)
    (h2 : m.testBit p = false → d ≤ p ∧ m.testBit (p - d) = true → p - d = q)
    (h3 : m.testBit p = false → ¬ (d ≤ p ∧ m.testBit (p - d) = true) → p = q) :
    Benes.swp d m p = q := by
  unfold Benes.swp
  by_cases a : m.testBit p = true
  · rw [if_pos a]
    exact h1 a
  · rw [if_neg a]
    have a' : m.testBit p = false := by simpa using a
    by_cases b : d ≤ p ∧ m.testBit (p - d) = true
    · rw [if_pos b]
      exact h2 a' b
    · rw [if_neg b]
      exact h3 a' b

theorem clA0 : Cl SA valA 0 := by
  intro q hq h1 h2
  barith

theorem clA1 : Cl SA valA 1 := by
  intro q hq h1 h2
  barith

theorem clA5 : Cl SA valA 5 := by
  intro q hq h1 h2
  barith

theorem clA6 : Cl SA valA 6 := by
  intro q hq h1 h2
  barith

theorem clW0 : Cl SX valW 0 := by
  intro q hq h1 h2
  barith

theorem clW1 : Cl SX valW 1 := by
  intro q hq h1 h2
  barith

theorem vA01 : Benes.ValidIn SA (2 ^ 1 - 2 ^ 0) (m1 SA 0 1 valA) := by
  intro p hp
  constructor
  · barith
  · barith

theorem vA56 : Benes.ValidIn SA (2 ^ 6 - 2 ^ 5) (m1 SA 5 6 valA) := by
  intro p hp
  constructor
  · barith
  · barith

theorem vW01 : Benes.ValidIn SX (2 ^ 1 - 2 ^ 0) (m1 SX 0 1 valW) := by
  intro p hp
  constructor
  · barith
  · barith

theorem m0A01_lt : m0 SA 0 1 valA < 2 ^ SA := m_lt_of fun p h1 => by barith

theorem m0A56_lt : m0 SA 5 6 valA < 2 ^ SA := m_lt_of fun p h1 => by barith

theorem m0W01_lt : m0 SX 0 1 valW < 2 ^ SX := m_lt_of fun p h1 => by barith

theorem colA01 (hO : PLaw np O) {x : ℕ} (hx : Bd np SA x) {i J u : ℕ} (hi : i < 24) (hJ : J < 6)
    (hu : u < 4) :
    resPN np SA (colxiG O SA 0 1 valA x) (32 * i + 4 * J + u) =
      ∑ w ∈ Finset.range 4, ((c4z w u : ℤ) : ZMod (2 ^ np - 1)) *
        resPN np SA x (32 * i + 4 * J + w) := by
  rw [colxiG_eq]
  exact blk4 hO (k := 10) SA_eq (by decide) (by decide) valA_lt clA0 clA1 m0A01_lt vA01
    hx (fun u => 32 * i + 4 * J + u) (by simp) (by simp) (by simp) (by barith)
    (by barith) (by barith) (by barith) (by barith) (by barith) (by barith) (by barith) (by barith)
    (by barith) (by barith) (by barith) (by barith)
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (by barith) (by barith) (by barith) (by barith) u hu

theorem colA56 (hO : PLaw np O) {x : ℕ} (hx : Bd np SA x) {I j u : ℕ} (hI : I < 6) (hj : j < 24)
    (hu : u < 4) :
    resPN np SA (colxiG O SA 5 6 valA x) (32 * (4 * I + u) + j) =
      ∑ w ∈ Finset.range 4, ((c4z w u : ℤ) : ZMod (2 ^ np - 1)) *
        resPN np SA x (32 * (4 * I + w) + j) := by
  rw [colxiG_eq]
  exact blk4 hO (k := 10) SA_eq (by decide) (by decide) valA_lt clA5 clA6 m0A56_lt vA56
    hx (fun u => 32 * (4 * I + u) + j) (by simp <;> omega) (by simp <;> omega)
    (by simp <;> omega) (by barith)
    (by barith) (by barith) (by barith) (by barith) (by barith) (by barith) (by barith) (by barith)
    (by barith) (by barith) (by barith) (by barith)
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (by barith) (by barith) (by barith) (by barith) u hu

theorem colW01 (hO : PLaw np O) {x : ℕ} (hx : Bd np SX x) {r J u : ℕ} (hr : r < 4096) (hJ : J < 6)
    (hu : u < 4) :
    resPN np SX (colxiG O SX 0 1 valW x) (32 * r + 4 * J + u) =
      ∑ w ∈ Finset.range 4, ((c4z w u : ℤ) : ZMod (2 ^ np - 1)) *
        resPN np SX x (32 * r + 4 * J + w) := by
  rw [colxiG_eq]
  exact blk4 hO (k := 17) SX_eq (by decide) (by decide) valW_lt clW0 clW1 m0W01_lt vW01
    hx (fun u => 32 * r + 4 * J + u) (by simp) (by simp) (by simp) (by barith)
    (by barith) (by barith) (by barith) (by barith) (by barith) (by barith) (by barith) (by barith)
    (by barith) (by barith) (by barith) (by barith)
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (by barith) (by barith) (by barith) (by barith) u hu

theorem outA01 (hO : PLaw np O) {x p : ℕ} (hx : Bd np SA x) (hp : p < SA)
    (hr : valA.testBit p = false) : resPN np SA (colxiG O SA 0 1 valA x) p = resPN np SA x p := by
  rw [colxiG_eq]
  exact blk_out hO (k := 10) SA_eq (by decide) (by decide) valA_lt clA0 clA1 m0A01_lt vA01 hx hp hr
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith)) (by barith)

theorem outA56 (hO : PLaw np O) {x p : ℕ} (hx : Bd np SA x) (hp : p < SA)
    (hr : valA.testBit p = false) : resPN np SA (colxiG O SA 5 6 valA x) p = resPN np SA x p := by
  rw [colxiG_eq]
  exact blk_out hO (k := 10) SA_eq (by decide) (by decide) valA_lt clA5 clA6 m0A56_lt vA56 hx hp hr
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith)) (by barith)

theorem outW01 (hO : PLaw np O) {x p : ℕ} (hx : Bd np SX x) (hp : p < SX)
    (hr : valW.testBit p = false) : resPN np SX (colxiG O SX 0 1 valW x) p = resPN np SX x p := by
  rw [colxiG_eq]
  exact blk_out hO (k := 17) SX_eq (by decide) (by decide) valW_lt clW0 clW1 m0W01_lt vW01 hx hp hr
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith)) (by barith)

theorem colA_bd (hO : PLaw np O) {b0 b1 x : ℕ} (hb0 : b0 < 10) (hb1 : b1 < 10)
    (hv : Benes.ValidIn SA (2 ^ b1 - 2 ^ b0) (m1 SA b0 b1 valA)) (hm : m0 SA b0 b1 valA < 2 ^ SA)
    (hx : Bd np SA x) : Bd np SA (colxiG O SA b0 b1 valA x) := by
  rw [colxiG_eq]
  exact colxi_bd hO SA_eq hb0 hb1 valA_lt hm hv hx

theorem colW_bd (hO : PLaw np O) {x : ℕ} (hx : Bd np SX x) : Bd np SX (colxiG O SX 0 1 valW x) := by
  rw [colxiG_eq]
  exact colxi_bd hO SX_eq (by decide) (by decide) valW_lt m0W01_lt vW01 hx

theorem xiG_get {k i : ℕ} (hk : k < 24) (hi : i < 24) :
    (Native.xiG ())[k * 24 + i]! = if k / 4 = i / 4 then c4z (k % 4) (i % 4) else 0 := by
  unfold Native.xiG c4z
  rw [getElem!_pos (Array.ofFn _) (k * 24 + i) (by simp; omega), Array.getElem_ofFn]
  have e1 : (k * 24 + i) / 24 = k := by omega
  have e2 : (k * 24 + i) % 24 = i := by omega
  simp only [e1, e2]

theorem blk_sum {M : ℕ} (f : ℕ → ZMod M) {i : ℕ} (hi : i < 24) :
    ∑ k ∈ Finset.range 24, (((Native.xiG ())[k * 24 + i]! : ℤ) : ZMod M) * f k =
      ∑ w ∈ Finset.range 4, ((c4z w (i % 4) : ℤ) : ZMod M) * f (4 * (i / 4) + w) := by
  have e : ∀ k ∈ Finset.range 24, (((Native.xiG ())[k * 24 + i]! : ℤ) : ZMod M) * f k =
      if k / 4 = i / 4 then ((c4z (k % 4) (i % 4) : ℤ) : ZMod M) * f k else 0 := by
    intro k hk
    rw [xiG_get (Finset.mem_range.1 hk) hi]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl e, ← Finset.sum_filter]
  have hs : (Finset.range 24).filter (fun k => k / 4 = i / 4) =
      (Finset.range 4).image (fun w => 4 * (i / 4) + w) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · intro hk
      exact ⟨k % 4, by omega, by omega⟩
    · rintro ⟨w, hw, rfl⟩
      omega
  rw [hs, Finset.sum_image (fun a _ b _ hab => by omega)]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw' := Finset.mem_range.1 hw
  rw [show (4 * (i / 4) + w) % 4 = w by omega]

theorem aIdx_lt' {i j : ℕ} (hi : i < 24) (hj : j < 24) : Native.aIdx i j < 300 :=
  InitAux.aIdx_lt i hi j hj

theorem xi_resA_le {M : ℕ} {h : ZMod M} (h2 : 2 * h = 1) (v : Native.DVec) {i j : ℕ} (hi : i < 24)
    (hj : j < 24) (hij : i ≤ j) :
    resM h (Native.applyGen (Native.mkCtx ()) .xi v) (Native.aIdx i j) = h ^ 2 *
      ∑ w' ∈ Finset.range 4, ((c4z w' (i % 4) : ℤ) : ZMod M) * ∑ w ∈ Finset.range 4,
        ((c4z w (j % 4) : ℤ) : ZMod M) * resM h v (Native.aIdx (4 * (i / 4) + w') (4 * (j / 4) + w)) := by
  change resM h (Native.applyGD (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) .xi) v) _ = _
  rw [applyGD_resA h2 _ _ _ (aIdx_lt' hi hj), ListAux.aPos_aIdx i hi j hj, min_eq_left hij,
    max_eq_right hij]
  have hG : (Native.GD.ofGen (Native.mkCtx ()) .xi).G = Native.xiG () := by
    simp only [Native.GD.ofGen]
  have hl : (Native.GD.ofGen (Native.mkCtx ()) .xi).latS = 1 := by simp only [Native.GD.ofGen]
  rw [hG, hl]
  have e : ∀ k, ∑ l ∈ Finset.range 24, (((Native.xiG ())[k * 24 + i]! : ℤ) : ZMod M) *
      (((Native.xiG ())[l * 24 + j]! : ℤ) : ZMod M) * resM h v (Native.aIdx k l) =
      (((Native.xiG ())[k * 24 + i]! : ℤ) : ZMod M) * ∑ l ∈ Finset.range 24,
        (((Native.xiG ())[l * 24 + j]! : ℤ) : ZMod M) * resM h v (Native.aIdx k l) := by
    intro k
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [e]
  simp only [blk_sum _ hj]
  rw [blk_sum _ hi]

theorem sum4_comm {M : ℕ} (f : ℕ → ℕ → ZMod M) :
    ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4, f a b =
      ∑ b ∈ Finset.range 4, ∑ a ∈ Finset.range 4, f a b := Finset.sum_comm

theorem xi_resA {M : ℕ} {h : ZMod M} (h2 : 2 * h = 1) (v : Native.DVec) {i j : ℕ} (hi : i < 24)
    (hj : j < 24) :
    resM h (Native.applyGen (Native.mkCtx ()) .xi v) (Native.aIdx i j) = h ^ 2 *
      ∑ w' ∈ Finset.range 4, ((c4z w' (i % 4) : ℤ) : ZMod M) * ∑ w ∈ Finset.range 4,
        ((c4z w (j % 4) : ℤ) : ZMod M) * resM h v (Native.aIdx (4 * (i / 4) + w') (4 * (j / 4) + w)) := by
  rcases le_total i j with hij | hij
  · exact xi_resA_le h2 v hi hj hij
  · rw [ListAux.aIdx_comm i hi j hj, xi_resA_le h2 v hj hi hij]
    congr 1
    simp only [Finset.mul_sum]
    rw [sum4_comm]
    refine Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun w' hw' => ?_
    have := Finset.mem_range.1 hw
    have := Finset.mem_range.1 hw'
    rw [ListAux.aIdx_comm _ (by omega) _ (by omega)]
    ring

theorem xiG_resA (hO : PLaw np O) {A : ℕ} (hA : Bd np SA A) {i j : ℕ} (hi : i < 24) (hj : j < 24) :
    resPN np SA (O.half SA 2 (colxiG O SA 5 6 valA (colxiG O SA 0 1 valA A))) (32 * i + j) =
      hN np ^ 2 * ∑ w' ∈ Finset.range 4, ((c4z w' (i % 4) : ℤ) : ZMod (2 ^ np - 1)) *
        ∑ w ∈ Finset.range 4, ((c4z w (j % 4) : ℤ) : ZMod (2 ^ np - 1)) *
          resPN np SA A (32 * (4 * (i / 4) + w') + (4 * (j / 4) + w)) := by
  have hB := colA_bd hO (by decide) (by decide) vA01 m0A01_lt hA
  have hC := colA_bd hO (by decide) (by decide) vA56 m0A56_lt hB
  rw [hO.half_res (by decide) (by decide) hC (by rw [SA_1024]; omega)]
  congr 1
  have e : 32 * i + j = 32 * (4 * (i / 4) + i % 4) + j := by omega
  rw [e, colA56 hO hB (by omega) hj (Nat.mod_lt _ (by decide))]
  refine Finset.sum_congr rfl fun w' hw' => ?_
  have := Finset.mem_range.1 hw'
  congr 1
  have e2 : 32 * (4 * (i / 4) + w') + j = 32 * (4 * (i / 4) + w') + 4 * (j / 4) + j % 4 := by omega
  rw [e2, colA01 hO hA (by omega) (by omega) (Nat.mod_lt _ (by decide))]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Nat.add_assoc]

theorem xiG_resA_zero (hO : PLaw np O) {A : ℕ} (hA : Bd np SA A) {p : ℕ} (hp : p < SA)
    (hv : 24 ≤ p % 32 ∨ 24 ≤ p / 32) (hz : resPN np SA A p = 0) :
    resPN np SA (O.half SA 2 (colxiG O SA 5 6 valA (colxiG O SA 0 1 valA A))) p = 0 := by
  have hB := colA_bd hO (by decide) (by decide) vA01 m0A01_lt hA
  have hC := colA_bd hO (by decide) (by decide) vA56 m0A56_lt hB
  have hr : valA.testBit p = false := by
    rw [testBit_valA]
    simp only [decide_eq_false_iff_not]
    omega
  rw [hO.half_res (by decide) (by decide) hC hp, outA56 hO hB hp hr, outA01 hO hA hp hr, hz,
    mul_zero]

theorem xiG_bdA (hO : PLaw np O) {A : ℕ} (hA : Bd np SA A) :
    Bd np SA (O.half SA 2 (colxiG O SA 5 6 valA (colxiG O SA 0 1 valA A))) :=
  hO.half_bd (by decide) (by decide)
    (colA_bd hO (by decide) (by decide) vA56 m0A56_lt (colA_bd hO (by decide) (by decide) vA01 m0A01_lt hA))

theorem andB_and (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem xorSum_congr {f g : ℕ → Bool} : ∀ {n}, (∀ i < n, f i = g i) → xorSum f n = xorSum g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [xorSum]
    rw [xorSum_congr (fun i hi => h i (by omega)), h n (by omega)]

theorem xorSum_succ (f : ℕ → Bool) : ∀ k, xorSum f (k + 1) = (f 0 ^^ xorSum (fun i => f (i + 1)) k)
  | 0 => by simp [xorSum]
  | k + 1 => by rw [xorSum, xorSum_succ f k, xorSum, Bool.xor_assoc]

theorem parN_xorSum : ∀ k a, parN k a = xorSum a.testBit k
  | 0, _ => rfl
  | k + 1, a => by
    have ih := parN_xorSum k (a / 2)
    have hf : (fun i => a.testBit (i + 1)) = (a / 2).testBit := funext fun i => Nat.testBit_succ a i
    unfold parN at ih ⊢
    rw [xorSum_succ, hf, ← ih, popcN, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one (popcN k (a / 2)) with h' | h' <;>
      simp [Nat.add_mod, h, h']

theorem testBit_xorLoop (g : ℕ → ℕ) (p : ℕ) : ∀ n,
    (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (g i)) n).testBit p =
      xorSum (fun i => (g i).testBit p) n
  | 0 => by
    change Nat.testBit 0 p = _
    simp [xorSum]
  | n + 1 => by
    change (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (g i)) n ^^^ g n).testBit p = _
    rw [Nat.testBit_xor, testBit_xorLoop g p n]
    rfl

theorem xorLoop_lt (g : ℕ → ℕ) {S : ℕ} (hg : ∀ i, g i < 2 ^ S) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (g i)) n < 2 ^ S
  | 0 => Nat.two_pow_pos S
  | n + 1 => Nat.xor_lt_two_pow (xorLoop_lt g hg n) (hg n)

theorem testBit_plane' {S b x p : ℕ} (hp : p < S) :
    (plane S b x).testBit p = x.testBit (b * S + p) := by
  change ((x >>> (b * S)) &&& ones S).testBit p = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones, decide_eq_true hp, Bool.and_true]

theorem plane_lt' (S b x : ℕ) : plane S b x < 2 ^ S := by
  change (x >>> (b * S)) &&& ones S < 2 ^ S
  rw [Benes.ones_eq]
  exact Benes.land_ones_lt _ _

theorem testBit_packN' (f : ℕ → Bool) :
    ∀ n j, (packN f n).testBit j = (decide (j < n) && f j)
  | 0, j => by simp [packN]
  | n + 1, j => by
    rw [packN, Nat.testBit_or, testBit_packN' f n]
    by_cases hj : j = n
    · subst hj
      cases f j <;> simp
    · have hj' : (decide (j < n + 1)) = decide (j < n) := by
        rcases Nat.lt_or_ge j n with h | h
        · simp [h, Nat.lt_succ_of_lt h]
        · have : n < j := lt_of_le_of_ne h (Ne.symm hj)
          simp [Nat.not_lt.2 h, Nat.not_lt.2 (Nat.succ_le_of_lt this)]
      rw [hj']
      split_ifs <;> simp [Ne.symm hj]

theorem packN_lt' (f : ℕ → Bool) (n : ℕ) : packN f n < 2 ^ n :=
  lt_of_tb fun i hi => by
    rw [testBit_packN'] at hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    exact hi.1

theorem idx_mod' {S b p : ℕ} (hp : p < S) : (b * S + p) % S = p := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]

@[expose] noncomputable def kv (K P : ℕ) : ℕ := packN (fun b => K.testBit (b * SX + P)) 12

@[expose] def At (Y P y : ℕ) : Prop := ∀ b < 12, Y.testBit (b * SX + P) = y.testBit b

theorem kv_lt (K P : ℕ) : kv K P < 4096 := packN_lt' _ 12

theorem at_kv (K P : ℕ) : At K P (kv K P) := fun b hb => by
  rw [kv, testBit_packN', decide_eq_true hb, Bool.true_and]

theorem kv_eq {K P y : ℕ} (h : At K P y) (hy : y < 4096) : kv K P = y := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 12
  · rw [← h b hb, at_kv K P b hb]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (kv_lt K P) (Nat.pow_le_pow_right (n := 2)
      (by decide) (by omega : 12 ≤ b))), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy
      (Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 12 ≤ b)))]

theorem at_xor {x y P a c : ℕ} (h1 : At x P a) (h2 : At y P c) : At (Nat.xor x y) P (a ^^^ c) :=
  fun b hb => by
    change (x ^^^ y).testBit _ = _
    rw [Nat.testBit_xor, Nat.testBit_xor, h1 b hb, h2 b hb]

theorem at_or {x y P a c : ℕ} (h1 : At x P a) (h2 : At y P c) : At (Nat.lor x y) P (a ||| c) :=
  fun b hb => by
    change (x ||| y).testBit _ = _
    rw [Nat.testBit_or, Nat.testBit_or, h1 b hb, h2 b hb]

theorem at_and {x y P a c : ℕ} (h1 : At x P a) (h2 : At y P c) : At (Nat.land x y) P (a &&& c) :=
  fun b hb => by
    change (x &&& y).testBit _ = _
    rw [Nat.testBit_and, Nat.testBit_and, h1 b hb, h2 b hb]

theorem lt_planes {b P n : ℕ} (hP : P < SX) : decide (b * SX + P < SX * n) = decide (b < n) := by
  rw [SX_131072]
  by_cases h : b < n
  · rw [decide_eq_true h, decide_eq_true]
    have : (b + 1) * 131072 ≤ n * 131072 := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this
    rw [SX_131072] at hP
    rw [Nat.mul_comm 131072 n]
    omega
  · rw [decide_eq_false h, decide_eq_false]
    have : n * 131072 ≤ b * 131072 := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.mul_comm 131072 n]
    omega

theorem t4032 : ∀ b < 12, (4032 : ℕ).testBit b = (decide (b < 12) ^^ decide (b < 6)) := by decide

theorem at_hi {P : ℕ} (hP : P < SX) : At (Nat.xor (onesP SX 12) (onesP SX 6)) P 4032 := fun b hb => by
  change (ones (SX * 12) ^^^ ones (SX * 6)).testBit _ = _
  rw [Nat.testBit_xor, testBit_ones, testBit_ones, lt_planes hP, lt_planes hP, t4032 b hb]

theorem testBit_63 (b : ℕ) : (63 : ℕ).testBit b = decide (b < 6) := by
  rw [(by rfl : (63 : ℕ) = 2 ^ 6 - 1), Nat.testBit_two_pow_sub_one]

theorem gammaLowN_testBit (y b : ℕ) :
    (gammaLowN y).testBit b = (decide (b < 6) && (y.testBit b ^^ parN 6 y)) := by
  unfold gammaLowN
  rw [Nat.testBit_xor, (by rfl : (64 : ℕ) = 2 ^ 6), Nat.testBit_mod_two_pow]
  cases parN 6 y
  · simp
  · simp only [ite_true, testBit_63]
    cases decide (b < 6) <;> simp

theorem parN6_mod (y : ℕ) : parN 6 (y % 64) = parN 6 y := by
  rw [parN_xorSum, parN_xorSum]
  exact xorSum_congr fun i hi => by
    rw [(by rfl : (64 : ℕ) = 2 ^ 6), Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]

theorem gammaLowN_mod (y : ℕ) : gammaLowN (y % 64) = gammaLowN y := by
  unfold gammaLowN
  rw [Nat.mod_mod, parN6_mod]

theorem gammaLowN_lt (y : ℕ) : gammaLowN y < 64 := by
  unfold gammaLowN
  have h1 : y % 64 < 2 ^ 6 := Nat.mod_lt _ (by decide)
  have h2 : (if parN 6 y = true then 63 else 0) < 2 ^ 6 := by split_ifs <;> decide
  exact Nat.xor_lt_two_pow h1 h2

theorem testBit_repP {S m : ℕ} (hm : m < 2 ^ S) (n q : ℕ) :
    (repP S n m).testBit q = (decide (q < S * n) && m.testBit (q % S)) :=
  Benes.rep_repP (fun p hp => by
    by_contra h
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide)
      (by omega)))] at hp
    exact Bool.false_ne_true hp) n q

theorem at_gam6 {K P y : ℕ} (hP : P < SX) (h : At K P y) : At (gam6 SX K) P (gammaLowN y) := by
  intro b hb
  have hm : Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (plane SX i K)) 6 < 2 ^ SX :=
    xorLoop_lt _ (fun i => plane_lt' SX i K) 6
  change ((K &&& ones (6 * SX)) ^^^ repP SX 6 (Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.xor acc (plane SX i K)) 6)).testBit (b * SX + P) = _
  rw [Nat.testBit_xor, Nat.testBit_and, testBit_ones, testBit_repP hm, idx_mod' hP,
    testBit_xorLoop, Nat.mul_comm 6 SX, lt_planes hP, gammaLowN_testBit, h b hb, parN_xorSum]
  have e : xorSum (fun i => (plane SX i K).testBit P) 6 = xorSum y.testBit 6 :=
    xorSum_congr fun i hi => by rw [testBit_plane' hP, h i (by omega)]
  rw [e]
  cases decide (b < 6) <;> cases y.testBit b <;> cases xorSum y.testBit 6 <;> rfl

@[expose] def xs (a d : ℕ) : Bool :=
  qGN (gammaLowN (d % 64)) ^^ pairN (gammaLowN (d % 64)) (gammaLowN (a % 64))

@[expose] def xa (a d : ℕ) : ℕ := gammaLowN (d % 64) ^^^ (a &&& 4032)

@[expose] def xd (a d : ℕ) : ℕ := gammaLowN (a % 64) ^^^ gammaLowN (gammaLowN (d % 64)) ^^^ (d &&& 4032)

theorem t4032' (b : ℕ) : (4032 : ℕ).testBit b = decide (6 ≤ b ∧ b < 12) := by
  by_cases hb : b < 12
  · rw [t4032 b hb]
    by_cases h6 : b < 6 <;> simp [h6, hb] <;> omega
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : (4032 : ℕ) < 2 ^ 12)
      (Nat.pow_le_pow_right (by decide) (by omega)))]
    simp [hb]

theorem xa_eq (a y : ℕ) : gammaLowN y ||| (a &&& 4032) = xa a y := by
  unfold xa
  rw [gammaLowN_mod]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, gammaLowN_testBit, t4032']
  by_cases h6 : b < 6
  · simp [h6, show ¬ 6 ≤ b by omega]
  · simp [h6, show 6 ≤ b by omega]

theorem xd_eq (a y : ℕ) :
    (gammaLowN a ^^^ gammaLowN (gammaLowN y)) ||| (y &&& 4032) = xd a y := by
  unfold xd
  rw [gammaLowN_mod, gammaLowN_mod]
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, gammaLowN_testBit, t4032']
  by_cases h6 : b < 6
  · simp [h6, show ¬ 6 ≤ b by omega]
  · simp [h6, show 6 ≤ b by omega]

theorem and4032_lt (a : ℕ) : a &&& 4032 < 2 ^ 12 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem gam_lt12 (y : ℕ) : gammaLowN y < 2 ^ 12 :=
  Nat.lt_of_lt_of_le (gammaLowN_lt y) (by decide)

theorem xa_lt (a d : ℕ) : xa a d < 4096 := Nat.xor_lt_two_pow (gam_lt12 _) (and4032_lt a)

theorem xd_lt (a d : ℕ) : xd a d < 4096 :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (gam_lt12 _) (gam_lt12 _)) (and4032_lt d)

theorem qGN_e2 : ∀ ν < 64,
    qGN ν = xorSum (fun i => ν.testBit i && xorSum (fun j => decide (i < j) && ν.testBit j) 6) 6 := by
  decide

theorem pairN_low : ∀ x < 64, ∀ y < 64, pairN x y = xorSum (fun i => x.testBit i && y.testBit i) 6 := by
  decide +kernel

theorem testBit_selB_blt (i j m p : ℕ) :
    (selB (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.blt i j)) m).testBit p = (decide (i < j) && m.testBit p) := by
  have e : Nat.blt i j = decide (i < j) := by
    cases h : Nat.blt i j
    · symm
      rw [decide_eq_false_iff_not]
      intro h'
      rw [← Nat.blt_eq] at h'
      rw [h'] at h
      exact Bool.noConfusion h
    · symm
      rw [decide_eq_true_eq, ← Nat.blt_eq]
      exact h
  rw [e]
  cases decide (i < j)
  · change (0 * m).testBit p = _
    simp
  · change (1 * m).testBit p = _
    simp

theorem testBit_e2six {X P : ℕ} (hP : P < SX) : (e2six SX X).testBit P =
    xorSum (fun i => X.testBit (i * SX + P) &&
      xorSum (fun j => decide (i < j) && X.testBit (j * SX + P)) 6) 6 := by
  refine (testBit_xorLoop (fun i => Nat.land (plane SX i X) (Nat.rec (motive := fun _ => ℕ) 0
    (fun j acc2 => Nat.xor acc2 (selB (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.blt i j))
      (plane SX j X))) 6)) P 6).trans ?_
  refine xorSum_congr fun i _ => ?_
  change (plane SX i X &&& _).testBit P = _
  rw [Nat.testBit_and, testBit_plane' hP, testBit_xorLoop]
  congr 1
  exact xorSum_congr fun j _ => by rw [testBit_selB_blt, testBit_plane' hP]

theorem testBit_pairLoop {X Y P : ℕ} (hP : P < SX) :
    (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (Nat.land (plane SX i X)
      (plane SX i Y))) 6).testBit P =
      xorSum (fun i => X.testBit (i * SX + P) && Y.testBit (i * SX + P)) 6 := by
  rw [testBit_xorLoop]
  refine xorSum_congr fun i _ => ?_
  change (plane SX i X &&& plane SX i Y).testBit P = _
  rw [Nat.testBit_and, testBit_plane' hP, testBit_plane' hP]

theorem tb_split {A D : ℕ} (hA : A < 2 ^ (12 * SX)) (q : ℕ) :
    (Nat.lor A (Nat.shiftLeft D (Nat.mul 12 SX))).testBit q =
      if q < 12 * SX then A.testBit q else D.testBit (q - 12 * SX) := by
  change (A ||| D <<< (12 * SX)).testBit q = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  split_ifs with h
  · rw [decide_eq_false (by omega)]
    simp
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide)
      (by omega))), decide_eq_true (by omega)]
    simp

theorem ones_lt (n : ℕ) : ones n < 2 ^ n := by
  rw [Benes.ones_eq]
  exact Nat.sub_lt (Nat.two_pow_pos n) (by decide)

theorem gam6_lt (K : ℕ) : gam6 SX K < 2 ^ (12 * SX) := by
  have hm : Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (plane SX i K)) 6 < 2 ^ SX :=
    xorLoop_lt _ (fun i => plane_lt' SX i K) 6
  change (K &&& ones (6 * SX)) ^^^ repP SX 6 (Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.xor acc (plane SX i K)) 6) < _
  refine Nat.xor_lt_two_pow ?_ ?_
  · exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.lt_of_lt_of_le (ones_lt _)
      (Nat.pow_le_pow_right (by decide) (by omega)))
  · refine lt_of_tb fun i hi => ?_
    rw [testBit_repP hm] at hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    omega

theorem hi_lt : Nat.xor (onesP SX 12) (onesP SX 6) < 2 ^ (12 * SX) := by
  change ones (SX * 12) ^^^ ones (SX * 6) < _
  refine Nat.xor_lt_two_pow ?_ ?_
  · rw [Nat.mul_comm]
    exact ones_lt _
  · exact Nat.lt_of_lt_of_le (ones_lt _) (Nat.pow_le_pow_right (by decide) (by omega))

theorem xiOK_split {F : Fix} (hx : xiOK F = true) : netOK 17 F.xiNet = true ∧
    netP SX 17 24 F.xiNet
        (Nat.lor (Nat.lor (gam6 SX F.keyD) (Nat.land F.keyA (Nat.xor (onesP SX 12) (onesP SX 6))))
          (Nat.shiftLeft (Nat.lor (Nat.xor (gam6 SX F.keyA) (gam6 SX (gam6 SX F.keyD)))
            (Nat.land F.keyD (Nat.xor (onesP SX 12) (onesP SX 6)))) (Nat.mul 12 SX))) =
      Nat.lor F.keyA (Nat.shiftLeft F.keyD (Nat.mul 12 SX)) ∧
    F.xiSgn = Nat.xor (e2six SX (gam6 SX F.keyD))
        (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (Nat.land (plane SX i (gam6 SX F.keyD))
          (plane SX i (gam6 SX F.keyA)))) 6) := by
  have hx' : andB (netOK 17 F.xiNet) (andB
      (Nat.beq (netP SX 17 24 F.xiNet
        (Nat.lor (Nat.lor (gam6 SX F.keyD) (Nat.land F.keyA (Nat.xor (onesP SX 12) (onesP SX 6))))
          (Nat.shiftLeft (Nat.lor (Nat.xor (gam6 SX F.keyA) (gam6 SX (gam6 SX F.keyD)))
            (Nat.land F.keyD (Nat.xor (onesP SX 12) (onesP SX 6)))) (Nat.mul 12 SX))))
        (Nat.lor F.keyA (Nat.shiftLeft F.keyD (Nat.mul 12 SX))))
      (Nat.beq F.xiSgn (Nat.xor (e2six SX (gam6 SX F.keyD))
        (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (Nat.land (plane SX i (gam6 SX F.keyD))
          (plane SX i (gam6 SX F.keyA)))) 6)))) = true := hx
  simp only [andB_and, Bool.and_eq_true, Nat.beq_eq] at hx'
  exact hx'

theorem xiSgn_lt {F : Fix} (hx : xiOK F = true) : F.xiSgn < 2 ^ SX := by
  rw [(xiOK_split hx).2.2]
  refine Nat.xor_lt_two_pow ?_ ?_
  · exact xorLoop_lt (fun i => Nat.land (plane SX i (gam6 SX F.keyD)) (Nat.rec (motive := fun _ => ℕ) 0
      (fun j acc2 => Nat.xor acc2 (selB (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.blt i j))
        (plane SX j (gam6 SX F.keyD)))) 6))
      (fun i => Nat.lt_of_le_of_lt Nat.and_le_left (plane_lt' _ _ _)) 6
  · exact xorLoop_lt (fun i => Nat.land (plane SX i (gam6 SX F.keyD)) (plane SX i (gam6 SX F.keyA)))
      (fun i => Nat.lt_of_le_of_lt Nat.and_le_left (plane_lt' _ _ _)) 6

theorem xi_lab {F : Fix} (hx : xiOK F = true) (hla : F.keyA < 2 ^ (12 * SX)) {r : ℕ} (hr : r < SX) :
    Benes.benesPerm 17 F.xiNet r < SX ∧
    kv F.keyA r = xa (kv F.keyA (Benes.benesPerm 17 F.xiNet r)) (kv F.keyD (Benes.benesPerm 17 F.xiNet r)) ∧
    kv F.keyD r = xd (kv F.keyA (Benes.benesPerm 17 F.xiNet r)) (kv F.keyD (Benes.benesPerm 17 F.xiNet r)) ∧
    F.xiSgn.testBit r = xs (kv F.keyA r) (kv F.keyD r) := by
  have hx' : andB (netOK 17 F.xiNet) (andB
      (Nat.beq (netP SX 17 24 F.xiNet
        (Nat.lor (Nat.lor (gam6 SX F.keyD) (Nat.land F.keyA (Nat.xor (onesP SX 12) (onesP SX 6))))
          (Nat.shiftLeft (Nat.lor (Nat.xor (gam6 SX F.keyA) (gam6 SX (gam6 SX F.keyD)))
            (Nat.land F.keyD (Nat.xor (onesP SX 12) (onesP SX 6)))) (Nat.mul 12 SX))))
        (Nat.lor F.keyA (Nat.shiftLeft F.keyD (Nat.mul 12 SX))))
      (Nat.beq F.xiSgn (Nat.xor (e2six SX (gam6 SX F.keyD))
        (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (Nat.land (plane SX i (gam6 SX F.keyD))
          (plane SX i (gam6 SX F.keyA)))) 6)))) = true := hx
  simp only [andB_and, Bool.and_eq_true, Nat.beq_eq] at hx'
  obtain ⟨hn, hl, hs⟩ := hx'
  have hv := Benes.stagesValid_of_netOK hn
  have hπ : Benes.benesPerm 17 F.xiNet r < SX := Benes.benesPerm_lt hv hr
  set π := Benes.benesPerm 17 F.xiNet r with hπdef
  have hAl : Nat.lor (gam6 SX F.keyD) (Nat.land F.keyA (Nat.xor (onesP SX 12) (onesP SX 6))) <
      2 ^ (12 * SX) := Nat.or_lt_two_pow (gam6_lt _) (Nat.lt_of_le_of_lt Nat.and_le_right hi_lt)
  have hN := (Benes.testBit_netP (n := 24) SX_eq hn (Nat.lor (Nat.lor (gam6 SX F.keyD)
    (Nat.land F.keyA (Nat.xor (onesP SX 12) (onesP SX 6)))) (Nat.shiftLeft (Nat.lor
      (Nat.xor (gam6 SX F.keyA) (gam6 SX (gam6 SX F.keyD))) (Nat.land F.keyD
        (Nat.xor (onesP SX 12) (onesP SX 6)))) (Nat.mul 12 SX)))).1
  rw [hl] at hN
  have kA : At (Nat.lor (gam6 SX F.keyD) (Nat.land F.keyA (Nat.xor (onesP SX 12) (onesP SX 6)))) π
      (gammaLowN (kv F.keyD π) ||| (kv F.keyA π &&& 4032)) :=
    at_or (at_gam6 hπ (at_kv _ _)) (at_and (at_kv _ _) (at_hi hπ))
  have kD : At (Nat.lor (Nat.xor (gam6 SX F.keyA) (gam6 SX (gam6 SX F.keyD))) (Nat.land F.keyD
        (Nat.xor (onesP SX 12) (onesP SX 6)))) π
      ((gammaLowN (kv F.keyA π) ^^^ gammaLowN (gammaLowN (kv F.keyD π))) ||| (kv F.keyD π &&& 4032)) :=
    at_or (at_xor (at_gam6 hπ (at_kv _ _)) (at_gam6 hπ (at_gam6 hπ (at_kv _ _))))
      (at_and (at_kv _ _) (at_hi hπ))
  rw [xa_eq] at kA
  rw [xd_eq] at kD
  have hSX : SX = 131072 := rfl
  refine ⟨hπ, kv_eq (fun b hb => ?_) (xa_lt _ _), kv_eq (fun b hb => ?_) (xd_lt _ _), ?_⟩
  · have e1 := hN b (by omega) r hr
    rw [tb_split hla, if_pos (by rw [hSX] at hr ⊢; omega), tb_split hAl,
      if_pos (by rw [hSX] at hπ ⊢; omega)] at e1
    rw [Nat.mul_comm b SX, e1, Nat.mul_comm SX b]
    exact kA b hb
  · have e1 := hN (12 + b) (by omega) r hr
    rw [tb_split hla, if_neg (by rw [hSX] at hr ⊢; omega), tb_split hAl,
      if_neg (by rw [hSX] at hπ ⊢; omega)] at e1
    have q1 : SX * (12 + b) + r - 12 * SX = b * SX + r := by rw [hSX]; omega
    have q2 : SX * (12 + b) + π - 12 * SX = b * SX + π := by rw [hSX]; omega
    rw [q1, q2] at e1
    rw [e1]
    exact kD b hb
  · rw [hs]
    change (e2six SX (gam6 SX F.keyD) ^^^ _).testBit r = _
    rw [Nat.testBit_xor, testBit_e2six hr, testBit_pairLoop hr]
    have g1 := at_gam6 hr (at_kv F.keyD r)
    have g2 := at_gam6 hr (at_kv F.keyA r)
    unfold xs
    rw [gammaLowN_mod, gammaLowN_mod, qGN_e2 _ (gammaLowN_lt _),
      pairN_low _ (gammaLowN_lt _) _ (gammaLowN_lt _)]
    congr 1
    · refine xorSum_congr fun i hi => ?_
      rw [g1 i (by omega)]
      congr 1
      exact xorSum_congr fun j hj => by rw [g1 j (by omega)]
    · exact xorSum_congr fun i hi => by rw [g1 i (by omega), g2 i (by omega)]

theorem xi_X (hO : PLaw np O) (hnp : 2 ≤ np) {F : Fix} (hK : KeyBind F) (hG : KeysGood)
    (hx : xiOK F = true) {v : Native.DVec} {X : ℕ}
    (hX1 : ∀ q < 98280, resPN np SX X (xposK q) = resN np v (300 + q))
    (hX2 : ∀ p < SX, (∀ q < 98280, xposK q ≠ p) → resPN np SX X p = 0) (hX3 : X < 2 ^ (np * SX)) :
    (∀ q < 98280, resPN np SX (O.net SX 17 F.xiNet (O.neg SX F.xiSgn X)) (xposK q) =
      resN np (Native.applyGen (Native.mkCtx ()) .xi v) (300 + q)) ∧
    (∀ p < SX, (∀ q < 98280, xposK q ≠ p) →
      resPN np SX (O.net SX 17 F.xiNet (O.neg SX F.xiSgn X)) p = 0) ∧
    O.net SX 17 F.xiNet (O.neg SX F.xiSgn X) < 2 ^ (np * SX) := by
  have hn := (xiOK_split hx).1
  have hv := Benes.stagesValid_of_netOK hn
  have hsl := xiSgn_lt hx
  have hNb : Bd np SX (O.neg SX F.xiSgn X) := hO.neg_bd hsl hX3
  have lab := fun {r : ℕ} (hr : r < SX) => xi_lab hx hK.la hr
  have key : ∀ q < 98280, kv F.keyA (xposK q) = (keyQ q).1 ∧ kv F.keyD (xposK q) = (keyQ q).2 :=
    fun q hq => ⟨kv_eq (hK.ka q hq) (hG.1 q hq).1, kv_eq (hK.kd q hq) (hG.1 q hq).2⟩
  have pad : ∀ P < SX, (∀ q < 98280, xposK q ≠ P) → kv F.keyA P = 0 ∧ kv F.keyD P = 0 :=
    fun P hP hq => ⟨kv_eq (fun b hb => by rw [hK.pa P hP hq b hb, Nat.zero_testBit]) (by decide),
      kv_eq (fun b hb => by rw [hK.pd P hP hq b hb, Nat.zero_testBit]) (by decide)⟩
  have x00 : xa 0 0 = 0 ∧ xd 0 0 = 0 := by decide
  have ex_pre : ∀ q, ∃ p, q < 98280 → p < 98280 ∧
      xposK p = Benes.benesPerm 17 F.xiNet (xposK q) := by
    intro q
    by_cases hq : q < 98280
    · have hP := InitAux.xposK_lt' hq
      obtain ⟨hπ, e1, e2, -⟩ := lab hP
      by_cases hex : ∃ p < 98280, xposK p = Benes.benesPerm 17 F.xiNet (xposK q)
      · obtain ⟨p, hp, e⟩ := hex
        exact ⟨p, fun _ => ⟨hp, e⟩⟩
      · exfalso
        obtain ⟨z1, z2⟩ := pad _ hπ fun p hp e => hex ⟨p, hp, e⟩
        rw [z1, z2, x00.1, (key q hq).1] at e1
        rw [z1, z2, x00.2, (key q hq).2] at e2
        exact keyQ_ne_zero hq (Prod.ext e1 e2)
    · exact ⟨0, fun h => absurd h hq⟩
  choose pre hpre using ex_pre
  have img_pre : ∀ q < 98280, xa (keyQ (pre q)).1 (keyQ (pre q)).2 = (keyQ q).1 ∧
      xd (keyQ (pre q)).1 (keyQ (pre q)).2 = (keyQ q).2 := by
    intro q hq
    obtain ⟨hp, e⟩ := hpre q hq
    obtain ⟨-, e1, e2, -⟩ := lab (InitAux.xposK_lt' hq)
    rw [← e, (key _ hp).1, (key _ hp).2, (key q hq).1] at e1
    rw [← e, (key _ hp).1, (key _ hp).2, (key q hq).2] at e2
    exact ⟨e1.symm, e2.symm⟩
  have pre_inj : ∀ q < 98280, ∀ q' < 98280, pre q = pre q' → q = q' := by
    intro q hq q' hq' e
    have e1 := (hpre q hq).2
    have e2 := (hpre q' hq').2
    rw [e] at e1
    rw [e1] at e2
    have := congrArg (Benes.benesInv 17 F.xiNet) e2
    rw [Benes.benesInv_benesPerm hv, Benes.benesInv_benesPerm hv] at this
    exact InitAux.xposK_inj hq hq' this
  have surj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range 98280) (t := Finset.range 98280)
    (fun q _ => pre q) (fun q hq => Finset.mem_range.2 (hpre q (Finset.mem_range.1 hq)).1)
    (fun a b ha hb e => pre_inj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) e) le_rfl
  have ex_post : ∀ p, ∃ q, p < 98280 → q < 98280 ∧ pre q = p := by
    intro p
    by_cases hp : p < 98280
    · obtain ⟨q, hq, e⟩ := surj p (Finset.mem_range.2 hp)
      exact ⟨q, fun _ => ⟨Finset.mem_range.1 hq, e.symm⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose post hpost using ex_post
  have img_post : ∀ p < 98280, xa (keyQ p).1 (keyQ p).2 = (keyQ (post p)).1 ∧
      xd (keyQ p).1 (keyQ p).2 = (keyQ (post p)).2 := by
    intro p hp
    have := img_pre (post p) (hpost p hp).1
    rw [(hpost p hp).2] at this
    exact this
  have post_inj : ∀ p < 98280, ∀ p' < 98280, post p = post p' → p = p' := by
    intro p hp p' hp' e
    rw [← (hpost p hp).2, ← (hpost p' hp').2, e]
  have post_pre : ∀ q < 98280, post (pre q) = q := by
    intro q hq
    have hp := (hpre q hq).1
    exact pre_inj _ (hpost _ hp).1 _ hq (hpost _ hp).2
  have hxT : ∀ p < 98280, Native.GD.xT (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) .xi) p =
      [(post p, sgnI (xs (keyQ p).1 (keyQ p).2))] := by
    intro p hp
    have hb := hG.1 p hp
    have e : Native.fastAct (Native.tabT conjXiN) (Native.tabD conjXiN) (false, (keyQ p).1, (keyQ p).2) =
        (xs (keyQ p).1 (keyQ p).2, xa (keyQ p).1 (keyQ p).2, xd (keyQ p).1 (keyQ p).2) :=
      fastAct_xi hb.1 hb.2
    unfold Native.GD.xT
    simp only [Native.GD.ofGen]
    rw [mkCtx_keys hp, e]
    dsimp only
    rw [(img_post p hp).1, (img_post p hp).2, mkCtx_find hG (hpost p hp).1]
  have hnat : ∀ q < 98280, resN np (Native.applyGen (Native.mkCtx ()) .xi v) (300 + q) =
      ((sgnI (xs (keyQ (pre q)).1 (keyQ (pre q)).2) : ℤ) : ZMod (2 ^ np - 1)) *
        resN np v (300 + pre q) := by
    intro q hq
    change resM (hN np) (Native.applyGD (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) .xi) v)
      (300 + q) = _
    rw [applyGD_resX (two_hN (by omega)) _ _ _ hq, sum_scat_single hxT post_inj]
    have hex : ∃ p < 98280, post p = q := ⟨pre q, (hpre q hq).1, post_pre q hq⟩
    rw [dite_eq_left hex]
    have hc : hex.choose = pre q :=
      post_inj _ hex.choose_spec.1 _ (hpre q hq).1 (by rw [hex.choose_spec.2, post_pre q hq])
    rw [hc]
    rfl
  refine ⟨fun q hq => ?_, fun P hP hq => ?_, hO.net_bd SX_eq hn hNb⟩
  · have hP := InitAux.xposK_lt' hq
    obtain ⟨hp, e⟩ := hpre q hq
    rw [hO.net_res SX_eq hn hNb hP, ← e, hO.neg_res hsl hX3 (InitAux.xposK_lt' hp),
      (lab (InitAux.xposK_lt' hp)).2.2.2, (key _ hp).1, (key _ hp).2, hX1 _ hp, hnat q hq, sgnI_mul]
  · obtain ⟨hπ, e1, e2, -⟩ := lab hP
    have hno : ∀ p < 98280, xposK p ≠ Benes.benesPerm 17 F.xiNet P := by
      intro p hp e
      obtain ⟨z1, z2⟩ := pad P hP hq
      rw [← e, (key _ hp).1, (key _ hp).2, (img_post p hp).1, z1] at e1
      rw [← e, (key _ hp).1, (key _ hp).2, (img_post p hp).2, z2] at e2
      exact keyQ_ne_zero (hpost p hp).1 (Prod.ext e1.symm e2.symm)
    rw [hO.net_res SX_eq hn hNb hP, hO.neg_res hsl hX3 hπ, hX2 _ hπ hno]
    simp

@[expose] def pos (H j k : ℕ) : ℕ := 32 * (2048 * (k / 32) + 32 * H + k % 32) + j

@[expose] def rr (H k : ℕ) : ℕ := 2048 * (k / 32) + 32 * H + k % 32

@[expose] def par4 (k : ℕ) : Bool := (k.testBit 0 ^^ k.testBit 1) ^^ (k.testBit 2 ^^ k.testBit 3)

@[expose] def e2B (a b c d : Bool) : Bool :=
  ((a && b) ^^ (a && c)) ^^ ((a && d) ^^ (b && c)) ^^ ((b && d) ^^ (c && d))

@[expose] def negIn (k : ℕ) : Bool := !(k.testBit 5 && k.testBit 4)

@[expose] def negOut (k : ℕ) : Bool :=
  e2B (k.testBit 0) (k.testBit 1) (k.testBit 2) (k.testBit 3) ^^ (k.testBit 5 && k.testBit 4)

@[expose] def pin (k : ℕ) : ℕ := if par4 k then k ^^^ 16 else k

@[expose] def linv (k : ℕ) : ℕ := (k % 16 ^^^ (if par4 k then 15 else 0)) +
  16 * (!k.testBit 5 ^^ (k.testBit 4 ^^ par4 k)).toNat + 32 * (k.testBit 4 ^^ par4 k).toNat

@[expose] def sg (b : Bool) : ℤ := if b then -1 else 1

@[expose] def LB (i k : ℕ) : List (ℕ × ℤ) :=
  if k.testBit i then [(k - 2 ^ i, 1), (k, -1)] else [(k, 1), (k + 2 ^ i, 1)]

@[expose] def compL (A B : ℕ → List (ℕ × ℤ)) (k : ℕ) : List (ℕ × ℤ) :=
  (A k).flatMap (fun e => (B e.1).map (fun f => (f.1, e.2 * f.2)))

@[expose] def Tl : ℕ → List (ℕ × ℤ) :=
  compL (fun k => [(k, sg (negOut k))]) (compL (fun k => [(linv k, 1)]) (compL (LB 3) (compL (LB 2)
    (compL (LB 1) (compL (LB 0) (compL (fun k => [(pin k, 1)]) (fun k => [(k, sg (negIn k))])))))))

@[expose] def rowList (r : ℕ) : List (ℕ × ℤ) :=
  [false, true].flatMap fun f =>
    let α := xiGammaN (Native.rowC r) f
    if α == 0 then []
    else (List.range 64).map fun ν =>
      let t := xiGTerm (Native.rowEta r != f) (Native.rowC r) ν
      (Native.rowIdx t.2.1 t.2.2, α * sgnI t.1)

@[expose] def coef (L : List (ℕ × ℤ)) (q : ℕ) : ℤ := (L.map fun t => if t.1 = q then t.2 else 0).sum

theorem pos_eq (H j k : ℕ) : pos H j k = 32 * rr H k + j := rfl

theorem pos_lt {H j k : ℕ} (hH : H < 64) (hj : j < 32) (hk : k < 64) : pos H j k < SX := by
  unfold pos
  rw [SX_131072]
  omega

theorem rr_lt {H k : ℕ} (hH : H < 64) (hk : k < 64) : rr H k < 4096 := by
  unfold rr
  omega

theorem tb_pos {H j k : ℕ} (hH : H < 64) (hj : j < 32) (hk : k < 64) (b : ℕ) :
    (pos H j k).testBit b = if b < 5 then j.testBit b else if b < 10 then k.testBit (b - 5)
      else if b < 16 then H.testBit (b - 10) else if b = 16 then k.testBit 5 else false := by
  rw [tbd, tbd j, tbd k, tbd H, tbd k 5]
  unfold pos
  by_cases h0 : b < 5
  · rw [if_pos h0]
    interval_cases b <;> simp <;> omega
  · rw [if_neg h0]
    by_cases h1 : b < 10
    · rw [if_pos h1]
      interval_cases b <;> simp <;> omega
    · rw [if_neg h1]
      by_cases h2 : b < 16
      · rw [if_pos h2]
        interval_cases b <;> simp <;> omega
      · rw [if_neg h2]
        by_cases h3 : b = 16
        · subst h3
          simp
          omega
        · rw [if_neg h3]
          have : 32 * (2048 * (k / 32) + 32 * H + k % 32) + j < 2 ^ b :=
            Nat.lt_of_lt_of_le (by omega : _ < 2 ^ 17) (Nat.pow_le_pow_right (by decide) (by omega))
          rw [Nat.div_eq_of_lt this]
          simp

theorem pos_add {H j k : ℕ} (hk : k < 64) {i : ℕ} (hi : i < 5) (hb : k.testBit i = false) :
    pos H j k + 2 ^ (5 + i) = pos H j (k + 2 ^ i) := by
  rw [tbd] at hb
  simp only [decide_eq_false_iff_not] at hb
  unfold pos
  interval_cases i <;> simp at hb ⊢ <;> omega

theorem pos_sub {H j k : ℕ} (hk : k < 64) {i : ℕ} (hi : i < 5) (hb : k.testBit i = true) :
    pos H j k - 2 ^ (5 + i) = pos H j (k - 2 ^ i) := by
  rw [tbd] at hb
  simp only [decide_eq_true_eq] at hb
  unfold pos
  interval_cases i <;> simp at hb ⊢ <;> omega

theorem pos_valW {H j k : ℕ} (hH : H < 64) (hj : j < 24) (hk : k < 64) : valW.testBit (pos H j k) = true := by
  rw [testBit_valW]
  unfold pos
  simp only [decide_eq_true_eq]
  omega

@[expose] def Rel (np : ℕ) (z' z : ℕ → ZMod (2 ^ np - 1)) (L : ℕ → List (ℕ × ℤ)) : Prop :=
  ∀ k < 64, (∀ e ∈ L k, e.1 < 64) ∧ z' k = ((L k).map fun e => (e.2 : ZMod (2 ^ np - 1)) * z e.1).sum

theorem rel_comp {z2 z1 z0 : ℕ → ZMod (2 ^ np - 1)} {A B : ℕ → List (ℕ × ℤ)} (hA : Rel np z2 z1 A)
    (hB : Rel np z1 z0 B) : Rel np z2 z0 (compL A B) := by
  have aux : ∀ l : List (ℕ × ℤ), (∀ e ∈ l, e.1 < 64) →
      (l.map fun e => (e.2 : ZMod (2 ^ np - 1)) * z1 e.1).sum =
        ((l.flatMap (fun e => (B e.1).map (fun f => (f.1, e.2 * f.2)))).map
          fun e => (e.2 : ZMod (2 ^ np - 1)) * z0 e.1).sum := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro hl
      rw [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append,
        ih (fun e he => hl e (List.mem_cons_of_mem _ he)), (hB a.1 (hl a List.mem_cons_self)).2,
        List.map_map, ← List.sum_map_mul_left]
      congr 2
      refine List.map_congr_left fun f _ => ?_
      simp only [Function.comp_apply]
      push_cast
      ring
  intro k hk
  obtain ⟨h1, h2⟩ := hA k hk
  refine ⟨fun e he => ?_, by rw [h2, aux _ h1]; rfl⟩
  unfold compL at he
  rw [List.mem_flatMap] at he
  obtain ⟨a, ha, he⟩ := he
  rw [List.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  exact (hB a.1 (h1 a ha)).1 f hf

theorem rel_one {z' z : ℕ → ZMod (2 ^ np - 1)} {σ : ℕ → ℕ} {c : ℕ → ℤ} (hσ : ∀ k < 64, σ k < 64)
    (h : ∀ k < 64, z' k = (c k : ZMod (2 ^ np - 1)) * z (σ k)) :
    Rel np z' z (fun k => [(σ k, c k)]) := fun k hk => ⟨fun e he => by
  rw [List.mem_singleton] at he
  rw [he]
  exact hσ k hk, by rw [h k hk]; simp⟩

theorem cast_sg (b : Bool) (x : ZMod (2 ^ np - 1)) :
    ((sg b : ℤ) : ZMod (2 ^ np - 1)) * x = if b then -x else x := by
  cases b <;> simp [sg]

theorem LB_lt : ∀ i < 4, ∀ k < 64, ∀ e ∈ LB i k, e.1 < 64 := by decide

theorem pin_lt : ∀ k < 64, pin k < 64 := by decide

theorem linv_lt : ∀ k < 64, linv k < 64 := by decide

theorem rel_bfly (hO : PLaw np O) {x H j : ℕ} (hx : Bd np SX x) (hH : H < 64) (hj : j < 24) {i : ℕ}
    (hi : i < 4) (hc : Cl SX valW (5 + i)) :
    Rel np (fun k => resPN np SX (O.bfly SX (5 + i) valW x) (pos H j k))
      (fun k => resPN np SX x (pos H j k)) (LB i) := by
  intro k hk
  refine ⟨LB_lt i hi k hk, ?_⟩
  dsimp only
  have hp := pos_lt hH (by omega : j < 32) hk
  have e5 : (pos H j k).testBit (5 + i) = k.testBit i := by
    rw [tb_pos hH (by omega) hk, if_neg (by omega), if_pos (by omega), show 5 + i - 5 = i by omega]
  rw [hO.bfly_res SX_eq (by omega) valW_lt hc hx hp, pos_valW hH hj hk, e5]
  unfold LB
  cases hb : k.testBit i
  · simp only [Bool.false_eq_true, if_false, reduceIte, Bool.true_eq_false]
    rw [pos_add hk (by omega) hb]
    simp
  · simp only [if_true, reduceIte, Bool.true_eq_false, Bool.not_true]
    rw [pos_sub hk (by omega) hb, pos_valW hH hj (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hk)]
    simp only [if_true, reduceIte]
    simp
    ring

theorem clW5 : Cl SX valW (5 + 0) := by
  intro q hq h1 h2
  barith

theorem clW6 : Cl SX valW (5 + 1) := by
  intro q hq h1 h2
  barith

theorem clW7 : Cl SX valW (5 + 2) := by
  intro q hq h1 h2
  barith

theorem clW8 : Cl SX valW (5 + 3) := by
  intro q hq h1 h2
  barith

theorem tb_pos5 {H j k : ℕ} (hH : H < 64) (hj : j < 24) (hk : k < 64) {i : ℕ} (hi : i < 5) :
    (pos H j k).testBit (5 + i) = k.testBit i := by
  rw [tb_pos hH (by omega) hk, if_neg (by omega), if_pos (by omega), show 5 + i - 5 = i by omega]

theorem tb_pos16 {H j k : ℕ} (hH : H < 64) (hj : j < 24) (hk : k < 64) :
    (pos H j k).testBit 16 = k.testBit 5 := by
  rw [tb_pos hH (by omega) hk]
  simp

theorem testBit_dinM (p : ℕ) :
    dinM.testBit p = (decide (p < 131072 ∧ p % 32 < 24) && !(p.testBit 16 && p.testBit 9)) := by
  change (valW &&& (ones SX ^^^ (idPlane SX 16 &&& idPlane SX 9))).testBit p = _
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and, testBit_valW, testBit_ones,
    idPlane_SX (by decide), idPlane_SX (by decide)]
  by_cases hp : p < 131072
  · have : p < SX := hp
    simp [hp, this]
  · simp [hp]

theorem dinM_lt : dinM < 2 ^ SX := Nat.lt_of_le_of_lt Nat.and_le_left valW_lt

theorem dinM_pos {H j k : ℕ} (hH : H < 64) (hj : j < 24) (hk : k < 64) :
    dinM.testBit (pos H j k) = negIn k := by
  rw [testBit_dinM, tb_pos16 hH hj hk, (by rfl : (9 : ℕ) = 5 + 4), tb_pos5 hH hj hk (by decide),
    decide_eq_true (by unfold pos; omega)]
  rfl

theorem testBit_doutM {p : ℕ} (hp : p < SX) :
    doutM.testBit p = (decide (p % 32 < 24) && (e2B (p.testBit 5) (p.testBit 6) (p.testBit 7)
      (p.testBit 8) ^^ (p.testBit 16 && p.testBit 9))) := by
  change (valW &&& ((((idPlane SX 5 &&& idPlane SX 6) ^^^ (idPlane SX 5 &&& idPlane SX 7)) ^^^
    ((idPlane SX 5 &&& idPlane SX 8) ^^^ (idPlane SX 6 &&& idPlane SX 7)) ^^^
    ((idPlane SX 6 &&& idPlane SX 8) ^^^ (idPlane SX 7 &&& idPlane SX 8))) ^^^
    (idPlane SX 16 &&& idPlane SX 9))).testBit p = _
  have hp' : p < 131072 := hp
  simp only [Nat.testBit_and, Nat.testBit_xor, testBit_valW, idPlane_SX (by decide : 5 < 17),
    idPlane_SX (by decide : 6 < 17), idPlane_SX (by decide : 7 < 17), idPlane_SX (by decide : 8 < 17),
    idPlane_SX (by decide : 16 < 17), idPlane_SX (by decide : 9 < 17), decide_eq_true hp,
    Bool.true_and, hp', true_and]
  unfold e2B
  generalize p.testBit 5 = a
  generalize p.testBit 6 = b
  generalize p.testBit 7 = c
  generalize p.testBit 8 = d
  generalize p.testBit 9 = e
  generalize p.testBit 16 = f
  generalize decide (p % 32 < 24) = g
  revert a b c d e f g
  decide

theorem doutM_lt : doutM < 2 ^ SX := Nat.lt_of_le_of_lt Nat.and_le_left valW_lt

theorem doutM_pos {H j k : ℕ} (hH : H < 64) (hj : j < 24) (hk : k < 64) :
    doutM.testBit (pos H j k) = negOut k := by
  rw [testBit_doutM (pos_lt hH (by omega) hk), tb_pos16 hH hj hk, (by rfl : (9 : ℕ) = 5 + 4),
    (by rfl : (5 : ℕ) = 5 + 0), (by rfl : (6 : ℕ) = 5 + 1), (by rfl : (7 : ℕ) = 5 + 2),
    (by rfl : (8 : ℕ) = 5 + 3), tb_pos5 hH hj hk (by decide), tb_pos5 hH hj hk (by decide),
    tb_pos5 hH hj hk (by decide), tb_pos5 hH hj hk (by decide), tb_pos5 hH hj hk (by decide),
    decide_eq_true (by unfold pos; omega)]
  rfl

@[expose] def par58b (q : ℕ) : Bool := (q.testBit 5 ^^ q.testBit 6) ^^ (q.testBit 7 ^^ q.testBit 8)

theorem testBit_par58 (q : ℕ) : par58.testBit q = (decide (q < SX) && par58b q) := by
  change ((idPlane SX 5 ^^^ idPlane SX 6) ^^^ (idPlane SX 7 ^^^ idPlane SX 8)).testBit q = _
  simp only [Nat.testBit_xor, idPlane_SX (by decide : 5 < 17), idPlane_SX (by decide : 6 < 17),
    idPlane_SX (by decide : 7 < 17), idPlane_SX (by decide : 8 < 17), par58b]
  cases decide (q < SX) <;> simp

@[expose] noncomputable def mpin : ℕ := Nat.land par58 (clr SX 9)

theorem testBit_mpin (q : ℕ) : mpin.testBit q = (decide (q < SX) && par58b q && !q.testBit 9) := by
  change (par58 &&& clr SX 9).testBit q = _
  rw [Nat.testBit_and, testBit_par58, testBit_clr_SX (by decide), tbd q 9]
  by_cases hq : q < SX
  · have hq' : q < 131072 := hq
    rw [decide_eq_true hq]
    simp only [Nat.reducePow]
    rcases Nat.mod_two_eq_zero_or_one (q / 512) with h | h <;> simp [h, hq']
  · have hq' : ¬ q < 131072 := hq
    simp [hq, hq']

theorem mpin_lt : mpin < 2 ^ SX := lt_of_tb fun i hi => by
  rw [testBit_mpin] at hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
  exact hi.1.1

theorem mpin_valid : Benes.ValidIn SX 512 mpin := by
  intro p hp
  rw [testBit_mpin] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp
  obtain ⟨⟨h1, -⟩, h2⟩ := hp
  rw [tbd] at h2
  simp only [decide_eq_false_iff_not] at h2
  rw [SX_131072] at h1 ⊢
  refine ⟨by omega, ?_⟩
  have : (p + 512).testBit 9 = true := by
    rw [tbd]
    simp only [decide_eq_true_eq, Nat.reducePow] at h2 ⊢
    omega
  rw [testBit_mpin, this]
  simp

theorem par4_lemmas : ∀ k < 64, (k.testBit 4 = false → k ^^^ 16 = k + 16) ∧
    (k.testBit 4 = true → k ^^^ 16 = k - 16 ∧ par4 (k - 16) = par4 k ∧ (k - 16).testBit 4 = false) := by
  decide

theorem par58b_pos {H j k : ℕ} (hH : H < 64) (hj : j < 24) (hk : k < 64) :
    par58b (pos H j k) = par4 k := by
  unfold par58b par4
  rw [(by rfl : (5 : ℕ) = 5 + 0), (by rfl : (6 : ℕ) = 5 + 1), (by rfl : (7 : ℕ) = 5 + 2),
    (by rfl : (8 : ℕ) = 5 + 3), tb_pos5 hH hj hk (by decide), tb_pos5 hH hj hk (by decide),
    tb_pos5 hH hj hk (by decide), tb_pos5 hH hj hk (by decide)]

theorem mpin_pos {H j k : ℕ} (hH : H < 64) (hj : j < 24) (hk : k < 64) :
    mpin.testBit (pos H j k) = (par4 k && !k.testBit 4) := by
  rw [testBit_mpin, par58b_pos hH hj hk, (by rfl : (9 : ℕ) = 5 + 4), tb_pos5 hH hj hk (by decide),
    decide_eq_true (pos_lt hH (by omega) hk), Bool.true_and]

theorem swp_pin {H j k : ℕ} (hH : H < 64) (hj : j < 24) (hk : k < 64) :
    Benes.swp 512 mpin (pos H j k) = pos H j (pin k) := by
  obtain ⟨l1, l2⟩ := par4_lemmas k hk
  have hp := pos_lt hH (by omega : j < 32) hk
  unfold pin
  cases hb : k.testBit 4 <;> cases hq : par4 k
  ·
    refine swp_eq (fun h => ?_) (fun _ h => ?_) (fun _ _ => by simp)
    · rw [mpin_pos hH hj hk, hb, hq] at h
      exact absurd h (by decide)
    · exfalso
      have h9 : (pos H j k).testBit 9 = false := by
        rw [(by rfl : (9 : ℕ) = 5 + 4), tb_pos5 hH hj hk (by decide), hb]
      have h9' : (pos H j k - 512).testBit 9 = true := by
        rw [tbd] at h9 ⊢
        simp only [decide_eq_false_iff_not, decide_eq_true_eq] at h9 ⊢
        simp only [Nat.reducePow] at h9 ⊢
        omega
      have := h.2
      rw [testBit_mpin, h9'] at this
      simp at this
  ·
    refine swp_eq (fun _ => ?_) (fun h _ => ?_) (fun h _ => ?_)
    · rw [l1 hb, (by rfl : (512 : ℕ) = 2 ^ (5 + 4)), pos_add hk (by decide) hb]
      rfl
    · rw [mpin_pos hH hj hk, hb, hq] at h
      exact absurd h (by decide)
    · rw [mpin_pos hH hj hk, hb, hq] at h
      exact absurd h (by decide)
  ·
    obtain ⟨m1, m2, m3⟩ := l2 hb
    refine swp_eq (fun h => ?_) (fun _ h => ?_) (fun _ _ => by simp)
    · rw [mpin_pos hH hj hk, hb] at h
      simp at h
    · exfalso
      have e := pos_sub (H := H) (j := j) hk (by decide : 4 < 5) hb
      simp only [Nat.reducePow, Nat.reduceAdd] at e
      have := h.2
      rw [e, mpin_pos hH hj (by omega), m2, hq] at this
      simp at this
  ·
    obtain ⟨m1, m2, m3⟩ := l2 hb
    have e := pos_sub (H := H) (j := j) hk (by decide : 4 < 5) hb
    simp only [Nat.reducePow, Nat.reduceAdd] at e
    refine swp_eq (fun h => ?_) (fun _ _ => ?_) (fun _ h => ?_)
    · rw [mpin_pos hH hj hk, hb] at h
      simp at h
    · rw [m1, e]
      rfl
    · exfalso
      apply h
      refine ⟨?_, ?_⟩
      · have h9 : (pos H j k).testBit 9 = true := by
          rw [(by rfl : (9 : ℕ) = 5 + 4), tb_pos5 hH hj hk (by decide), hb]
        rw [tbd] at h9
        simp only [decide_eq_true_eq, Nat.reducePow] at h9
        omega
      · rw [e, mpin_pos hH hj (by omega), m2, hq, m3]
        rfl

theorem tb_shl_plane {S f u v p : ℕ} (hf : f < 2 ^ S) (hp : p < S) :
    (f <<< (v * S)).testBit (u * S + p) = (decide (u = v) && f.testBit p) := by
  rw [Nat.testBit_shiftLeft]
  by_cases h : u = v
  · subst h
    rw [decide_eq_true (by omega), show u * S + p - u * S = p by omega]
    simp
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · have : u * S + p < v * S := by
        have : (u + 1) * S ≤ v * S := Nat.mul_le_mul_right _ h'
        rw [Nat.succ_mul] at this
        omega
      rw [decide_eq_false (by omega)]
      simp [h]
    · have hle : (v + 1) * S ≤ u * S := Nat.mul_le_mul_right _ h'
      rw [Nat.succ_mul] at hle
      rw [decide_eq_true (by omega), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hf
        (Nat.pow_le_pow_right (by decide) (by omega)))]
      simp [h]

theorem tb_planeLoop {S p u : ℕ} (f : ℕ → ℕ) (hp : p < S) : ∀ n, (∀ b < n, f b < 2 ^ S) →
    (Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => Nat.lor acc (Nat.shiftLeft (f b) (Nat.mul b S))) n).testBit
      (u * S + p) = (decide (u < n) && (f u).testBit p)
  | 0, _ => by
    change Nat.testBit 0 _ = _
    simp
  | n + 1, hf => by
    change (Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => Nat.lor acc (Nat.shiftLeft (f b)
      (Nat.mul b S))) n ||| (f n <<< (n * S))).testBit (u * S + p) = _
    rw [Nat.testBit_or, tb_planeLoop f hp n (fun b hb => hf b (by omega)),
      tb_shl_plane (hf n (by omega)) hp]
    by_cases h : u = n
    · subst h
      simp
    · by_cases h' : u < n
      · simp [h, h', show u < n + 1 by omega]
      · simp [h, h', show ¬ u < n + 1 by omega]

theorem idP17_eq : idP 17 = Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => Nat.lor acc
    (Nat.shiftLeft (idPlane SX b) (Nat.mul b SX))) 17 := by
  unfold idP
  rfl

theorem tb_idP17 {u p : ℕ} (hp : p < SX) :
    (idP 17).testBit (u * SX + p) = (decide (u < 17) && p.testBit u) := by
  rw [idP17_eq, tb_planeLoop (fun b => idPlane SX b) hp 17 (fun b hb => lt_of_tb fun i hi => by
    rw [idPlane_SX hb, Bool.and_eq_true, decide_eq_true_eq] at hi
    exact hi.1)]
  by_cases hu : u < 17
  · rw [decide_eq_true hu, idPlane_SX hu, decide_eq_true hp]
    simp
  · simp [hu]

theorem testBit_setPl {S b y X u p : ℕ} (hy : y < 2 ^ S) (hp : p < S) :
    (setPl S b y X).testBit (u * S + p) = if u = b then y.testBit p else X.testBit (u * S + p) := by
  change ((X ^^^ (plane S b X <<< (b * S))) ||| (y <<< (b * S))).testBit (u * S + p) = _
  rw [Nat.testBit_or, Nat.testBit_xor, tb_shl_plane (plane_lt' S b X) hp, tb_shl_plane hy hp,
    testBit_plane' hp]
  by_cases h : u = b
  · subst h
    simp
  · simp [h]

theorem par58b_lt {y : ℕ} (hy : y < SX) : par58.testBit y = par58b y := by
  rw [testBit_par58, decide_eq_true hy, Bool.true_and]

theorem testBit_lab {u y : ℕ} (hu : u < 17) (hy : y < SX) :
    (setPl SX 16 (Nat.xor (ones SX) (Nat.xor (idPlane SX 16) (idPlane SX 9)))
      (setPl SX 9 (Nat.xor (idPlane SX 16) par58)
        (Nat.xor (idP 17) (Nat.shiftLeft (repP SX 4 par58) (Nat.mul 5 SX))))).testBit (u * SX + y) =
      if u = 16 then !(y.testBit 16 ^^ y.testBit 9) else if u = 9 then (y.testBit 16 ^^ par58b y)
      else (y.testBit u ^^ (decide (5 ≤ u ∧ u < 9) && par58b y)) := by
  have l16 : Nat.xor (ones SX) (Nat.xor (idPlane SX 16) (idPlane SX 9)) < 2 ^ SX :=
    Nat.xor_lt_two_pow (ones_lt _) (Nat.xor_lt_two_pow (lt_of_tb fun i hi => by
      rw [idPlane_SX (by decide), Bool.and_eq_true, decide_eq_true_eq] at hi
      exact hi.1) (lt_of_tb fun i hi => by
      rw [idPlane_SX (by decide), Bool.and_eq_true, decide_eq_true_eq] at hi
      exact hi.1))
  have l9 : Nat.xor (idPlane SX 16) par58 < 2 ^ SX :=
    Nat.xor_lt_two_pow (lt_of_tb fun i hi => by
      rw [idPlane_SX (by decide), Bool.and_eq_true, decide_eq_true_eq] at hi
      exact hi.1) (lt_of_tb fun i hi => by
      rw [testBit_par58, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact hi.1)
  have hy' : y < 131072 := hy
  rw [testBit_setPl l16 hy]
  by_cases h16 : u = 16
  · rw [if_pos h16, if_pos h16]
    change (ones SX ^^^ (idPlane SX 16 ^^^ idPlane SX 9)).testBit y = _
    rw [Nat.testBit_xor, Nat.testBit_xor, testBit_ones, idPlane_SX (by decide),
      idPlane_SX (by decide), decide_eq_true hy]
    simp
  · rw [if_neg h16, if_neg h16, testBit_setPl l9 hy]
    by_cases h9 : u = 9
    · rw [if_pos h9, if_pos h9]
      change (idPlane SX 16 ^^^ par58).testBit y = _
      rw [Nat.testBit_xor, idPlane_SX (by decide), decide_eq_true hy, par58b_lt hy, Bool.true_and]
    · rw [if_neg h9, if_neg h9]
      change (idP 17 ^^^ (repP SX 4 par58 <<< (5 * SX))).testBit (u * SX + y) = _
      have hm : par58 < 2 ^ SX := lt_of_tb fun i hi => by
        rw [testBit_par58, Bool.and_eq_true, decide_eq_true_eq] at hi
        exact hi.1
      rw [Nat.testBit_xor, tb_idP17 hy, decide_eq_true hu, Bool.true_and, Nat.testBit_shiftLeft]
      congr 1
      by_cases h5 : 5 ≤ u
      · rw [decide_eq_true (by rw [SX_131072]; omega), Bool.true_and, testBit_repP hm,
          show u * SX + y - 5 * SX = (u - 5) * SX + y by rw [SX_131072]; omega, idx_mod' hy,
          par58b_lt hy]
        by_cases h8 : u < 9
        · rw [decide_eq_true (by rw [SX_131072]; omega), decide_eq_true ⟨h5, h8⟩]
        · rw [decide_eq_false (by rw [SX_131072]; omega), decide_eq_false (by omega)]
      · rw [decide_eq_false (by rw [SX_131072]; omega), decide_eq_false (by omega)]
        simp

theorem linv_bits : ∀ k < 64, (∀ i < 4, (linv k).testBit i = (k.testBit i ^^ par4 k)) ∧
    (linv k).testBit 4 = (!k.testBit 5 ^^ (k.testBit 4 ^^ par4 k)) ∧
    (linv k).testBit 5 = (k.testBit 4 ^^ par4 k) := by
  decide

theorem bool_solve : ∀ y5 y6 y7 y8 y9 y16 x5 x6 x7 x8 x9 x16 : Bool,
    x5 = (y5 ^^ ((y5 ^^ y6) ^^ (y7 ^^ y8))) → x6 = (y6 ^^ ((y5 ^^ y6) ^^ (y7 ^^ y8))) →
    x7 = (y7 ^^ ((y5 ^^ y6) ^^ (y7 ^^ y8))) → x8 = (y8 ^^ ((y5 ^^ y6) ^^ (y7 ^^ y8))) →
    x9 = (y16 ^^ ((y5 ^^ y6) ^^ (y7 ^^ y8))) → x16 = !(y16 ^^ y9) →
    y5 = (x5 ^^ ((x5 ^^ x6) ^^ (x7 ^^ x8))) ∧ y6 = (x6 ^^ ((x5 ^^ x6) ^^ (x7 ^^ x8))) ∧
    y7 = (x7 ^^ ((x5 ^^ x6) ^^ (x7 ^^ x8))) ∧ y8 = (x8 ^^ ((x5 ^^ x6) ^^ (x7 ^^ x8))) ∧
    y16 = (x9 ^^ ((x5 ^^ x6) ^^ (x7 ^^ x8))) ∧ y9 = (!x16 ^^ (x9 ^^ ((x5 ^^ x6) ^^ (x7 ^^ x8)))) := by
  intro y5 y6 y7 y8 y9 y16 x5 x6 x7 x8 x9 x16 h5 h6 h7 h8 h9 h16
  subst h5 h6 h7 h8 h9 h16
  revert y5 y6 y7 y8 y9 y16
  decide

theorem pout_lab {F : Fix} (hp : poutOK F = true) : netOK 17 F.pout = true ∧
    ∀ u < 17, ∀ r < SX, r.testBit u =
      (if u = 16 then !((Benes.benesPerm 17 F.pout r).testBit 16 ^^ (Benes.benesPerm 17 F.pout r).testBit 9)
      else if u = 9 then ((Benes.benesPerm 17 F.pout r).testBit 16 ^^ par58b (Benes.benesPerm 17 F.pout r))
      else ((Benes.benesPerm 17 F.pout r).testBit u ^^
        (decide (5 ≤ u ∧ u < 9) && par58b (Benes.benesPerm 17 F.pout r)))) := by
  have hp' : andB (netOK 17 F.pout) (Nat.beq (netP SX 17 17 F.pout
      (setPl SX 16 (Nat.xor (ones SX) (Nat.xor (idPlane SX 16) (idPlane SX 9)))
        (setPl SX 9 (Nat.xor (idPlane SX 16) par58)
          (Nat.xor (idP 17) (Nat.shiftLeft (repP SX 4 par58) (Nat.mul 5 SX)))))) (idP 17)) = true := hp
  simp only [andB_and, Bool.and_eq_true, Nat.beq_eq] at hp'
  obtain ⟨hn, he⟩ := hp'
  refine ⟨hn, fun u hu r hr => ?_⟩
  have hv := Benes.stagesValid_of_netOK hn
  have hπ := Benes.benesPerm_lt hv hr
  have := (Benes.testBit_netP (n := 17) SX_eq hn (setPl SX 16 (Nat.xor (ones SX) (Nat.xor
    (idPlane SX 16) (idPlane SX 9))) (setPl SX 9 (Nat.xor (idPlane SX 16) par58)
      (Nat.xor (idP 17) (Nat.shiftLeft (repP SX 4 par58) (Nat.mul 5 SX)))))).1 u hu r hr
  rw [he, Nat.mul_comm SX u, tb_idP17 hr, decide_eq_true hu, Bool.true_and,
    testBit_lab hu hπ] at this
  exact this

theorem pout_pos {F : Fix} (hp : poutOK F = true) {H j k : ℕ} (hH : H < 64) (hj : j < 24)
    (hk : k < 64) : Benes.benesPerm 17 F.pout (pos H j k) = pos H j (linv k) := by
  obtain ⟨hn, hl⟩ := pout_lab hp
  have hv := Benes.stagesValid_of_netOK hn
  have hr := pos_lt hH (by omega : j < 32) hk
  have hπ := Benes.benesPerm_lt hv hr
  have hl' := linv_lt k hk
  obtain ⟨lb, l4, l5⟩ := linv_bits k hk
  have e : ∀ u < 17, u ≠ 5 → u ≠ 6 → u ≠ 7 → u ≠ 8 → u ≠ 9 → u ≠ 16 →
      (Benes.benesPerm 17 F.pout (pos H j k)).testBit u = (pos H j k).testBit u := by
    intro u hu a5 a6 a7 a8 a9 a16
    rw [hl u hu _ hr, if_neg a16, if_neg a9, decide_eq_false (by omega), Bool.false_and,
      Bool.xor_false]
  have e5 := hl 5 (by decide) _ hr
  have e6 := hl 6 (by decide) _ hr
  have e7 := hl 7 (by decide) _ hr
  have e8 := hl 8 (by decide) _ hr
  have e9 := hl 9 (by decide) _ hr
  have e16 := hl 16 (by decide) _ hr
  rw [if_neg (by decide), if_neg (by decide), decide_eq_true (by decide), Bool.true_and] at e5 e6 e7 e8
  rw [if_neg (by decide), if_pos rfl] at e9
  rw [if_pos rfl] at e16
  unfold par58b at e5 e6 e7 e8 e9
  generalize Benes.benesPerm 17 F.pout (pos H j k) = y at e5 e6 e7 e8 e9 e16 e hπ ⊢
  obtain ⟨s5, s6, s7, s8, s16, s9⟩ := bool_solve _ _ _ _ _ _ _ _ _ _ _ _ e5 e6 e7 e8 e9 e16
  have k5 : ∀ i < 5, (pos H j k).testBit (5 + i) = k.testBit i := fun i hi => tb_pos5 hH hj hk hi
  have q : ((((pos H j k).testBit 5 ^^ (pos H j k).testBit 6) ^^ ((pos H j k).testBit 7 ^^
      (pos H j k).testBit 8))) = par4 k := par58b_pos hH hj hk
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 17
  · rw [tb_pos hH (by omega) hl']
    by_cases b5 : b < 5
    · rw [if_pos b5, e b hb (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        tb_pos hH (by omega) hk, if_pos b5]
    · rw [if_neg b5]
      by_cases b10 : b < 10
      · rw [if_pos b10]
        interval_cases b
        · rw [s5, q, lb 0 (by decide), ← k5 0 (by decide)]
        · rw [s6, q, lb 1 (by decide), ← k5 1 (by decide)]
        · rw [s7, q, lb 2 (by decide), ← k5 2 (by decide)]
        · rw [s8, q, lb 3 (by decide), ← k5 3 (by decide)]
        · rw [s9, q, l4, (by rfl : (9 : ℕ) = 5 + 4), k5 4 (by decide), tb_pos16 hH hj hk]
      · rw [if_neg b10]
        by_cases b16 : b < 16
        · rw [if_pos b16, e b hb (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            tb_pos hH (by omega) hk, if_neg b5, if_neg b10, if_pos b16]
        · rw [if_neg b16, if_pos (by omega : b = 16)]
          obtain rfl : b = 16 := by omega
          rw [s16, q, l5, (by rfl : (9 : ℕ) = 5 + 4), k5 4 (by decide)]
  · have h1 : y < 2 ^ b := Nat.lt_of_lt_of_le hπ (Nat.pow_le_pow_right (n := 2) (by decide)
      (by omega : 17 ≤ b))
    have h2 : pos H j (linv k) < 2 ^ b := Nat.lt_of_lt_of_le (pos_lt hH (by omega) hl')
      (Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 17 ≤ b))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

theorem pout_col {F : Fix} (hp : poutOK F = true) {r : ℕ} (hr : r < SX) :
    Benes.benesPerm 17 F.pout r < SX ∧ Benes.benesPerm 17 F.pout r % 32 = r % 32 := by
  obtain ⟨hn, hl⟩ := pout_lab hp
  have hπ := Benes.benesPerm_lt (Benes.stagesValid_of_netOK hn) hr
  refine ⟨hπ, Nat.eq_of_testBit_eq fun b => ?_⟩
  rw [(by rfl : (32 : ℕ) = 2 ^ 5), Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hb : b < 5
  · rw [decide_eq_true hb, Bool.true_and, Bool.true_and, hl b (by omega) r hr, if_neg (by omega),
      if_neg (by omega), decide_eq_false (by omega)]
    simp
  · simp [hb]

theorem pinWG_eq (x : ℕ) : pinWG O x = dsw 512 (O.rep SX mpin) x := rfl

theorem wht4G_eq (x : ℕ) : wht4G O x =
    O.bfly SX (5 + 3) valW (O.bfly SX (5 + 2) valW (O.bfly SX (5 + 1) valW (O.bfly SX (5 + 0) valW x))) :=
  rfl

theorem rel_neg (hO : PLaw np O) {m x H j : ℕ} (hm : m < 2 ^ SX) (hx : Bd np SX x) (hH : H < 64)
    (hj : j < 24) {f : ℕ → Bool} (hf : ∀ k < 64, m.testBit (pos H j k) = f k) :
    Rel np (fun k => resPN np SX (O.neg SX m x) (pos H j k)) (fun k => resPN np SX x (pos H j k))
      (fun k => [(k, sg (f k))]) :=
  rel_one (fun k hk => hk) fun k hk => by
    rw [hO.neg_res hm hx (pos_lt hH (by omega) hk), hf k hk, cast_sg]

theorem rel_twin (hO : PLaw np O) {F : Fix} (hp : poutOK F = true) {W H j : ℕ} (hW : Bd np SX W)
    (hH : H < 64) (hj : j < 24) :
    Rel np (fun k => resPN np SX (O.neg SX doutM (O.net SX 17 F.pout
      (wht4G O (pinWG O (O.neg SX dinM (colxiG O SX 0 1 valW W)))))) (pos H j k))
      (fun k => resPN np SX (colxiG O SX 0 1 valW W) (pos H j k)) Tl := by
  have hn := (pout_lab hp).1
  have b0 := colW_bd hO hW
  have b1 := hO.neg_bd dinM_lt b0
  have b2 : Bd np SX (pinWG O (O.neg SX dinM (colxiG O SX 0 1 valW W))) :=
    bd_dsw_rep hO mpin_valid b1
  have c5 := hO.bfly_bd (k := 17) (b := 5 + 0) SX_eq (by decide) valW_lt b2
  have c6 := hO.bfly_bd (k := 17) (b := 5 + 1) SX_eq (by decide) valW_lt c5
  have c7 := hO.bfly_bd (k := 17) (b := 5 + 2) SX_eq (by decide) valW_lt c6
  have c8 := hO.bfly_bd (k := 17) (b := 5 + 3) SX_eq (by decide) valW_lt c7
  have c8' : Bd np SX (wht4G O (pinWG O (O.neg SX dinM (colxiG O SX 0 1 valW W)))) := c8
  have b4 := hO.net_bd SX_eq hn c8'
  have r8 := rel_neg hO dinM_lt b0 hH hj (fun k hk => dinM_pos hH hj hk)
  have r7 : Rel np (fun k => resPN np SX (pinWG O (O.neg SX dinM (colxiG O SX 0 1 valW W))) (pos H j k))
      (fun k => resPN np SX (O.neg SX dinM (colxiG O SX 0 1 valW W)) (pos H j k))
      (fun k => [(pin k, 1)]) := rel_one pin_lt fun k hk => by
    rw [pinWG_eq, res_dsw_rep hO mpin_valid b1 (pos_lt hH (by omega) hk), swp_pin hH hj hk]
    simp
  have q0 := rel_bfly hO b2 hH hj (i := 0) (by decide) clW5
  have q1 := rel_bfly hO c5 hH hj (i := 1) (by decide) clW6
  have q2 := rel_bfly hO c6 hH hj (i := 2) (by decide) clW7
  have q3 := rel_bfly hO c7 hH hj (i := 3) (by decide) clW8
  have r2 : Rel np (fun k => resPN np SX (O.net SX 17 F.pout (wht4G O (pinWG O (O.neg SX dinM
      (colxiG O SX 0 1 valW W))))) (pos H j k))
      (fun k => resPN np SX (wht4G O (pinWG O (O.neg SX dinM (colxiG O SX 0 1 valW W)))) (pos H j k))
      (fun k => [(linv k, 1)]) := rel_one linv_lt fun k hk => by
    rw [hO.net_res SX_eq hn c8' (pos_lt hH (by omega) hk), pout_pos hp hH hj hk]
    simp
  have r1 := rel_neg hO doutM_lt b4 hH hj (fun k hk => doutM_pos hH hj hk)
  exact rel_comp r1 (rel_comp r2 (rel_comp q3 (rel_comp q2 (rel_comp q1 (rel_comp q0
    (rel_comp r7 r8))))))

theorem pi0N_bit0' (x : ℕ) : (pi0N x).testBit 0 = false := by
  unfold pi0N
  cases h : x.testBit 0
  · rw [ite_eq_right (by simp), Nat.xor_zero, h]
  · rw [ite_eq_left rfl, Nat.testBit_xor, h]
    rfl

theorem pi0N_of_even' {x : ℕ} (h : x.testBit 0 = false) : pi0N x = x := by
  unfold pi0N
  rw [ite_eq_right (by simp [h]), Nat.xor_zero]

theorem xor_split' (i a b a' b' : ℕ) (hb : b < 2 ^ i) (hb' : b' < 2 ^ i) :
    (2 ^ i * a + b) ^^^ (2 ^ i * a' + b') = 2 ^ i * (a ^^^ a') + (b ^^^ b') := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hb',
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hb hb'), Nat.testBit_xor, Nat.testBit_xor]
  split_ifs <;> rfl

theorem xor64 {H y m : ℕ} (hy : y < 64) (hm : m < 64) : (64 * H + y) ^^^ m = 64 * H + (y ^^^ m) := by
  have := xor_split' 6 H y 0 m (by simpa using hy) (by simpa using hm)
  simpa using this

theorem tb0_64 {H y : ℕ} (hy : y < 64) : (64 * H + y).testBit 0 = y.testBit 0 := by
  have := Nat.testBit_two_pow_mul_add H (i := 6) (b := y) (by simpa using hy) 0
  simpa using this

theorem pi0N_lt64 {y : ℕ} (hy : y < 64) : pi0N y < 64 := by
  unfold pi0N
  have : (if y.testBit 0 = true then 63 else 0) < 2 ^ 6 := by split_ifs <;> decide
  exact Nat.xor_lt_two_pow (n := 6) (by simpa using hy) this

theorem pi0N_64 {H y : ℕ} (hy : y < 64) : pi0N (64 * H + y) = 64 * H + pi0N y := by
  unfold pi0N
  rw [tb0_64 hy]
  exact xor64 hy (by split_ifs <;> decide)

theorem pairN_64 {H c g : ℕ} (hc : c < 64) (hg : g < 64) : pairN (64 * H + c) g = pairN c g := by
  unfold pairN
  congr 1
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_and, Nat.testBit_and]
  by_cases hb : b < 6
  · have := Nat.testBit_two_pow_mul_add H (i := 6) (b := c) (by simpa using hc) b
    simp only [Nat.reducePow] at this
    rw [this, if_pos hb]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hg (Nat.pow_le_pow_right (n := 2) (by decide)
      (by omega : 6 ≤ b)))]
    simp

theorem xiGammaN_64 {H c0 : ℕ} (hc : c0 < 64) (he : c0.testBit 0 = false) (f : Bool) :
    xiGammaN (64 * H + c0) f = xiGammaN c0 f := by
  unfold xiGammaN
  have e : pi0N (64 * H + c0) = 64 * H + c0 := pi0N_of_even' (by rw [tb0_64 hc, he])
  rw [e, pi0N_of_even' he]
  congr 1
  funext μ
  rw [pairN_64 hc (gammaLowN_lt μ)]

theorem rowIdx_64 {H c0 ν : ℕ} (hH : H < 64) (hc : c0 < 64) (he : c0.testBit 0 = false)
    (hν : ν < 64) (η : Bool) :
    Native.rowIdx η (shiftN ν (pi0N (64 * H + c0))) =
      (if η then 2048 else 0) + (32 * H + pi0N (c0 ^^^ ν) / 2) := by
  have e : pi0N (64 * H + c0) = 64 * H + c0 := pi0N_of_even' (by rw [tb0_64 hc, he])
  have hx : c0 ^^^ ν < 64 := Nat.xor_lt_two_pow (n := 6) (by simpa using hc) (by simpa using hν)
  have hw := pi0N_lt64 hx
  unfold shiftN Native.rowIdx
  rw [e, xor64 hc hν, pi0N_64 hx, pi0N_of_even' (by rw [tb0_64 hw, pi0N_bit0'])]
  congr 1
  omega

@[expose] def rowOf (η : Bool) (c : ℕ) : List (ℕ × ℤ) :=
  [false, true].flatMap fun f =>
    if xiGammaN c f == 0 then []
    else (List.range 64).map fun ν =>
      (Native.rowIdx (xiGTerm (η != f) c ν).2.1 (xiGTerm (η != f) c ν).2.2,
        xiGammaN c f * sgnI (xiGTerm (η != f) c ν).1)

theorem rowList_eq (r : ℕ) : rowList r = rowOf (Native.rowEta r) (Native.rowC r) := rfl

theorem rowOf_64 {H c0 : ℕ} (hH : H < 64) (hc : c0 < 64) (he : c0.testBit 0 = false) (η : Bool) :
    rowOf η (64 * H + c0) = (rowOf η c0).map fun t => (t.1 + 32 * H, t.2) := by
  unfold rowOf
  rw [List.map_flatMap]
  congr 1
  funext f
  rw [xiGammaN_64 hc he]
  split_ifs
  · rfl
  · rw [List.map_map]
    refine List.map_congr_left fun ν hν => ?_
    have hν' := List.mem_range.1 hν
    simp only [Function.comp_apply, xiGTerm]
    rw [rowIdx_64 hH hc he hν', show c0 = 64 * 0 + c0 by omega, rowIdx_64 (by decide) hc he hν']
    simp only [Nat.mul_zero, Nat.zero_add, Prod.mk.injEq, and_true]
    omega

theorem rowC_rr {H k : ℕ} (hH : H < 64) (hk : k < 64) : Native.rowC (rr H k) = 64 * H + 2 * (k % 32) := by
  unfold Native.rowC rr
  omega

theorem rowEta_rr {H k : ℕ} (hH : H < 64) (hk : k < 64) : Native.rowEta (rr H k) = Native.rowEta (rr 0 k) := by
  unfold Native.rowEta rr
  apply decide_eq_decide.2
  omega

theorem rowList_shift {H k : ℕ} (hH : H < 64) (hk : k < 64) :
    rowList (rr H k) = (rowList (rr 0 k)).map fun t => (t.1 + 32 * H, t.2) := by
  have he : (2 * (k % 32)).testBit 0 = false := by
    rw [Nat.testBit_zero]
    simp
  rw [rowList_eq, rowList_eq, rowEta_rr hH hk, rowC_rr hH hk, rowC_rr (by decide) hk, Nat.mul_zero,
    Nat.zero_add]
  exact rowOf_64 hH (by omega) he _

theorem xiRows_get {r : ℕ} (hr : r < 4096) : (Native.xiRows ())[r]! = rowList r := by
  unfold Native.xiRows
  rw [getElem!_pos _ r (by simp; omega)]
  simp only [Array.getElem_map, Array.getElem_range]
  rfl

theorem wT_xi {p : ℕ} (hp : p < 98304) :
    (Native.GD.ofGen (Native.mkCtx ()) .xi).wT p = (rowList (p / 24)).map fun t => (t.1 * 24 + p % 24, t.2) := by
  unfold Native.GD.wT
  simp only [Native.GD.ofGen]
  rw [xiRows_get (by omega)]

@[expose] def rbB (k0 : ℕ) : Bool :=
  (rowList (rr 0 k0)).all (fun t => decide (t.1 < 4096 ∧ t.1 / 32 % 64 = 0)) &&
    (List.range 64).all fun k => coef (rowList (rr 0 k0)) (rr 0 k) == 16 * coef (Tl k) k0

set_option maxRecDepth 100000 in
theorem rb0 : ∀ i < 8, rbB (0 + i) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem rb1 : ∀ i < 8, rbB (8 + i) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem rb2 : ∀ i < 8, rbB (16 + i) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem rb3 : ∀ i < 8, rbB (24 + i) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem rb4 : ∀ i < 8, rbB (32 + i) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem rb5 : ∀ i < 8, rbB (40 + i) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem rb6 : ∀ i < 8, rbB (48 + i) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem rb7 : ∀ i < 8, rbB (56 + i) = true := by decide +kernel

theorem rbB_all : ∀ k0 < 64, rbB k0 = true := by
  intro k0 hk0
  have e : k0 = 8 * (k0 / 8) + k0 % 8 := by omega
  have hi : k0 % 8 < 8 := Nat.mod_lt _ (by decide)
  have hc : k0 / 8 < 8 := by omega
  rw [e]
  generalize k0 / 8 = c at hc
  generalize k0 % 8 = i at hi
  interval_cases c
  · exact rb0 i hi
  · exact rb1 i hi
  · exact rb2 i hi
  · exact rb3 i hi
  · exact rb4 i hi
  · exact rb5 i hi
  · exact rb6 i hi
  · exact rb7 i hi

theorem rows_block : ∀ k0 < 64, (rowList (rr 0 k0)).all (fun t => decide (t.1 < 4096 ∧ t.1 / 32 % 64 = 0)) ∧
    ∀ k < 64, coef (rowList (rr 0 k0)) (rr 0 k) = 16 * coef (Tl k) k0 := by
  intro k0 hk0
  have h := rbB_all k0 hk0
  unfold rbB at h
  rw [Bool.and_eq_true] at h
  refine ⟨h.1, fun k hk => ?_⟩
  have := List.all_eq_true.1 h.2 k (List.mem_range.2 hk)
  simpa using this

theorem Tl_lt : ∀ k < 64, ∀ e ∈ Tl k, e.1 < 64 := by decide

theorem scat_coef (T : ℕ → List (ℕ × ℤ)) (p q : ℕ) : scat T p q = coef (T p) q := by
  unfold scat coef
  induction T p with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    by_cases h : a.1 = q
    · simp [h, ih]
    · simp [h, ih]

theorem coef_zero {L : List (ℕ × ℤ)} {q : ℕ} (h : ∀ t ∈ L, t.1 ≠ q) : coef L q = 0 := by
  unfold coef
  rw [List.map_congr_left (g := fun _ => (0 : ℤ)) fun t ht => if_neg (h t ht)]
  simp

theorem coef_map_col {L : List (ℕ × ℤ)} {r j c : ℕ} (hj : j < 24) (hc : c < 24) :
    coef (L.map fun t => (t.1 * 24 + c, t.2)) (24 * r + j) = if c = j then coef L r else 0 := by
  split_ifs with h
  · subst h
    unfold coef
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply]
    by_cases e : t.1 = r
    · rw [if_pos (by omega), if_pos e]
    · rw [if_neg (by omega), if_neg e]
  · refine coef_zero fun t ht => ?_
    obtain ⟨t', -, rfl⟩ := List.mem_map.1 ht
    simp only
    omega

theorem coef_shift {L : List (ℕ × ℤ)} (hL : ∀ t ∈ L, t.1 < 4096 ∧ t.1 / 32 % 64 = 0) {H0 H k : ℕ}
    (hH0 : H0 < 64) (hH : H < 64) (hk : k < 64) :
    coef (L.map fun t => (t.1 + 32 * H0, t.2)) (rr H k) = if H0 = H then coef L (rr 0 k) else 0 := by
  split_ifs with h
  · subst h
    unfold coef
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    have := hL t ht
    simp only [Function.comp_apply]
    by_cases e : t.1 = rr 0 k
    · rw [if_pos (by unfold rr at e ⊢; omega), if_pos e]
    · rw [if_neg (by unfold rr at e ⊢; omega), if_neg e]
  · refine coef_zero fun t ht => ?_
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    have := hL t' ht'
    simp only
    unfold rr
    omega

theorem sum_coef {M : ℕ} (L : List (ℕ × ℤ)) (hL : ∀ e ∈ L, e.1 < 64) (f : ℕ → ZMod M) :
    ∑ k0 ∈ Finset.range 64, ((coef L k0 : ℤ) : ZMod M) * f k0 =
      (L.map fun e => (e.2 : ZMod M) * f e.1).sum := by
  induction L with
  | nil => simp [coef]
  | cons a L ih =>
    have e : ∀ k0, coef (a :: L) k0 = (if a.1 = k0 then a.2 else 0) + coef L k0 := fun k0 => by
      unfold coef
      rw [List.map_cons, List.sum_cons]
    simp only [e]
    push_cast
    simp only [add_mul, Finset.sum_add_distrib]
    rw [ih fun e he => hL e (List.mem_cons_of_mem _ he), List.map_cons, List.sum_cons]
    congr 1
    have ha := hL a List.mem_cons_self
    rw [Finset.sum_eq_single a.1]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]
      simp
    · intro hn
      exact absurd (Finset.mem_range.2 ha) hn

theorem sum_range_mul {M : ℕ} (f : ℕ → ZMod M) (b : ℕ) : ∀ a,
    ∑ p ∈ Finset.range (a * b), f p = ∑ x ∈ Finset.range a, ∑ y ∈ Finset.range b, f (b * x + y)
  | 0 => by simp
  | a + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul f b a, Finset.sum_range_succ]
    rw [Nat.mul_comm a b]

theorem nat_sum {M : ℕ} (Y : ℕ → ℕ → ZMod M) {H k j : ℕ} (hH : H < 64) (hk : k < 64) (hj : j < 24) :
    ∑ p ∈ Finset.range 98304, ((scat (Native.GD.ofGen (Native.mkCtx ()) .xi).wT p (24 * rr H k + j) : ℤ)
      : ZMod M) * Y (p / 24) (p % 24) =
      16 * ((Tl k).map fun e => (e.2 : ZMod M) * Y (rr H e.1) j).sum := by
  rw [show (98304 : ℕ) = 4096 * 24 by rfl, sum_range_mul]
  have s1 : ∀ r ∈ Finset.range 4096, ∑ c ∈ Finset.range 24,
      ((scat (Native.GD.ofGen (Native.mkCtx ()) .xi).wT (24 * r + c) (24 * rr H k + j) : ℤ) : ZMod M) *
        Y ((24 * r + c) / 24) ((24 * r + c) % 24) =
      ((coef (rowList r) (rr H k) : ℤ) : ZMod M) * Y r j := by
    intro r hr
    have hr' := Finset.mem_range.1 hr
    rw [Finset.sum_eq_single j]
    · rw [scat_coef, wT_xi (by omega), show (24 * r + j) / 24 = r by omega,
        show (24 * r + j) % 24 = j by omega, coef_map_col hj hj, if_pos rfl]
    · intro c hc hcj
      have := Finset.mem_range.1 hc
      rw [scat_coef, wT_xi (by omega), show (24 * r + c) / 24 = r by omega,
        show (24 * r + c) % 24 = c by omega, coef_map_col hj this, if_neg hcj]
      simp
    · intro hn
      exact absurd (Finset.mem_range.2 hj) hn
  rw [Finset.sum_congr rfl s1]
  rw [show (4096 : ℕ) = 2 * 2048 by rfl, sum_range_mul]
  have s2 : ∀ a ∈ Finset.range 2, ∑ x ∈ Finset.range 2048,
      ((coef (rowList (2048 * a + x)) (rr H k) : ℤ) : ZMod M) * Y (2048 * a + x) j =
      ∑ b ∈ Finset.range 32, ((coef (rowList (rr 0 (32 * a + b))) (rr 0 k) : ℤ) : ZMod M) *
        Y (rr H (32 * a + b)) j := by
    intro a ha
    have ha' := Finset.mem_range.1 ha
    rw [show (2048 : ℕ) = 64 * 32 by rfl, sum_range_mul, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb' := Finset.mem_range.1 hb
    rw [Finset.sum_eq_single H]
    · have e : 64 * 32 * a + (32 * H + b) = rr H (32 * a + b) := by unfold rr; omega
      rw [e, rowList_shift hH (by omega), coef_shift (by
        intro t ht
        have := (rows_block (32 * a + b) (by omega)).1
        rw [List.all_eq_true] at this
        simpa using this t ht) hH hH hk, if_pos rfl]
    · intro H0 hH0 hne
      have hH0' := Finset.mem_range.1 hH0
      have e : 64 * 32 * a + (32 * H0 + b) = rr H0 (32 * a + b) := by unfold rr; omega
      rw [e, rowList_shift hH0' (by omega), coef_shift (by
        intro t ht
        have := (rows_block (32 * a + b) (by omega)).1
        rw [List.all_eq_true] at this
        simpa using this t ht) hH0' hH hk, if_neg hne]
      simp
    · intro hn
      exact absurd (Finset.mem_range.2 hH) hn
  rw [Finset.sum_congr rfl s2]
  have s3 := sum_range_mul (fun k0 => ((coef (rowList (rr 0 k0)) (rr 0 k) : ℤ) : ZMod M) *
    Y (rr H k0) j) 32 2
  simp only [Nat.reduceMul] at s3
  rw [← s3]
  have s4 : ∀ k0 ∈ Finset.range 64, ((coef (rowList (rr 0 k0)) (rr 0 k) : ℤ) : ZMod M) * Y (rr H k0) j =
      16 * (((coef (Tl k) k0 : ℤ) : ZMod M) * Y (rr H k0) j) := by
    intro k0 hk0
    rw [(rows_block k0 (Finset.mem_range.1 hk0)).2 k hk]
    push_cast
    ring
  rw [Finset.sum_congr rfl s4, ← Finset.mul_sum, sum_coef _ (Tl_lt k hk)]

theorem xi_W (hO : PLaw np O) (hnp : 2 ≤ np) {F : Fix} (hp : poutOK F = true) {v : Native.DVec}
    {W : ℕ} (hW1 : ∀ r < 4096, ∀ j < 24, resPN np SX W (32 * r + j) = resN np v (98580 + 24 * r + j))
    (hW2 : ∀ p < SX, 24 ≤ p % 32 → resPN np SX W p = 0) (hW3 : W < 2 ^ (np * SX)) :
    (∀ r < 4096, ∀ j < 24, resPN np SX (O.half SX 3 (O.neg SX doutM (O.net SX 17 F.pout
      (wht4G O (pinWG O (O.neg SX dinM (colxiG O SX 0 1 valW W))))))) (32 * r + j) =
        resN np (Native.applyGen (Native.mkCtx ()) .xi v) (98580 + 24 * r + j)) ∧
    (∀ p < SX, 24 ≤ p % 32 → resPN np SX (O.half SX 3 (O.neg SX doutM (O.net SX 17 F.pout
      (wht4G O (pinWG O (O.neg SX dinM (colxiG O SX 0 1 valW W))))))) p = 0) ∧
    O.half SX 3 (O.neg SX doutM (O.net SX 17 F.pout
      (wht4G O (pinWG O (O.neg SX dinM (colxiG O SX 0 1 valW W)))))) < 2 ^ (np * SX) := by
  have h2 := two_hN (np := np) (by omega)
  have hn := (pout_lab hp).1
  have b0 := colW_bd hO hW3
  have b1 := hO.neg_bd dinM_lt b0
  have b2 : Bd np SX (pinWG O (O.neg SX dinM (colxiG O SX 0 1 valW W))) :=
    bd_dsw_rep hO mpin_valid b1
  have c5 := hO.bfly_bd (k := 17) (b := 5 + 0) SX_eq (by decide) valW_lt b2
  have c6 := hO.bfly_bd (k := 17) (b := 5 + 1) SX_eq (by decide) valW_lt c5
  have c7 := hO.bfly_bd (k := 17) (b := 5 + 2) SX_eq (by decide) valW_lt c6
  have c8 := hO.bfly_bd (k := 17) (b := 5 + 3) SX_eq (by decide) valW_lt c7
  have c8' : Bd np SX (wht4G O (pinWG O (O.neg SX dinM (colxiG O SX 0 1 valW W)))) := c8
  have b4 := hO.net_bd SX_eq hn c8'
  have b5 := hO.neg_bd doutM_lt b4
  let Y : ℕ → ℕ → ZMod (2 ^ np - 1) := fun r j => ∑ w ∈ Finset.range 4,
    ((c4z w (j % 4) : ℤ) : ZMod (2 ^ np - 1)) * resN np v (98580 + 24 * r + 4 * (j / 4) + w)
  refine ⟨fun r hr j hj => ?_, fun p hpS hpm => ?_, hO.half_bd (by decide) (by decide) b5⟩
  · have hH : r / 32 % 64 < 64 := Nat.mod_lt _ (by decide)
    have hk : r % 32 + 32 * (r / 2048) < 64 := by omega
    have hrr : rr (r / 32 % 64) (r % 32 + 32 * (r / 2048)) = r := by unfold rr; omega
    generalize r / 32 % 64 = H at hH hrr
    generalize r % 32 + 32 * (r / 2048) = k at hk hrr
    subst hrr
    have hP := pos_lt hH (by omega : j < 32) hk
    have rt := (rel_twin hO hp hW3 hH hj k hk).2
    dsimp only at rt
    rw [← pos_eq, hO.half_res (by decide) (by decide) b5 hP, rt]
    have tw : ∀ e ∈ Tl k, ((e.2 : ℤ) : ZMod (2 ^ np - 1)) *
        resPN np SX (colxiG O SX 0 1 valW W) (pos H j e.1) =
        ((e.2 : ℤ) : ZMod (2 ^ np - 1)) * Y (rr H e.1) j := by
      intro e he
      have he' := Tl_lt k hk e he
      congr 1
      rw [pos_eq, show 32 * rr H e.1 + j = 32 * rr H e.1 + 4 * (j / 4) + j % 4 by omega,
        colW01 hO hW3 (rr_lt hH he') (by omega) (Nat.mod_lt _ (by decide))]
      refine Finset.sum_congr rfl fun w hw => ?_
      have := Finset.mem_range.1 hw
      rw [Nat.add_assoc, hW1 _ (rr_lt hH he') _ (by omega), ← Nat.add_assoc]
    rw [List.map_congr_left tw]
    change _ = resM (hN np) (Native.applyGD (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) .xi) v)
      (98580 + 24 * rr H k + j)
    rw [Nat.add_assoc, applyGD_resW h2 _ _ _ (by have := rr_lt hH hk; omega)]
    have hG : (Native.GD.ofGen (Native.mkCtx ()) .xi).G = Native.xiG () := by
      simp only [Native.GD.ofGen]
    have hl : (Native.GD.ofGen (Native.mkCtx ()) .xi).latS + (Native.GD.ofGen (Native.mkCtx ()) .xi).rowS
        = 7 := by simp only [Native.GD.ofGen]
    rw [hG, hl]
    have inner : ∀ p ∈ Finset.range 98304,
        ((scat (Native.GD.ofGen (Native.mkCtx ()) .xi).wT p (24 * rr H k + j) : ℤ) : ZMod (2 ^ np - 1)) *
          ∑ j' ∈ Finset.range 24, (((Native.xiG ())[j' * 24 + p % 24]! : ℤ) : ZMod (2 ^ np - 1)) *
            resM (hN np) v (98580 + p / 24 * 24 + j') =
        ((scat (Native.GD.ofGen (Native.mkCtx ()) .xi).wT p (24 * rr H k + j) : ℤ) : ZMod (2 ^ np - 1)) *
          Y (p / 24) (p % 24) := by
      intro p _
      rw [blk_sum _ (Nat.mod_lt _ (by decide))]
      refine congrArg _ (Finset.sum_congr rfl fun w _ => ?_)
      rw [show 98580 + p / 24 * 24 + (4 * (p % 24 / 4) + w) =
        98580 + 24 * (p / 24) + 4 * (p % 24 / 4) + w by ring]
      rfl
    rw [Finset.sum_congr rfl inner, nat_sum Y hH hk hj]
    have h16 : (16 : ZMod (2 ^ np - 1)) * hN np ^ 4 = 1 := by
      rw [show (16 : ZMod (2 ^ np - 1)) * hN np ^ 4 = (2 * hN np) ^ 4 by ring, h2, one_pow]
    linear_combination (-(hN np ^ 3 * ((Tl k).map fun e => ((e.2 : ℤ) : ZMod (2 ^ np - 1)) *
      Y (rr H e.1) j).sum)) * h16
  ·
    obtain ⟨hπ, hπm⟩ := pout_col hp hpS
    set q := Benes.benesPerm 17 F.pout p with hq
    have hvq : valW.testBit q = false := by
      rw [testBit_valW]
      simp only [decide_eq_false_iff_not]
      omega
    have hs : Benes.swp 512 mpin q < SX ∧ Benes.swp 512 mpin q % 32 = q % 32 := by
      have hv := mpin_valid
      unfold Benes.swp
      split_ifs with h1 h2
      · have := (hv q h1).1
        exact ⟨this, by omega⟩
      · exact ⟨by omega, by omega⟩
      · exact ⟨hπ, rfl⟩
    have hvs : valW.testBit (Benes.swp 512 mpin q) = false := by
      rw [testBit_valW]
      simp only [decide_eq_false_iff_not]
      omega
    have z0 : resPN np SX (colxiG O SX 0 1 valW W) (Benes.swp 512 mpin q) = 0 := by
      rw [outW01 hO hW3 hs.1 hvs, hW2 _ hs.1 (by omega)]
    have z3 : resPN np SX (wht4G O (pinWG O (O.neg SX dinM (colxiG O SX 0 1 valW W)))) q = 0 := by
      rw [wht4G_eq, hO.bfly_res SX_eq (by decide) valW_lt clW8 c7 hπ, hvq, if_pos rfl,
        hO.bfly_res SX_eq (by decide) valW_lt clW7 c6 hπ, hvq, if_pos rfl,
        hO.bfly_res SX_eq (by decide) valW_lt clW6 c5 hπ, hvq, if_pos rfl,
        hO.bfly_res SX_eq (by decide) valW_lt clW5 b2 hπ, hvq, if_pos rfl, pinWG_eq,
        res_dsw_rep hO mpin_valid b1 hπ, hO.neg_res dinM_lt b0 hs.1, z0]
      simp
    rw [hO.half_res (by decide) (by decide) b5 hpS, hO.neg_res doutM_lt b4 hpS,
      hO.net_res SX_eq hn c8' hpS, ← hq, z3]
    simp

end XiAux

open XiAux

theorem xi_sound {np : ℕ} {O : POps} (hO : PLaw np O) (hnp : 2 ≤ np) {F : Fix} (hK : KeyBind F)
    (hG : KeysGood) (hx : xiOK F = true) (hp : poutOK F = true) {v : Native.DVec} {t : St}
    (ht : RepN np v t) (f : Bool) :
    RepN np (Native.applyGen (Native.mkCtx ()) .xi v) (f, xiG O F t.2.1 t.2.2.1 t.2.2.2) := by
  obtain ⟨hX1, hX2, hX3, hA1, hA2, hA3, hW1, hW2, hW3⟩ := ht
  obtain ⟨x1, x2, x3⟩ := xi_X hO hnp hK hG hx hX1 hX2 hX3
  obtain ⟨w1, w2, w3⟩ := xi_W hO hnp hp hW1 hW2 hW3
  refine ⟨x1, x2, x3, fun i hi j hj => ?_, fun p hp hv => ?_, xiG_bdA hO hA3, w1, w2, w3⟩
  · change resPN np SA (O.half SA 2 (colxiG O SA 5 6 valA (colxiG O SA 0 1 valA t.2.2.1)))
      (32 * i + j) = resM (hN np) _ _
    rw [xiG_resA hO hA3 hi hj, xi_resA (two_hN (by omega)) v hi hj]
    congr 1
    refine Finset.sum_congr rfl fun w' hw' => ?_
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    have := Finset.mem_range.1 hw
    have := Finset.mem_range.1 hw'
    rw [hA1 _ (by omega) _ (by omega)]
    rfl
  · exact xiG_resA_zero hO hA3 hp hv (hA2 p hp hv)

end CFSG.KC.KStep

end
