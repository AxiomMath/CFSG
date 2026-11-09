module

public import CFSG.Certificates.Kernel.KStep.Xi
public import CFSG.Certificates.Kernel.BenesRev
public import Certificates.Data.Kernel.KDenseP.XiInvStep
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.KC.KStep

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP
open CFSG.Monster.AxisCount CFSG.Monster.B.Rep4371.Native CFSG.KC.MonsterConv.Perm

@[expose] noncomputable def colxiTG (O : POps) (S b0 b1 R x : Nat) : Nat :=
  O.neg S (Nat.land R (Nat.land (clr S b0) (clr S b1)))
    (O.bfly S b0 R (O.bfly S b1 R
      (dsw (Nat.sub (Nat.shiftLeft (nat_lit 1) b1) (Nat.shiftLeft (nat_lit 1) b0))
        (O.rep S (Nat.land R (Nat.land (idPlane S b0) (clr S b1)))) x)))

@[expose] noncomputable def xiInvG (O : POps) (F : Fix) (XN PN : Nat) (X A W : Nat) :
    Nat × Nat × Nat :=
  (O.neg SX F.xiSgn (O.net SX (nat_lit 17) XN X),
    O.half SA (nat_lit 2) (colxiTG O SA (nat_lit 5) (nat_lit 6) valA (colxiTG O SA (nat_lit 0) (nat_lit 1) valA A)),
    O.half SX (nat_lit 3) (colxiTG O SX (nat_lit 0) (nat_lit 1) valW (O.neg SX dinM
      (pinWG O (wht4G O (O.net SX (nat_lit 17) PN (O.neg SX doutM W)))))))

theorem xiInvStepN_eq (n lg : ℕ) (F : Fix) (XN PN X A W : Nat) :
    xiInvStepN n lg F XN PN X A W = xiInvG (opsN n lg) F XN PN X A W :=
  rfl

namespace XiInvAux

open XiAux

variable {np : ℕ} {O : POps}

theorem colxiTG_eq (S b0 b1 R x : ℕ) : colxiTG O S b0 b1 R x =
    O.neg S (m0 S b0 b1 R) (O.bfly S b0 R (O.bfly S b1 R
      (dsw (2 ^ b1 - 2 ^ b0) (O.rep S (m1 S b0 b1 R)) x))) := by
  unfold colxiTG m0 m1
  simp only [Benes.nsub, Benes.nshl, Nat.one_shiftLeft]

theorem blk4T (hO : PLaw np O) {k S b0 b1 R d M0 M1 x : ℕ} (hS : S = 2 ^ k) (hb0 : b0 < k)
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
    ∀ u < 4, resPN np S (O.neg S M0 (O.bfly S b0 R (O.bfly S b1 R (dsw d (O.rep S M1) x)))) (P u) =
      ∑ w ∈ Finset.range 4, ((c4z u w : ℤ) : ZMod (2 ^ np - 1)) * resPN np S x (P w) := by
  have y0b := bd_dsw_rep hO hv hx
  have y1b := hO.bfly_bd hS hb1 hR y0b
  have y2b := hO.bfly_bd hS hb0 hR y1b
  have key : ∀ D0 D1 a0 a1 a2 a3 : ℕ, a1 = a0 + D0 → a2 = a0 + D1 → a3 = a0 + D0 + D1 → a3 < S →
      (a0 < S ∧ a1 < S ∧ a2 < S) ∧ (a1 - D0 = a0 ∧ a2 - D1 = a0 ∧ a3 - D1 = a1 ∧ a3 - D0 = a2) ∧
      (a0 + D0 = a1 ∧ a0 + D1 = a2 ∧ a1 + D1 = a3 ∧ a2 + D0 = a3) := by
    intros
    omega
  obtain ⟨⟨lt0, lt1, lt2⟩, ⟨q1, q2, q3, q3'⟩, ⟨q0, q0', q1', q2'⟩⟩ :=
    key (2 ^ b0) (2 ^ b1) (P 0) (P 1) (P 2) (P 3) e1 e2 e3 hP
  have d0 := res_dsw_rep hO hv hx lt0
  have d1 := res_dsw_rep hO hv hx lt1
  have d2 := res_dsw_rep hO hv hx lt2
  have d3 := res_dsw_rep hO hv hx hP
  rw [s0] at d0
  rw [s1] at d1
  rw [s2] at d2
  rw [s3] at d3
  have a0 := hO.bfly_res (x := dsw d (O.rep S M1) x) hS hb1 hR hc1 y0b lt0
  have a1 := hO.bfly_res (x := dsw d (O.rep S M1) x) hS hb1 hR hc1 y0b lt1
  have a2 := hO.bfly_res (x := dsw d (O.rep S M1) x) hS hb1 hR hc1 y0b lt2
  have a3 := hO.bfly_res (x := dsw d (O.rep S M1) x) hS hb1 hR hc1 y0b hP
  rw [r0, t01, q0'] at a0
  rw [r1, t11, q1'] at a1
  rw [r2, t21, q2, r0] at a2
  rw [r3, t31, q3, r1] at a3
  simp only [ite_true, ite_false, Bool.true_eq_false] at a0 a1 a2 a3
  have b0' := hO.bfly_res (x := O.bfly S b1 R (dsw d (O.rep S M1) x)) hS hb0 hR hc0 y1b lt0
  have b1' := hO.bfly_res (x := O.bfly S b1 R (dsw d (O.rep S M1) x)) hS hb0 hR hc0 y1b lt1
  have b2' := hO.bfly_res (x := O.bfly S b1 R (dsw d (O.rep S M1) x)) hS hb0 hR hc0 y1b lt2
  have b3' := hO.bfly_res (x := O.bfly S b1 R (dsw d (O.rep S M1) x)) hS hb0 hR hc0 y1b hP
  rw [r0, t00, q0] at b0'
  rw [r1, t10, q1, r0] at b1'
  rw [r2, t20, q2'] at b2'
  rw [r3, t30, q3', r2] at b3'
  simp only [ite_true, ite_false, Bool.true_eq_false] at b0' b1' b2' b3'
  intro u hu
  interval_cases u
  · rw [hO.neg_res hM0 y2b lt0, n0, b0', a0, a1, d0, d1, d2, d3]
    simp [Finset.sum_range_succ, c4z, c4N]
    ring
  · rw [hO.neg_res hM0 y2b lt1, n1, b1', a0, a1, d0, d1, d2, d3]
    simp [Finset.sum_range_succ, c4z, c4N]
    ring
  · rw [hO.neg_res hM0 y2b lt2, n2, b2', a2, a3, d0, d1, d2, d3]
    simp [Finset.sum_range_succ, c4z, c4N]
    ring
  · rw [hO.neg_res hM0 y2b hP, n3, b3', a2, a3, d0, d1, d2, d3]
    simp [Finset.sum_range_succ, c4z, c4N]
    ring

theorem blk_outT (hO : PLaw np O) {k S b0 b1 R d M0 M1 x p : ℕ} (hS : S = 2 ^ k) (hb0 : b0 < k)
    (hb1 : b1 < k) (hR : R < 2 ^ S) (hc0 : Cl S R b0) (hc1 : Cl S R b1) (hM0 : M0 < 2 ^ S)
    (hv : Benes.ValidIn S d M1) (hx : Bd np S x) (hp : p < S) (hr : R.testBit p = false)
    (hs : Benes.swp d M1 p = p) (hn : M0.testBit p = false) :
    resPN np S (O.neg S M0 (O.bfly S b0 R (O.bfly S b1 R (dsw d (O.rep S M1) x)))) p =
      resPN np S x p := by
  have y0b := bd_dsw_rep hO hv hx
  have y1b := hO.bfly_bd hS hb1 hR y0b
  have y2b := hO.bfly_bd hS hb0 hR y1b
  rw [hO.neg_res hM0 y2b hp, hn, hO.bfly_res hS hb0 hR hc0 y1b hp, hr,
    hO.bfly_res hS hb1 hR hc1 y0b hp, hr, res_dsw_rep hO hv hx hp, hs]
  simp

theorem colxiT_bd (hO : PLaw np O) {k S b0 b1 R d M0 M1 x : ℕ} (hS : S = 2 ^ k) (hb0 : b0 < k)
    (hb1 : b1 < k) (hR : R < 2 ^ S) (hM0 : M0 < 2 ^ S) (hv : Benes.ValidIn S d M1)
    (hx : Bd np S x) :
    Bd np S (O.neg S M0 (O.bfly S b0 R (O.bfly S b1 R (dsw d (O.rep S M1) x)))) :=
  hO.neg_bd hM0 (hO.bfly_bd hS hb0 hR (hO.bfly_bd hS hb1 hR (bd_dsw_rep hO hv hx)))

theorem colA01T (hO : PLaw np O) {x : ℕ} (hx : Bd np SA x) {i J u : ℕ} (hi : i < 24) (hJ : J < 6)
    (hu : u < 4) :
    resPN np SA (colxiTG O SA 0 1 valA x) (32 * i + 4 * J + u) =
      ∑ w ∈ Finset.range 4, ((c4z u w : ℤ) : ZMod (2 ^ np - 1)) *
        resPN np SA x (32 * i + 4 * J + w) := by
  rw [colxiTG_eq]
  exact blk4T hO (k := 10) SA_eq (by decide) (by decide) valA_lt clA0 clA1 m0A01_lt vA01
    hx (fun u => 32 * i + 4 * J + u) (by simp) (by simp) (by simp) (by barith)
    (by barith) (by barith) (by barith) (by barith) (by barith) (by barith) (by barith) (by barith)
    (by barith) (by barith) (by barith) (by barith)
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (by barith) (by barith) (by barith) (by barith) u hu

theorem colA56T (hO : PLaw np O) {x : ℕ} (hx : Bd np SA x) {I j u : ℕ} (hI : I < 6) (hj : j < 24)
    (hu : u < 4) :
    resPN np SA (colxiTG O SA 5 6 valA x) (32 * (4 * I + u) + j) =
      ∑ w ∈ Finset.range 4, ((c4z u w : ℤ) : ZMod (2 ^ np - 1)) *
        resPN np SA x (32 * (4 * I + w) + j) := by
  rw [colxiTG_eq]
  exact blk4T hO (k := 10) SA_eq (by decide) (by decide) valA_lt clA5 clA6 m0A56_lt vA56
    hx (fun u => 32 * (4 * I + u) + j) (by simp; omega) (by simp; omega)
    (by simp; omega) (by barith)
    (by barith) (by barith) (by barith) (by barith) (by barith) (by barith) (by barith) (by barith)
    (by barith) (by barith) (by barith) (by barith)
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (by barith) (by barith) (by barith) (by barith) u hu

theorem colW01T (hO : PLaw np O) {x : ℕ} (hx : Bd np SX x) {r J u : ℕ} (hr : r < 4096) (hJ : J < 6)
    (hu : u < 4) :
    resPN np SX (colxiTG O SX 0 1 valW x) (32 * r + 4 * J + u) =
      ∑ w ∈ Finset.range 4, ((c4z u w : ℤ) : ZMod (2 ^ np - 1)) *
        resPN np SX x (32 * r + 4 * J + w) := by
  rw [colxiTG_eq]
  exact blk4T hO (k := 17) SX_eq (by decide) (by decide) valW_lt clW0 clW1 m0W01_lt vW01
    hx (fun u => 32 * r + 4 * J + u) (by simp) (by simp) (by simp) (by barith)
    (by barith) (by barith) (by barith) (by barith) (by barith) (by barith) (by barith) (by barith)
    (by barith) (by barith) (by barith) (by barith)
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith))
    (by barith) (by barith) (by barith) (by barith) u hu

theorem outA01T (hO : PLaw np O) {x p : ℕ} (hx : Bd np SA x) (hp : p < SA)
    (hr : valA.testBit p = false) : resPN np SA (colxiTG O SA 0 1 valA x) p = resPN np SA x p := by
  rw [colxiTG_eq]
  exact blk_outT hO (k := 10) SA_eq (by decide) (by decide) valA_lt clA0 clA1 m0A01_lt vA01 hx hp hr
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith)) (by barith)

theorem outA56T (hO : PLaw np O) {x p : ℕ} (hx : Bd np SA x) (hp : p < SA)
    (hr : valA.testBit p = false) : resPN np SA (colxiTG O SA 5 6 valA x) p = resPN np SA x p := by
  rw [colxiTG_eq]
  exact blk_outT hO (k := 10) SA_eq (by decide) (by decide) valA_lt clA5 clA6 m0A56_lt vA56 hx hp hr
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith)) (by barith)

theorem outW01T (hO : PLaw np O) {x p : ℕ} (hx : Bd np SX x) (hp : p < SX)
    (hr : valW.testBit p = false) : resPN np SX (colxiTG O SX 0 1 valW x) p = resPN np SX x p := by
  rw [colxiTG_eq]
  exact blk_outT hO (k := 17) SX_eq (by decide) (by decide) valW_lt clW0 clW1 m0W01_lt vW01 hx hp hr
    (swp_eq (fun h1 => by barith) (fun h1 h2 => by barith) (fun h1 h2 => by barith)) (by barith)

theorem colAT_bd (hO : PLaw np O) {b0 b1 x : ℕ} (hb0 : b0 < 10) (hb1 : b1 < 10)
    (hv : Benes.ValidIn SA (2 ^ b1 - 2 ^ b0) (m1 SA b0 b1 valA)) (hm : m0 SA b0 b1 valA < 2 ^ SA)
    (hx : Bd np SA x) : Bd np SA (colxiTG O SA b0 b1 valA x) := by
  rw [colxiTG_eq]
  exact colxiT_bd hO SA_eq hb0 hb1 valA_lt hm hv hx

theorem colWT_bd (hO : PLaw np O) {x : ℕ} (hx : Bd np SX x) : Bd np SX (colxiTG O SX 0 1 valW x) := by
  rw [colxiTG_eq]
  exact colxiT_bd hO SX_eq (by decide) (by decide) valW_lt m0W01_lt vW01 hx

theorem xiInvG_resA (hO : PLaw np O) {A : ℕ} (hA : Bd np SA A) {i j : ℕ} (hi : i < 24) (hj : j < 24) :
    resPN np SA (O.half SA 2 (colxiTG O SA 5 6 valA (colxiTG O SA 0 1 valA A))) (32 * i + j) =
      hN np ^ 2 * ∑ w' ∈ Finset.range 4, ((c4z (i % 4) w' : ℤ) : ZMod (2 ^ np - 1)) *
        ∑ w ∈ Finset.range 4, ((c4z (j % 4) w : ℤ) : ZMod (2 ^ np - 1)) *
          resPN np SA A (32 * (4 * (i / 4) + w') + (4 * (j / 4) + w)) := by
  have hB := colAT_bd hO (by decide) (by decide) vA01 m0A01_lt hA
  have hC := colAT_bd hO (by decide) (by decide) vA56 m0A56_lt hB
  rw [hO.half_res (by decide) (by decide) hC (by rw [SA_1024]; omega)]
  congr 1
  have e : 32 * i + j = 32 * (4 * (i / 4) + i % 4) + j := by omega
  rw [e, colA56T hO hB (by omega) hj (Nat.mod_lt _ (by decide))]
  refine Finset.sum_congr rfl fun w' hw' => ?_
  have := Finset.mem_range.1 hw'
  congr 1
  have e2 : 32 * (4 * (i / 4) + w') + j = 32 * (4 * (i / 4) + w') + 4 * (j / 4) + j % 4 := by omega
  rw [e2, colA01T hO hA (by omega) (by omega) (Nat.mod_lt _ (by decide))]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Nat.add_assoc]

theorem xiInvG_resA_zero (hO : PLaw np O) {A : ℕ} (hA : Bd np SA A) {p : ℕ} (hp : p < SA)
    (hv : 24 ≤ p % 32 ∨ 24 ≤ p / 32) (hz : resPN np SA A p = 0) :
    resPN np SA (O.half SA 2 (colxiTG O SA 5 6 valA (colxiTG O SA 0 1 valA A))) p = 0 := by
  have hB := colAT_bd hO (by decide) (by decide) vA01 m0A01_lt hA
  have hC := colAT_bd hO (by decide) (by decide) vA56 m0A56_lt hB
  have hr : valA.testBit p = false := by
    rw [testBit_valA]
    simp only [decide_eq_false_iff_not]
    omega
  rw [hO.half_res (by decide) (by decide) hC hp, outA56T hO hB hp hr, outA01T hO hA hp hr, hz,
    mul_zero]

theorem xiInvG_bdA (hO : PLaw np O) {A : ℕ} (hA : Bd np SA A) :
    Bd np SA (O.half SA 2 (colxiTG O SA 5 6 valA (colxiTG O SA 0 1 valA A))) :=
  hO.half_bd (by decide) (by decide)
    (colAT_bd hO (by decide) (by decide) vA56 m0A56_lt (colAT_bd hO (by decide) (by decide) vA01 m0A01_lt hA))

theorem c4_sq {M u : ℕ} (hu : u < 4) (f : ℕ → ZMod M) :
    ∑ w ∈ Finset.range 4, ((c4z w u : ℤ) : ZMod M) * ∑ a ∈ Finset.range 4, ((c4z a w : ℤ) : ZMod M) * f a =
      2 * ∑ a ∈ Finset.range 4, ((c4z u a : ℤ) : ZMod M) * f a := by
  interval_cases u <;> simp [Finset.sum_range_succ, c4z, c4N] <;> ring

theorem sum4_swap {M : ℕ} (cw ca : ℕ → ZMod M) (g : ℕ → ℕ → ZMod M) :
    ∑ w ∈ Finset.range 4, cw w * ∑ a ∈ Finset.range 4, ca a * g a w =
      ∑ a ∈ Finset.range 4, ca a * ∑ w ∈ Finset.range 4, cw w * g a w := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem xi2_resA {M : ℕ} {h : ZMod M} (h2 : 2 * h = 1) (v : Native.DVec) {i j : ℕ} (hi : i < 24)
    (hj : j < 24) :
    resM h (Native.applyGen (Native.mkCtx ()) .xi (Native.applyGen (Native.mkCtx ()) .xi v))
        (Native.aIdx i j) = h ^ 2 *
      ∑ w' ∈ Finset.range 4, ((c4z (i % 4) w' : ℤ) : ZMod M) * ∑ w ∈ Finset.range 4,
        ((c4z (j % 4) w : ℤ) : ZMod M) * resM h v (Native.aIdx (4 * (i / 4) + w') (4 * (j / 4) + w)) := by
  rw [xi_resA h2 _ hi hj]
  have e1 : ∀ w' ∈ Finset.range 4, ((c4z w' (i % 4) : ℤ) : ZMod M) * ∑ w ∈ Finset.range 4,
      ((c4z w (j % 4) : ℤ) : ZMod M) *
        resM h (Native.applyGen (Native.mkCtx ()) .xi v) (Native.aIdx (4 * (i / 4) + w') (4 * (j / 4) + w)) =
      h ^ 2 * (((c4z w' (i % 4) : ℤ) : ZMod M) * ∑ a ∈ Finset.range 4, ((c4z a w' : ℤ) : ZMod M) *
        (2 * ∑ b ∈ Finset.range 4, ((c4z (j % 4) b : ℤ) : ZMod M) *
          resM h v (Native.aIdx (4 * (i / 4) + a) (4 * (j / 4) + b)))) := by
    intro w' hw'
    have hw'' := Finset.mem_range.1 hw'
    have e2 : ∀ w ∈ Finset.range 4, ((c4z w (j % 4) : ℤ) : ZMod M) *
        resM h (Native.applyGen (Native.mkCtx ()) .xi v) (Native.aIdx (4 * (i / 4) + w') (4 * (j / 4) + w)) =
        h ^ 2 * (((c4z w (j % 4) : ℤ) : ZMod M) * ∑ a ∈ Finset.range 4, ((c4z a w' : ℤ) : ZMod M) *
          ∑ b ∈ Finset.range 4, ((c4z b w : ℤ) : ZMod M) *
            resM h v (Native.aIdx (4 * (i / 4) + a) (4 * (j / 4) + b))) := by
      intro w hw
      have hw2 := Finset.mem_range.1 hw
      rw [xi_resA h2 v (by omega) (by omega)]
      have m1 : (4 * (i / 4) + w') % 4 = w' := by omega
      have m2 : (4 * (i / 4) + w') / 4 = i / 4 := by omega
      have m3 : (4 * (j / 4) + w) % 4 = w := by omega
      have m4 : (4 * (j / 4) + w) / 4 = j / 4 := by omega
      rw [m1, m2, m3, m4]
      ring
    rw [Finset.sum_congr rfl e2, ← Finset.mul_sum, sum4_swap (fun w => ((c4z w (j % 4) : ℤ) : ZMod M))
      (fun a => ((c4z a w' : ℤ) : ZMod M)) (fun a w => ∑ b ∈ Finset.range 4, ((c4z b w : ℤ) : ZMod M) *
        resM h v (Native.aIdx (4 * (i / 4) + a) (4 * (j / 4) + b)))]
    have e3 : ∀ a ∈ Finset.range 4, ((c4z a w' : ℤ) : ZMod M) * ∑ w ∈ Finset.range 4,
        ((c4z w (j % 4) : ℤ) : ZMod M) * ∑ b ∈ Finset.range 4, ((c4z b w : ℤ) : ZMod M) *
          resM h v (Native.aIdx (4 * (i / 4) + a) (4 * (j / 4) + b)) =
        ((c4z a w' : ℤ) : ZMod M) * (2 * ∑ b ∈ Finset.range 4, ((c4z (j % 4) b : ℤ) : ZMod M) *
          resM h v (Native.aIdx (4 * (i / 4) + a) (4 * (j / 4) + b))) := fun a _ => by
      rw [c4_sq (Nat.mod_lt _ (by decide))]
    rw [Finset.sum_congr rfl e3]
    ring
  rw [Finset.sum_congr rfl e1, ← Finset.mul_sum,
    c4_sq (Nat.mod_lt _ (by decide)) (fun a => 2 * ∑ b ∈ Finset.range 4, ((c4z (j % 4) b : ℤ) : ZMod M) *
      resM h v (Native.aIdx (4 * (i / 4) + a) (4 * (j / 4) + b)))]
  have e4 : ∀ G : ℕ → ZMod M, ∑ a ∈ Finset.range 4, ((c4z (i % 4) a : ℤ) : ZMod M) * (2 * G a) =
      2 * ∑ a ∈ Finset.range 4, ((c4z (i % 4) a : ℤ) : ZMod M) * G a := fun G => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e4]
  linear_combination (h ^ 2 * (2 * h + 1) * ∑ a ∈ Finset.range 4, ((c4z (i % 4) a : ℤ) : ZMod M) *
    ∑ b ∈ Finset.range 4, ((c4z (j % 4) b : ℤ) : ZMod M) *
      resM h v (Native.aIdx (4 * (i / 4) + a) (4 * (j / 4) + b))) * h2

theorem xiInv_A (hO : PLaw np O) (hnp : 2 ≤ np) {v : Native.DVec} {A : ℕ}
    (hA1 : ∀ i < 24, ∀ j < 24, resPN np SA A (32 * i + j) = resN np v (Native.aIdx i j))
    (hA3 : Bd np SA A) {i j : ℕ} (hi : i < 24) (hj : j < 24) :
    resPN np SA (O.half SA 2 (colxiTG O SA 5 6 valA (colxiTG O SA 0 1 valA A))) (32 * i + j) =
      resN np (Native.applyGen (Native.mkCtx ()) .xi (Native.applyGen (Native.mkCtx ()) .xi v))
        (Native.aIdx i j) := by
  change _ = resM (hN np) _ _
  rw [xiInvG_resA hO hA3 hi hj, xi2_resA (two_hN (by omega)) v hi hj]
  congr 1
  refine Finset.sum_congr rfl fun w' hw' => ?_
  congr 1
  refine Finset.sum_congr rfl fun w hw => ?_
  have := Finset.mem_range.1 hw
  have := Finset.mem_range.1 hw'
  rw [hA1 _ (by omega) _ (by omega)]
  rfl

@[expose] def xiLow (l : ℕ × ℕ) : ℕ × ℕ :=
  (gammaLowN l.2, gammaLowN l.1 ^^^ gammaLowN (gammaLowN l.2))

theorem xiLow_cube : ∀ a < 64, ∀ d < 64, xiLow (xiLow (xiLow (a, d))) = (a, d) := by
  decide +kernel

theorem xs_xiLow : ∀ a < 64, ∀ d < 64,
    (xs a d ^^ xs (xiLow (a, d)).1 (xiLow (a, d)).2 ^^
      xs (xiLow (xiLow (a, d))).1 (xiLow (xiLow (a, d))).2) = false := by
  decide +kernel

theorem tb_ge6 {x i : ℕ} (hx : x < 64) (hi : ¬ i < 6) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx
    (Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 6 ≤ i)))

theorem tb_mod64 (x i : ℕ) : (x % 64).testBit i = (decide (i < 6) && x.testBit i) :=
  Nat.testBit_mod_two_pow x 6 i

theorem xa_low (a d : ℕ) : xa a d % 64 = gammaLowN (d % 64) := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold xa
  simp only [tb_mod64, Nat.testBit_xor, Nat.testBit_and, t4032']
  by_cases hi : i < 6
  · simp [hi, show ¬ 6 ≤ i by omega]
  · rw [tb_ge6 (gammaLowN_lt _) hi]
    simp [hi]

theorem xa_hi (a d : ℕ) : xa a d &&& 4032 = a &&& 4032 := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold xa
  simp only [Nat.testBit_xor, Nat.testBit_and, t4032']
  by_cases hi : i < 6
  · simp [show ¬ 6 ≤ i by omega]
  · rw [tb_ge6 (gammaLowN_lt _) hi]
    simp

theorem xd_low (a d : ℕ) : xd a d % 64 = gammaLowN (a % 64) ^^^ gammaLowN (gammaLowN (d % 64)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold xd
  simp only [tb_mod64, Nat.testBit_xor, Nat.testBit_and, t4032']
  by_cases hi : i < 6
  · simp [hi, show ¬ 6 ≤ i by omega]
  · rw [tb_ge6 (gammaLowN_lt _) hi, tb_ge6 (gammaLowN_lt _) hi]
    simp [hi]

theorem xd_hi (a d : ℕ) : xd a d &&& 4032 = d &&& 4032 := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold xd
  simp only [Nat.testBit_xor, Nat.testBit_and, t4032']
  by_cases hi : i < 6
  · simp [show ¬ 6 ≤ i by omega]
  · rw [tb_ge6 (gammaLowN_lt _) hi, tb_ge6 (gammaLowN_lt _) hi]
    simp

theorem xad_low (a d : ℕ) : (xa a d % 64, xd a d % 64) = xiLow (a % 64, d % 64) := by
  rw [xa_low, xd_low]
  rfl

theorem eq_of_low_hi {x y : ℕ} (hx : x < 4096) (hy : y < 4096) (h1 : x % 64 = y % 64)
    (h2 : x &&& 4032 = y &&& 4032) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · have := congrArg (fun z => z.testBit i) h1
    simpa [tb_mod64, hi] using this
  · by_cases hi2 : i < 12
    · have := congrArg (fun z => z.testBit i) h2
      simp only [Nat.testBit_and, t4032'] at this
      simpa [show 6 ≤ i by omega, hi2] using this
    · have hle : 2 ^ 12 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx hle),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy hle)]

@[expose] def xiKey (k : ℕ × ℕ) : ℕ × ℕ := (xa k.1 k.2, xd k.1 k.2)

theorem xiKey_low (k : ℕ × ℕ) : ((xiKey k).1 % 64, (xiKey k).2 % 64) = xiLow (k.1 % 64, k.2 % 64) :=
  xad_low _ _

theorem xiLow_lt (l : ℕ × ℕ) : (xiLow l).1 < 64 ∧ (xiLow l).2 < 64 :=
  ⟨gammaLowN_lt _, Nat.xor_lt_two_pow (n := 6) (gammaLowN_lt _) (gammaLowN_lt _)⟩

theorem xiKey_cube {k : ℕ × ℕ} (h1 : k.1 < 4096) (h2 : k.2 < 4096) : xiKey (xiKey (xiKey k)) = k := by
  have lo : ∀ k : ℕ × ℕ, ((xiKey k).1 % 64, (xiKey k).2 % 64) = xiLow (k.1 % 64, k.2 % 64) := xiKey_low
  have l3 := lo (xiKey (xiKey k))
  rw [lo (xiKey k), lo k, xiLow_cube _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide))] at l3
  have e1 : (xiKey (xiKey (xiKey k))).1 = k.1 := by
    refine eq_of_low_hi (xa_lt _ _) h1 (congrArg Prod.fst l3) ?_
    change xa _ _ &&& 4032 = _
    rw [xa_hi]
    change xa _ _ &&& 4032 = _
    rw [xa_hi]
    change xa _ _ &&& 4032 = _
    rw [xa_hi]
  have e2 : (xiKey (xiKey (xiKey k))).2 = k.2 := by
    refine eq_of_low_hi (xd_lt _ _) h2 (congrArg Prod.snd l3) ?_
    change xd _ _ &&& 4032 = _
    rw [xd_hi]
    change xd _ _ &&& 4032 = _
    rw [xd_hi]
    change xd _ _ &&& 4032 = _
    rw [xd_hi]
  exact Prod.ext e1 e2

theorem xs_mod (a d : ℕ) : xs a d = xs (a % 64) (d % 64) := by
  simp only [xs, Nat.mod_mod]

theorem xs_xiKey (k : ℕ × ℕ) :
    (xs k.1 k.2 ^^ xs (xiKey k).1 (xiKey k).2 ^^ xs (xiKey (xiKey k)).1 (xiKey (xiKey k)).2) = false := by
  have lo : ∀ k : ℕ × ℕ, ((xiKey k).1 % 64, (xiKey k).2 % 64) = xiLow (k.1 % 64, k.2 % 64) := xiKey_low
  have l1 := lo k
  have l2 := lo (xiKey k)
  rw [l1] at l2
  have a1 : (xiKey k).1 % 64 = (xiLow (k.1 % 64, k.2 % 64)).1 := congrArg Prod.fst l1
  have b1 : (xiKey k).2 % 64 = (xiLow (k.1 % 64, k.2 % 64)).2 := congrArg Prod.snd l1
  have a2 : (xiKey (xiKey k)).1 % 64 = (xiLow (xiLow (k.1 % 64, k.2 % 64))).1 := congrArg Prod.fst l2
  have b2 : (xiKey (xiKey k)).2 % 64 = (xiLow (xiLow (k.1 % 64, k.2 % 64))).2 := congrArg Prod.snd l2
  rw [xs_mod k.1, xs_mod (xiKey k).1, xs_mod (xiKey (xiKey k)).1, a1, b1, a2, b2]
  exact xs_xiLow _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide))

theorem xiSgn_orbit {F : Fix} (hx : xiOK F = true) (hla : F.keyA < 2 ^ (12 * SX)) {r : ℕ}
    (hr : r < SX) :
    F.xiSgn.testBit r = (F.xiSgn.testBit (Benes.benesPerm 17 F.xiNet r) ^^
      F.xiSgn.testBit (Benes.benesPerm 17 F.xiNet (Benes.benesPerm 17 F.xiNet r))) := by
  obtain ⟨h1, a0, d0, s0⟩ := xi_lab hx hla hr
  obtain ⟨h2, a1, d1, s1⟩ := xi_lab hx hla h1
  have s2 := (xi_lab hx hla h2).2.2.2
  set k : ℕ × ℕ := (kv F.keyA (Benes.benesPerm 17 F.xiNet (Benes.benesPerm 17 F.xiNet r)),
    kv F.keyD (Benes.benesPerm 17 F.xiNet (Benes.benesPerm 17 F.xiNet r))) with hk
  have k1 : (kv F.keyA (Benes.benesPerm 17 F.xiNet r), kv F.keyD (Benes.benesPerm 17 F.xiNet r)) =
      xiKey k := Prod.ext a1 d1
  have k0 : (kv F.keyA r, kv F.keyD r) = xiKey (xiKey k) := by
    rw [← k1]
    exact Prod.ext a0 d0
  have e0 : F.xiSgn.testBit r = xs (xiKey (xiKey k)).1 (xiKey (xiKey k)).2 := by
    rw [s0, ← k0]
  have e1 : F.xiSgn.testBit (Benes.benesPerm 17 F.xiNet r) = xs (xiKey k).1 (xiKey k).2 := by
    rw [s1, ← k1]
  have e2 : F.xiSgn.testBit (Benes.benesPerm 17 F.xiNet (Benes.benesPerm 17 F.xiNet r)) =
      xs k.1 k.2 := s2
  have hp := xs_xiKey k
  rw [e0, e1, e2]
  revert hp
  cases xs k.1 k.2 <;> cases xs (xiKey k).1 (xiKey k).2 <;>
    cases xs (xiKey (xiKey k)).1 (xiKey (xiKey k)).2 <;> decide

theorem xiNet_cube {F : Fix} (hK : KeyBind F) (hG : KeysGood) (hx : xiOK F = true) {q : ℕ}
    (hq : q < 98280) :
    Benes.benesPerm 17 F.xiNet (Benes.benesPerm 17 F.xiNet (Benes.benesPerm 17 F.xiNet (xposK q))) =
      xposK q := by
  have hP := InitAux.xposK_lt' hq
  obtain ⟨h1, a0, d0, -⟩ := xi_lab hx hK.la hP
  obtain ⟨h2, a1, d1, -⟩ := xi_lab hx hK.la h1
  obtain ⟨h3, a2, d2, -⟩ := xi_lab hx hK.la h2
  set R := Benes.benesPerm 17 F.xiNet (Benes.benesPerm 17 F.xiNet (Benes.benesPerm 17 F.xiNet (xposK q)))
    with hR
  have k2 : (kv F.keyA (Benes.benesPerm 17 F.xiNet (Benes.benesPerm 17 F.xiNet (xposK q))),
      kv F.keyD (Benes.benesPerm 17 F.xiNet (Benes.benesPerm 17 F.xiNet (xposK q)))) =
      xiKey (kv F.keyA R, kv F.keyD R) := Prod.ext a2 d2
  have k1 : (kv F.keyA (Benes.benesPerm 17 F.xiNet (xposK q)),
      kv F.keyD (Benes.benesPerm 17 F.xiNet (xposK q))) =
      xiKey (xiKey (kv F.keyA R, kv F.keyD R)) := by
    rw [← k2]
    exact Prod.ext a1 d1
  have k0 : (kv F.keyA (xposK q), kv F.keyD (xposK q)) =
      xiKey (xiKey (xiKey (kv F.keyA R, kv F.keyD R))) := by
    rw [← k1]
    exact Prod.ext a0 d0
  rw [xiKey_cube (kv_lt _ _) (kv_lt _ _)] at k0
  have kq : (kv F.keyA (xposK q), kv F.keyD (xposK q)) = keyQ q :=
    Prod.ext (kv_eq (hK.ka q hq) (hG.1 q hq).1) (kv_eq (hK.kd q hq) (hG.1 q hq).2)
  by_cases hex : ∃ p < 98280, xposK p = R
  · obtain ⟨p, hp, e⟩ := hex
    have kp : (kv F.keyA (xposK p), kv F.keyD (xposK p)) = keyQ p :=
      Prod.ext (kv_eq (hK.ka p hp) (hG.1 p hp).1) (kv_eq (hK.kd p hp) (hG.1 p hp).2)
    rw [← e, kp, kq] at k0
    rw [← e, hG.2 p hp q hq k0.symm]
  · exfalso
    have hno : ∀ p < 98280, xposK p ≠ R := fun p hp e => hex ⟨p, hp, e⟩
    have z1 : kv F.keyA R = 0 :=
      kv_eq (fun b hb => by rw [hK.pa R h3 hno b hb, Nat.zero_testBit]) (by decide)
    have z2 : kv F.keyD R = 0 :=
      kv_eq (fun b hb => by rw [hK.pd R h3 hno b hb, Nat.zero_testBit]) (by decide)
    rw [z1, z2, kq] at k0
    exact keyQ_ne_zero hq k0

theorem xiInv_X (hO : PLaw np O) (hnp : 2 ≤ np) {F : Fix} (hK : KeyBind F) (hG : KeysGood)
    (hx : xiOK F = true) {XN : ℕ} (hXN : netOK 17 XN = true)
    (hXI : ∀ r < SX, Benes.benesPerm 17 XN r = Benes.benesInv 17 F.xiNet r) {v : Native.DVec} {X : ℕ}
    (hX1 : ∀ q < 98280, resPN np SX X (xposK q) = resN np v (300 + q))
    (hX2 : ∀ p < SX, (∀ q < 98280, xposK q ≠ p) → resPN np SX X p = 0) (hX3 : X < 2 ^ (np * SX)) :
    (∀ q < 98280, resPN np SX (O.neg SX F.xiSgn (O.net SX 17 XN X)) (xposK q) =
      resN np (Native.applyGen (Native.mkCtx ()) .xi (Native.applyGen (Native.mkCtx ()) .xi v))
        (300 + q)) ∧
    (∀ p < SX, (∀ q < 98280, xposK q ≠ p) → resPN np SX (O.neg SX F.xiSgn (O.net SX 17 XN X)) p = 0) ∧
    O.neg SX F.xiSgn (O.net SX 17 XN X) < 2 ^ (np * SX) := by
  have hn := (xiOK_split hx).1
  have hv := Benes.stagesValid_of_netOK hn
  have hsl := xiSgn_lt hx
  obtain ⟨y1, y2, y3⟩ := xi_X hO hnp hK hG hx hX1 hX2 hX3
  obtain ⟨z1, -, -⟩ := xi_X hO hnp hK hG hx y1 y2 y3
  have hW : Bd np SX (O.net SX 17 XN X) := hO.net_bd SX_eq hXN hX3
  have hNb : Bd np SX (O.neg SX F.xiSgn X) := hO.neg_bd hsl hX3
  refine ⟨fun q hq => ?_, fun P hP hno => ?_, hO.neg_bd hsl hW⟩
  · have hP := InitAux.xposK_lt' hq
    have h1 := Benes.benesPerm_lt hv hP
    have h2 := Benes.benesPerm_lt hv h1
    have hinv : Benes.benesInv 17 F.xiNet (xposK q) =
        Benes.benesPerm 17 F.xiNet (Benes.benesPerm 17 F.xiNet (xposK q)) := by
      have e := congrArg (Benes.benesInv 17 F.xiNet) (xiNet_cube hK hG hx hq)
      rw [Benes.benesInv_benesPerm hv] at e
      exact e.symm
    rw [← z1 q hq, hO.net_res SX_eq hn (hO.neg_bd hsl (hO.net_bd SX_eq hn hNb)) hP,
      hO.neg_res hsl (hO.net_bd SX_eq hn hNb) h1, hO.net_res SX_eq hn hNb h1,
      hO.neg_res hsl hX3 h2, hO.neg_res hsl hW hP, hO.net_res SX_eq hXN hX3 hP, hXI _ hP, hinv,
      xiSgn_orbit hx hK.la hP]
    cases F.xiSgn.testBit (Benes.benesPerm 17 F.xiNet (xposK q)) <;>
      cases F.xiSgn.testBit (Benes.benesPerm 17 F.xiNet (Benes.benesPerm 17 F.xiNet (xposK q))) <;>
        simp
  · have hR := Benes.benesInv_lt hv hP
    have hRno : ∀ q < 98280, xposK q ≠ Benes.benesInv 17 F.xiNet P := by
      intro q hq e
      obtain ⟨-, a0, d0, -⟩ := xi_lab hx hK.la (InitAux.xposK_lt' hq)
      rw [e, Benes.benesPerm_benesInv hv] at a0 d0
      have zA : kv F.keyA P = 0 :=
        kv_eq (fun b hb => by rw [hK.pa P hP hno b hb, Nat.zero_testBit]) (by decide)
      have zD : kv F.keyD P = 0 :=
        kv_eq (fun b hb => by rw [hK.pd P hP hno b hb, Nat.zero_testBit]) (by decide)
      rw [zA, zD] at a0 d0
      have kq : (kv F.keyA (xposK q), kv F.keyD (xposK q)) = keyQ q :=
        Prod.ext (kv_eq (hK.ka q hq) (hG.1 q hq).1) (kv_eq (hK.kd q hq) (hG.1 q hq).2)
      rw [e, a0, d0] at kq
      exact keyQ_ne_zero hq (by rw [← kq]; decide)
    rw [hO.neg_res hsl hW hP, hO.net_res SX_eq hXN hX3 hP, hXI _ hP, hX2 _ hR hRno]
    simp

@[expose] def linvI (k : ℕ) : ℕ := (k % 16 ^^^ (if par4 k then 15 else 0)) +
  16 * (k.testBit 5 ^^ par4 k).toNat + 32 * (!(k.testBit 4 ^^ k.testBit 5)).toNat

theorem linvI_spec : ∀ k < 64, linvI k < 64 ∧ linv (linvI k) = k := by decide

theorem linvI_lt : ∀ k < 64, linvI k < 64 := fun k hk => (linvI_spec k hk).1

@[expose] def TlI : ℕ → List (ℕ × ℤ) :=
  compL (fun k => [(k, sg (negIn k))]) (compL (fun k => [(pin k, 1)]) (compL (LB 3) (compL (LB 2)
    (compL (LB 1) (compL (LB 0) (compL (fun k => [(linvI k, 1)]) (fun k => [(k, sg (negOut k))])))))))

@[expose] def TlD : List (List ℕ) := [
  [33, 3, 5, 39, 9, 43, 45, 15, 17, 51, 53, 23, 57, 27, 29, 63],
  [65, 98, 101, 70, 105, 74, 77, 110, 113, 82, 85, 118, 89, 122, 125, 94],
  [65, 99, 100, 70, 105, 75, 76, 110, 113, 83, 84, 118, 89, 123, 124, 94],
  [32, 3, 5, 38, 8, 43, 45, 14, 16, 51, 53, 22, 56, 27, 29, 62],
  [65, 99, 101, 71, 104, 74, 76, 110, 113, 83, 85, 119, 88, 122, 124, 94],
  [32, 3, 4, 39, 9, 42, 45, 14, 16, 51, 52, 23, 57, 26, 29, 62],
  [32, 2, 5, 39, 9, 43, 44, 14, 16, 50, 53, 23, 57, 27, 28, 62],
  [64, 99, 101, 70, 105, 74, 76, 111, 112, 83, 85, 118, 89, 122, 124, 95],
  [65, 99, 101, 71, 105, 75, 77, 111, 112, 82, 84, 118, 88, 122, 124, 94],
  [32, 3, 4, 39, 8, 43, 44, 15, 17, 50, 53, 22, 57, 26, 29, 62],
  [32, 2, 5, 39, 8, 42, 45, 15, 17, 51, 52, 22, 57, 27, 28, 62],
  [64, 99, 101, 70, 104, 75, 77, 110, 113, 82, 84, 119, 89, 122, 124, 95],
  [32, 2, 4, 38, 9, 43, 45, 15, 17, 51, 53, 23, 56, 26, 28, 62],
  [64, 99, 100, 71, 105, 74, 77, 110, 113, 82, 85, 118, 88, 123, 124, 95],
  [64, 98, 101, 71, 105, 75, 76, 110, 113, 83, 84, 118, 88, 122, 125, 95],
  [33, 2, 4, 39, 8, 43, 45, 14, 16, 51, 53, 22, 57, 26, 28, 63],
  [65, 98, 100, 71, 104, 75, 77, 110, 112, 83, 85, 118, 89, 122, 124, 95],
  [33, 3, 4, 38, 8, 42, 45, 15, 16, 50, 53, 23, 57, 27, 28, 62],
  [33, 2, 5, 38, 8, 43, 44, 15, 16, 51, 52, 23, 57, 26, 29, 62],
  [64, 98, 100, 70, 105, 75, 77, 111, 113, 83, 85, 119, 88, 122, 124, 94],
  [33, 2, 4, 39, 9, 42, 44, 15, 16, 51, 53, 22, 56, 27, 29, 62],
  [64, 98, 101, 71, 104, 74, 77, 111, 113, 83, 84, 118, 89, 123, 124, 94],
  [64, 99, 100, 71, 104, 75, 76, 111, 113, 82, 85, 118, 89, 122, 125, 94],
  [32, 2, 4, 38, 8, 42, 44, 14, 17, 51, 53, 23, 57, 27, 29, 63],
  [33, 2, 4, 39, 8, 43, 45, 14, 17, 50, 52, 23, 56, 27, 29, 62],
  [64, 98, 101, 71, 105, 75, 76, 110, 112, 82, 85, 119, 89, 123, 124, 94],
  [64, 99, 100, 71, 105, 74, 77, 110, 112, 83, 84, 119, 89, 122, 125, 94],
  [32, 2, 4, 38, 9, 43, 45, 15, 16, 50, 52, 22, 57, 27, 29, 63],
  [64, 99, 101, 70, 104, 75, 77, 110, 112, 83, 85, 118, 88, 123, 125, 94],
  [32, 2, 5, 39, 8, 42, 45, 15, 16, 50, 53, 23, 56, 26, 29, 63],
  [32, 3, 4, 39, 8, 43, 44, 15, 16, 51, 52, 23, 56, 27, 28, 63],
  [65, 99, 101, 71, 105, 75, 77, 111, 113, 83, 85, 119, 89, 123, 125, 95],
  [1, 35, 37, 7, 41, 11, 13, 47, 49, 19, 21, 55, 25, 59, 61, 31],
  [96, 67, 68, 103, 72, 107, 108, 79, 80, 115, 116, 87, 120, 91, 92, 127],
  [96, 66, 69, 103, 72, 106, 109, 79, 80, 114, 117, 87, 120, 90, 93, 127],
  [0, 35, 37, 6, 40, 11, 13, 46, 48, 19, 21, 54, 24, 59, 61, 30],
  [96, 66, 68, 102, 73, 107, 109, 79, 80, 114, 116, 86, 121, 91, 93, 127],
  [0, 35, 36, 7, 41, 10, 13, 46, 48, 19, 20, 55, 25, 58, 61, 30],
  [0, 34, 37, 7, 41, 11, 12, 46, 48, 18, 21, 55, 25, 59, 60, 30],
  [97, 66, 68, 103, 72, 107, 109, 78, 81, 114, 116, 87, 120, 91, 93, 126],
  [96, 66, 68, 102, 72, 106, 108, 78, 81, 115, 117, 87, 121, 91, 93, 127],
  [0, 35, 36, 7, 40, 11, 12, 47, 49, 18, 21, 54, 25, 58, 61, 30],
  [0, 34, 37, 7, 40, 10, 13, 47, 49, 19, 20, 54, 25, 59, 60, 30],
  [97, 66, 68, 103, 73, 106, 108, 79, 80, 115, 117, 86, 120, 91, 93, 126],
  [0, 34, 36, 6, 41, 11, 13, 47, 49, 19, 21, 55, 24, 58, 60, 30],
  [97, 66, 69, 102, 72, 107, 108, 79, 80, 115, 116, 87, 121, 90, 93, 126],
  [97, 67, 68, 102, 72, 106, 109, 79, 80, 114, 117, 87, 121, 91, 92, 126],
  [1, 34, 36, 7, 40, 11, 13, 46, 48, 19, 21, 54, 25, 58, 60, 31],
  [97, 66, 68, 103, 72, 107, 109, 78, 80, 115, 117, 86, 121, 90, 92, 127],
  [0, 34, 37, 7, 41, 11, 12, 46, 49, 19, 20, 54, 24, 58, 61, 31],
  [0, 35, 36, 7, 41, 10, 13, 46, 49, 18, 21, 54, 24, 59, 60, 31],
  [96, 66, 68, 102, 73, 107, 109, 79, 81, 115, 117, 87, 120, 90, 92, 126],
  [0, 35, 37, 6, 40, 11, 13, 46, 49, 18, 20, 55, 25, 58, 60, 31],
  [96, 66, 69, 103, 72, 106, 109, 79, 81, 115, 116, 86, 121, 91, 92, 126],
  [96, 67, 68, 103, 72, 107, 108, 79, 81, 114, 117, 86, 121, 90, 93, 126],
  [1, 35, 37, 7, 41, 11, 13, 47, 48, 18, 20, 54, 24, 58, 60, 30],
  [0, 35, 37, 6, 41, 10, 12, 47, 48, 19, 21, 54, 25, 58, 60, 31],
  [96, 66, 69, 103, 73, 107, 108, 78, 80, 114, 117, 87, 121, 91, 92, 126],
  [96, 67, 68, 103, 73, 106, 109, 78, 80, 115, 116, 87, 121, 90, 93, 126],
  [1, 35, 37, 7, 40, 10, 12, 46, 49, 19, 21, 55, 24, 58, 60, 30],
  [96, 67, 69, 102, 72, 107, 109, 78, 80, 115, 117, 86, 120, 91, 93, 126],
  [1, 35, 36, 6, 41, 11, 12, 46, 49, 19, 20, 54, 25, 59, 60, 30],
  [1, 34, 37, 6, 41, 10, 13, 46, 49, 18, 21, 54, 25, 58, 61, 30],
  [97, 67, 69, 103, 73, 107, 109, 79, 81, 115, 117, 87, 121, 91, 93, 127]]

@[expose] def TlID : List (List ℕ) := [
  [65, 125, 123, 70, 119, 74, 76, 112, 111, 82, 84, 104, 88, 100, 98, 95],
  [1, 61, 58, 7, 54, 11, 12, 48, 46, 19, 20, 40, 24, 36, 35, 30],
  [1, 60, 59, 7, 54, 10, 13, 48, 46, 18, 21, 40, 24, 37, 34, 30],
  [65, 124, 122, 70, 119, 75, 77, 112, 111, 83, 85, 104, 88, 101, 99, 95],
  [1, 60, 58, 6, 55, 11, 13, 48, 46, 18, 20, 41, 25, 36, 34, 30],
  [65, 124, 123, 71, 118, 74, 77, 112, 111, 83, 84, 105, 89, 100, 99, 95],
  [65, 125, 122, 71, 118, 75, 76, 112, 111, 82, 85, 105, 89, 101, 98, 95],
  [1, 61, 59, 6, 55, 10, 12, 48, 46, 19, 21, 41, 25, 37, 35, 30],
  [1, 60, 58, 6, 54, 10, 12, 49, 47, 19, 21, 40, 25, 36, 34, 30],
  [65, 124, 123, 71, 119, 75, 76, 113, 110, 82, 85, 104, 89, 100, 99, 95],
  [65, 125, 122, 71, 119, 74, 77, 113, 110, 83, 84, 104, 89, 101, 98, 95],
  [1, 61, 59, 6, 54, 11, 13, 49, 47, 18, 20, 40, 25, 37, 35, 30],
  [65, 125, 123, 70, 118, 75, 77, 113, 110, 83, 85, 105, 88, 100, 98, 95],
  [1, 61, 58, 7, 55, 10, 13, 49, 47, 18, 21, 41, 24, 36, 35, 30],
  [1, 60, 59, 7, 55, 11, 12, 49, 47, 19, 20, 41, 24, 37, 34, 30],
  [65, 124, 122, 70, 118, 74, 76, 113, 110, 82, 84, 105, 88, 101, 99, 95],
  [1, 60, 58, 6, 54, 10, 12, 49, 46, 18, 20, 41, 24, 37, 35, 31],
  [65, 124, 123, 71, 119, 75, 76, 113, 111, 83, 84, 105, 88, 101, 98, 94],
  [65, 125, 122, 71, 119, 74, 77, 113, 111, 82, 85, 105, 88, 100, 99, 94],
  [1, 61, 59, 6, 54, 11, 13, 49, 46, 19, 21, 41, 24, 36, 34, 31],
  [65, 125, 123, 70, 118, 75, 77, 113, 111, 82, 84, 104, 89, 101, 99, 94],
  [1, 61, 58, 7, 55, 10, 13, 49, 46, 19, 20, 40, 25, 37, 34, 31],
  [1, 60, 59, 7, 55, 11, 12, 49, 46, 18, 21, 40, 25, 36, 35, 31],
  [65, 124, 122, 70, 118, 74, 76, 113, 111, 83, 85, 104, 89, 100, 98, 94],
  [65, 125, 123, 70, 119, 74, 76, 112, 110, 83, 85, 105, 89, 101, 99, 94],
  [1, 61, 58, 7, 54, 11, 12, 48, 47, 18, 21, 41, 25, 37, 34, 31],
  [1, 60, 59, 7, 54, 10, 13, 48, 47, 19, 20, 41, 25, 36, 35, 31],
  [65, 124, 122, 70, 119, 75, 77, 112, 110, 82, 84, 105, 89, 100, 98, 94],
  [1, 60, 58, 6, 55, 11, 13, 48, 47, 19, 21, 40, 24, 37, 35, 31],
  [65, 124, 123, 71, 118, 74, 77, 112, 110, 82, 85, 104, 88, 101, 98, 94],
  [65, 125, 122, 71, 118, 75, 76, 112, 110, 83, 84, 104, 88, 100, 99, 94],
  [1, 61, 59, 6, 55, 10, 12, 48, 47, 18, 20, 40, 24, 36, 34, 31],
  [33, 28, 26, 38, 22, 42, 44, 17, 14, 50, 52, 9, 56, 5, 3, 63],
  [96, 93, 90, 102, 86, 106, 109, 80, 78, 114, 117, 72, 121, 68, 67, 127],
  [96, 92, 91, 102, 86, 107, 108, 80, 78, 115, 116, 72, 121, 69, 66, 127],
  [33, 29, 27, 38, 22, 43, 45, 17, 14, 51, 53, 9, 56, 4, 2, 63],
  [96, 92, 90, 103, 87, 106, 108, 80, 78, 115, 117, 73, 120, 68, 66, 127],
  [33, 29, 26, 39, 23, 42, 45, 17, 14, 51, 52, 8, 57, 5, 2, 63],
  [33, 28, 27, 39, 23, 43, 44, 17, 14, 50, 53, 8, 57, 4, 3, 63],
  [96, 93, 91, 103, 87, 107, 109, 80, 78, 114, 116, 73, 120, 69, 67, 127],
  [96, 92, 90, 103, 86, 107, 109, 81, 79, 114, 116, 72, 120, 68, 66, 127],
  [33, 29, 26, 39, 22, 43, 44, 16, 15, 50, 53, 9, 57, 5, 2, 63],
  [33, 28, 27, 39, 22, 42, 45, 16, 15, 51, 52, 9, 57, 4, 3, 63],
  [96, 93, 91, 103, 86, 106, 108, 81, 79, 115, 117, 72, 120, 69, 67, 127],
  [33, 28, 26, 38, 23, 43, 45, 16, 15, 51, 53, 8, 56, 5, 3, 63],
  [96, 93, 90, 102, 87, 107, 108, 81, 79, 115, 116, 73, 121, 68, 67, 127],
  [96, 92, 91, 102, 87, 106, 109, 81, 79, 114, 117, 73, 121, 69, 66, 127],
  [33, 29, 27, 38, 23, 42, 44, 16, 15, 50, 52, 8, 56, 4, 2, 63],
  [97, 93, 91, 102, 87, 106, 108, 80, 79, 114, 116, 72, 120, 68, 66, 127],
  [32, 28, 27, 38, 23, 42, 45, 17, 15, 50, 53, 9, 57, 5, 2, 63],
  [32, 29, 26, 38, 23, 43, 44, 17, 15, 51, 52, 9, 57, 4, 3, 63],
  [97, 92, 90, 102, 87, 107, 109, 80, 79, 115, 117, 72, 120, 69, 67, 127],
  [32, 29, 27, 39, 22, 42, 44, 17, 15, 51, 53, 8, 56, 5, 3, 63],
  [97, 92, 91, 103, 86, 106, 109, 80, 79, 115, 116, 73, 121, 68, 67, 127],
  [97, 93, 90, 103, 86, 107, 108, 80, 79, 114, 117, 73, 121, 69, 66, 127],
  [32, 28, 26, 39, 22, 43, 45, 17, 15, 50, 52, 8, 56, 4, 2, 63],
  [32, 29, 27, 39, 23, 43, 45, 16, 14, 50, 52, 9, 56, 5, 3, 63],
  [97, 92, 91, 103, 87, 107, 108, 81, 78, 114, 117, 72, 121, 68, 67, 127],
  [97, 93, 90, 103, 87, 106, 109, 81, 78, 115, 116, 72, 121, 69, 66, 127],
  [32, 28, 26, 39, 23, 42, 44, 16, 14, 51, 53, 9, 56, 4, 2, 63],
  [97, 93, 91, 102, 86, 107, 109, 81, 78, 115, 117, 73, 120, 68, 66, 127],
  [32, 28, 27, 38, 22, 43, 44, 16, 14, 51, 52, 8, 57, 5, 2, 63],
  [32, 29, 26, 38, 22, 42, 45, 16, 14, 50, 53, 8, 57, 4, 3, 63],
  [97, 92, 90, 102, 86, 106, 108, 81, 78, 114, 116, 73, 120, 69, 67, 127]]

@[expose] def tlDec (x : ℕ) : ℕ × ℤ := (x / 2, if x % 2 = 1 then -1 else 1)

@[expose] def tlRow (E : List (List ℕ)) (k : ℕ) : List (ℕ × ℤ) := (E.getD k []).map tlDec

set_option maxRecDepth 100000 in
theorem Tl_tab : ∀ k < 64, Tl k = tlRow TlD k := by decide +kernel

set_option maxRecDepth 100000 in
theorem TlI_tab : ∀ k < 64, TlI k = tlRow TlID k := by decide +kernel

@[expose] def tlPk (s : ℤ) (L : List (ℕ × ℤ)) : ℕ :=
  (L.map fun t => if t.2 = s then 1024 ^ t.1 else 0).sum

@[expose] def tlCnt (s : ℤ) (L : List (ℕ × ℤ)) (q : ℕ) : ℕ :=
  (L.map fun t => if t.1 = q ∧ t.2 = s then 1 else 0).sum

@[expose] def tlChk (L M : List (ℕ × ℤ)) : Bool :=
  tlPk 1 L + 4 * tlPk (-1) M == tlPk (-1) L + 4 * tlPk 1 M && decide (L.length ≤ 256) &&
    decide (M.length ≤ 16) && L.all (fun t => decide (t.1 < 64) && (t.2 == 1 || t.2 == -1)) &&
    M.all (fun t => decide (t.1 < 64) && (t.2 == 1 || t.2 == -1))

theorem tlInd_sum {B n : ℕ} (a : ℕ × ℤ) (s : ℤ) (ha : a.1 < n) :
    ∑ q ∈ Finset.range n, (if a.1 = q ∧ a.2 = s then 1 else 0) * B ^ q =
      if a.2 = s then B ^ a.1 else 0 := by
  by_cases hs : a.2 = s
  · simp only [hs, and_true, ite_mul, one_mul, zero_mul, ↓reduceIte]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 ha)]
  · simp [hs]

theorem tlPk_eq (s : ℤ) {L : List (ℕ × ℤ)} (hL : ∀ t ∈ L, t.1 < 64) :
    tlPk s L = ∑ q ∈ Finset.range 64, tlCnt s L q * 1024 ^ q := by
  induction L with
  | nil => simp [tlPk, tlCnt]
  | cons a L ih =>
    have h := ih fun t ht => hL t (List.mem_cons_of_mem _ ht)
    have ha : a.1 < 64 := hL a List.mem_cons_self
    simp only [tlPk, tlCnt, List.map_cons, List.sum_cons] at h ⊢
    simp only [h, add_mul, Finset.sum_add_distrib]
    rw [tlInd_sum a s ha]

theorem tlCnt_le (s : ℤ) (L : List (ℕ × ℤ)) (q : ℕ) : tlCnt s L q ≤ L.length := by
  induction L with
  | nil => simp [tlCnt]
  | cons a L ih =>
    simp only [tlCnt, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    split_ifs <;> omega

theorem coef_tlCnt {L : List (ℕ × ℤ)} (hL : ∀ t ∈ L, t.2 = 1 ∨ t.2 = -1) (q : ℕ) :
    coef L q = tlCnt 1 L q - tlCnt (-1) L q := by
  induction L with
  | nil => simp [coef, tlCnt]
  | cons a L ih =>
    have h := ih fun t ht => hL t (List.mem_cons_of_mem _ ht)
    simp only [coef, tlCnt, List.map_cons, List.sum_cons] at h ⊢
    rw [h]
    push_cast
    rcases hL a List.mem_cons_self with h2 | h2 <;> by_cases h1 : a.1 = q <;> simp [h1, h2] <;> ring

theorem tlDig_inj {B : ℕ} : ∀ n (a b : ℕ → ℕ), (∀ q < n, a q < B) → (∀ q < n, b q < B) →
    ∑ q ∈ Finset.range n, a q * B ^ q = ∑ q ∈ Finset.range n, b q * B ^ q → ∀ q < n, a q = b q := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ q hq; omega
  | succ n ih =>
    intro a b ha hb h q hq
    have e : ∀ c : ℕ → ℕ, ∑ q ∈ Finset.range (n + 1), c q * B ^ q =
        c 0 + B * ∑ q ∈ Finset.range n, c (q + 1) * B ^ q := by
      intro c
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm, pow_zero, mul_one]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, e] at h
    have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (ha 0 (by omega))
    have h0 : a 0 = b 0 := by
      have h' := congrArg (· % B) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ha 0 (by omega)),
        Nat.mod_eq_of_lt (hb 0 (by omega))] at h'
      exact h'
    have h1 : ∑ q ∈ Finset.range n, a (q + 1) * B ^ q = ∑ q ∈ Finset.range n, b (q + 1) * B ^ q := by
      rw [h0] at h
      exact Nat.eq_of_mul_eq_mul_left hB (by omega)
    rcases q with _ | q
    · exact h0
    · exact ih (fun q => a (q + 1)) (fun q => b (q + 1)) (fun q _ => ha _ (by omega))
        (fun q _ => hb _ (by omega)) h1 q (by omega)

theorem coef_of_tlChk {L M : List (ℕ × ℤ)} (h : tlChk L M = true) :
    ∀ q < 64, coef L q = 4 * coef M q := by
  simp only [tlChk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨h, hl⟩, hm⟩, hL⟩, hM⟩ := h
  have hd := tlDig_inj (B := 1024) 64 (fun q => tlCnt 1 L q + 4 * tlCnt (-1) M q)
    (fun q => tlCnt (-1) L q + 4 * tlCnt 1 M q)
    (fun q _ => by have := tlCnt_le 1 L q; have := tlCnt_le (-1) M q; omega)
    (fun q _ => by have := tlCnt_le (-1) L q; have := tlCnt_le 1 M q; omega) (by
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
        ← tlPk_eq _ fun t ht => (hL t ht).1, ← tlPk_eq _ fun t ht => (hM t ht).1]
      exact h)
  intro q hq
  have hq' := hd q hq
  rw [coef_tlCnt (fun t ht => by simpa using (hL t ht).2) q,
    coef_tlCnt (fun t ht => by simpa using (hM t ht).2) q]
  omega

set_option maxRecDepth 100000 in
theorem TlD_chk : ∀ k < 64, tlChk (compL (tlRow TlD) (tlRow TlD) k) (tlRow TlID k) = true := by
  decide +kernel

theorem TlD_sq : ∀ k < 64, ∀ k0 < 64,
    coef (compL (tlRow TlD) (tlRow TlD) k) k0 = 4 * coef (tlRow TlID k) k0 :=
  fun k hk => coef_of_tlChk (TlD_chk k hk)

theorem compL_congr64 {A A' B B' : ℕ → List (ℕ × ℤ)} (hA : ∀ k < 64, A k = A' k)
    (hB : ∀ k < 64, B k = B' k) (hAl : ∀ k < 64, ∀ e ∈ A k, e.1 < 64) {k : ℕ} (hk : k < 64) :
    compL A B k = compL A' B' k := by
  have aux : ∀ l : List (ℕ × ℤ), (∀ e ∈ l, e.1 < 64) →
      l.flatMap (fun e => (B e.1).map (fun f => (f.1, e.2 * f.2))) =
        l.flatMap (fun e => (B' e.1).map (fun f => (f.1, e.2 * f.2))) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro hl
      rw [List.flatMap_cons, List.flatMap_cons, hB a.1 (hl a List.mem_cons_self),
        ih fun e he => hl e (List.mem_cons_of_mem _ he)]
  unfold compL
  rw [← hA k hk]
  exact aux _ (hAl k hk)

theorem Tl_sq : ∀ k < 64, ∀ k0 < 64, coef (compL Tl Tl k) k0 = 4 * coef (TlI k) k0 := by
  intro k hk k0 hk0
  rw [compL_congr64 Tl_tab Tl_tab Tl_lt hk, TlI_tab k hk]
  exact TlD_sq k hk k0 hk0

theorem TlI_lt : ∀ k < 64, ∀ e ∈ TlI k, e.1 < 64 := by decide

theorem poutI_pos {F : Fix} (hp : poutOK F = true) {H j k : ℕ} (hH : H < 64) (hj : j < 24)
    (hk : k < 64) : Benes.benesInv 17 F.pout (pos H j k) = pos H j (linvI k) := by
  have hv := Benes.stagesValid_of_netOK (pout_lab hp).1
  obtain ⟨hl, he⟩ := linvI_spec k hk
  have e := congrArg (Benes.benesInv 17 F.pout) (pout_pos hp hH hj hl)
  rw [Benes.benesInv_benesPerm hv, he] at e
  exact e.symm

theorem lsum_compL {M : ℕ} (A B : ℕ → List (ℕ × ℤ)) (g : ℕ → ZMod M) (k : ℕ) :
    ((compL A B k).map fun e => (e.2 : ZMod M) * g e.1).sum =
      ((A k).map fun e => (e.2 : ZMod M) * ((B e.1).map fun f => (f.2 : ZMod M) * g f.1).sum).sum := by
  unfold compL
  induction A k with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons,
      List.map_map, ← List.sum_map_mul_left]
    congr 2
    refine List.map_congr_left fun f _ => ?_
    simp only [Function.comp_apply]
    push_cast
    ring

theorem lsum_fsum {M : ℕ} (L : List (ℕ × ℤ)) (s : Finset ℕ) (c : ℕ → ZMod M) (g : ℕ → ℕ → ZMod M) :
    ∑ w ∈ s, c w * (L.map fun e => (e.2 : ZMod M) * g w e.1).sum =
      (L.map fun e => (e.2 : ZMod M) * ∑ w ∈ s, c w * g w e.1).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem xi_resW (hnp : 2 ≤ np) (v : Native.DVec) {H k j : ℕ} (hH : H < 64) (hk : k < 64)
    (hj : j < 24) :
    resN np (Native.applyGen (Native.mkCtx ()) .xi v) (98580 + 24 * rr H k + j) =
      hN np ^ 3 * ((Tl k).map fun e => ((e.2 : ℤ) : ZMod (2 ^ np - 1)) * ∑ w ∈ Finset.range 4,
        ((c4z w (j % 4) : ℤ) : ZMod (2 ^ np - 1)) *
          resN np v (98580 + 24 * rr H e.1 + 4 * (j / 4) + w)).sum := by
  have h2 := two_hN (np := np) (by omega)
  let Y : ℕ → ℕ → ZMod (2 ^ np - 1) := fun r j => ∑ w ∈ Finset.range 4,
    ((c4z w (j % 4) : ℤ) : ZMod (2 ^ np - 1)) * resN np v (98580 + 24 * r + 4 * (j / 4) + w)
  change resM (hN np) (Native.applyGD (Native.mkCtx ()) (Native.GD.ofGen (Native.mkCtx ()) .xi) v)
    (98580 + 24 * rr H k + j) = hN np ^ 3 * ((Tl k).map fun e => ((e.2 : ℤ) : ZMod (2 ^ np - 1)) *
      Y (rr H e.1) j).sum
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
  linear_combination (hN np ^ 3 * ((Tl k).map fun e => ((e.2 : ℤ) : ZMod (2 ^ np - 1)) *
    Y (rr H e.1) j).sum) * h16

theorem rel_twinI (hO : PLaw np O) {F : Fix} (hp : poutOK F = true) {PN : ℕ}
    (hPN : netOK 17 PN = true) (hPI : ∀ r < SX, Benes.benesPerm 17 PN r = Benes.benesInv 17 F.pout r)
    {W H j : ℕ} (hW : Bd np SX W) (hH : H < 64) (hj : j < 24) :
    Rel np (fun k => resPN np SX (O.neg SX dinM (pinWG O (wht4G O (O.net SX 17 PN
      (O.neg SX doutM W))))) (pos H j k)) (fun k => resPN np SX W (pos H j k)) TlI := by
  have b0 := hO.neg_bd doutM_lt hW
  have b1 := hO.net_bd SX_eq hPN b0
  have c5 := hO.bfly_bd (k := 17) (b := 5 + 0) SX_eq (by decide) valW_lt b1
  have c6 := hO.bfly_bd (k := 17) (b := 5 + 1) SX_eq (by decide) valW_lt c5
  have c7 := hO.bfly_bd (k := 17) (b := 5 + 2) SX_eq (by decide) valW_lt c6
  have c8 := hO.bfly_bd (k := 17) (b := 5 + 3) SX_eq (by decide) valW_lt c7
  have c8' : Bd np SX (wht4G O (O.net SX 17 PN (O.neg SX doutM W))) := c8
  have b2 : Bd np SX (pinWG O (wht4G O (O.net SX 17 PN (O.neg SX doutM W)))) :=
    bd_dsw_rep hO mpin_valid c8'
  have r8 := rel_neg hO doutM_lt hW hH hj (fun k hk => doutM_pos hH hj hk)
  have r7 : Rel np (fun k => resPN np SX (O.net SX 17 PN (O.neg SX doutM W)) (pos H j k))
      (fun k => resPN np SX (O.neg SX doutM W) (pos H j k)) (fun k => [(linvI k, 1)]) :=
    rel_one linvI_lt fun k hk => by
      rw [hO.net_res SX_eq hPN b0 (pos_lt hH (by omega) hk), hPI _ (pos_lt hH (by omega) hk),
        poutI_pos hp hH hj hk]
      simp
  have q0 := rel_bfly hO b1 hH hj (i := 0) (by decide) clW5
  have q1 := rel_bfly hO c5 hH hj (i := 1) (by decide) clW6
  have q2 := rel_bfly hO c6 hH hj (i := 2) (by decide) clW7
  have q3 := rel_bfly hO c7 hH hj (i := 3) (by decide) clW8
  have r2 : Rel np (fun k => resPN np SX (pinWG O (wht4G O (O.net SX 17 PN (O.neg SX doutM W))))
      (pos H j k)) (fun k => resPN np SX (wht4G O (O.net SX 17 PN (O.neg SX doutM W))) (pos H j k))
      (fun k => [(pin k, 1)]) := rel_one pin_lt fun k hk => by
    rw [pinWG_eq, res_dsw_rep hO mpin_valid c8' (pos_lt hH (by omega) hk), swp_pin hH hj hk]
    simp
  have r1 := rel_neg hO dinM_lt b2 hH hj (fun k hk => dinM_pos hH hj hk)
  exact rel_comp r1 (rel_comp r2 (rel_comp q3 (rel_comp q2 (rel_comp q1 (rel_comp q0
    (rel_comp r7 r8))))))

theorem compL_lt64 {A B : ℕ → List (ℕ × ℤ)} (hB : ∀ k < 64, ∀ e ∈ B k, e.1 < 64) {k : ℕ}
    (hA : ∀ e ∈ A k, e.1 < 64) : ∀ e ∈ compL A B k, e.1 < 64 := by
  intro e he
  unfold compL at he
  rw [List.mem_flatMap] at he
  obtain ⟨a, ha, he⟩ := he
  rw [List.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  exact hB a.1 (hA a ha) f hf

theorem lsum_smul {M : ℕ} (L : List (ℕ × ℤ)) (c : ZMod M) (g : ℕ → ZMod M) :
    (L.map fun e => (e.2 : ZMod M) * (c * g e.1)).sum = c * (L.map fun e => (e.2 : ZMod M) * g e.1).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem xiInv_W (hO : PLaw np O) (hnp : 2 ≤ np) {F : Fix} (hp : poutOK F = true) {PN : ℕ}
    (hPN : netOK 17 PN = true) (hPI : ∀ r < SX, Benes.benesPerm 17 PN r = Benes.benesInv 17 F.pout r)
    {v : Native.DVec} {W : ℕ}
    (hW1 : ∀ r < 4096, ∀ j < 24, resPN np SX W (32 * r + j) = resN np v (98580 + 24 * r + j))
    (hW2 : ∀ p < SX, 24 ≤ p % 32 → resPN np SX W p = 0) (hW3 : W < 2 ^ (np * SX)) :
    (∀ r < 4096, ∀ j < 24, resPN np SX (O.half SX 3 (colxiTG O SX 0 1 valW (O.neg SX dinM
      (pinWG O (wht4G O (O.net SX 17 PN (O.neg SX doutM W))))))) (32 * r + j) =
        resN np (Native.applyGen (Native.mkCtx ()) .xi (Native.applyGen (Native.mkCtx ()) .xi v))
          (98580 + 24 * r + j)) ∧
    (∀ p < SX, 24 ≤ p % 32 → resPN np SX (O.half SX 3 (colxiTG O SX 0 1 valW (O.neg SX dinM
      (pinWG O (wht4G O (O.net SX 17 PN (O.neg SX doutM W))))))) p = 0) ∧
    O.half SX 3 (colxiTG O SX 0 1 valW (O.neg SX dinM
      (pinWG O (wht4G O (O.net SX 17 PN (O.neg SX doutM W)))))) < 2 ^ (np * SX) := by
  have h2 := two_hN (np := np) (by omega)
  have b0 := hO.neg_bd doutM_lt hW3
  have b1 := hO.net_bd SX_eq hPN b0
  have c5 := hO.bfly_bd (k := 17) (b := 5 + 0) SX_eq (by decide) valW_lt b1
  have c6 := hO.bfly_bd (k := 17) (b := 5 + 1) SX_eq (by decide) valW_lt c5
  have c7 := hO.bfly_bd (k := 17) (b := 5 + 2) SX_eq (by decide) valW_lt c6
  have c8 := hO.bfly_bd (k := 17) (b := 5 + 3) SX_eq (by decide) valW_lt c7
  have c8' : Bd np SX (wht4G O (O.net SX 17 PN (O.neg SX doutM W))) := c8
  have b2 : Bd np SX (pinWG O (wht4G O (O.net SX 17 PN (O.neg SX doutM W)))) :=
    bd_dsw_rep hO mpin_valid c8'
  have b3 := hO.neg_bd dinM_lt b2
  have b4 := colWT_bd hO b3
  refine ⟨fun r hr j hj => ?_, fun p hpS hpm => ?_, hO.half_bd (by decide) (by decide) b4⟩
  · have hH : r / 32 % 64 < 64 := Nat.mod_lt _ (by decide)
    have hk : r % 32 + 32 * (r / 2048) < 64 := by omega
    have hrr : rr (r / 32 % 64) (r % 32 + 32 * (r / 2048)) = r := by unfold rr; omega
    generalize r / 32 % 64 = H at hH hrr
    generalize r % 32 + 32 * (r / 2048) = k at hk hrr
    subst hrr
    have hu : j % 4 < 4 := Nat.mod_lt _ (by decide)
    let f : ℕ → ℕ → ZMod (2 ^ np - 1) := fun k0 a => resN np v (98580 + 24 * rr H k0 + 4 * (j / 4) + a)
    let G : ℕ → ZMod (2 ^ np - 1) := fun k0 => ∑ a ∈ Finset.range 4,
      ((c4z (j % 4) a : ℤ) : ZMod (2 ^ np - 1)) * f k0 a
    have hP : 32 * rr H k + j < SX := pos_lt hH (by omega : j < 32) hk
    rw [hO.half_res (by decide) (by decide) b4 hP,
      show 32 * rr H k + j = 32 * rr H k + 4 * (j / 4) + j % 4 by omega,
      colW01T hO b3 (rr_lt hH hk) (by omega) hu]
    have pl : ∀ w ∈ Finset.range 4, ((c4z (j % 4) w : ℤ) : ZMod (2 ^ np - 1)) *
        resPN np SX (O.neg SX dinM (pinWG O (wht4G O (O.net SX 17 PN (O.neg SX doutM W)))))
          (32 * rr H k + 4 * (j / 4) + w) = ((c4z (j % 4) w : ℤ) : ZMod (2 ^ np - 1)) *
        ((TlI k).map fun e => ((e.2 : ℤ) : ZMod (2 ^ np - 1)) * f e.1 w).sum := by
      intro w hw
      have hw' := Finset.mem_range.1 hw
      have rt := ((rel_twinI hO hp hPN hPI hW3 hH (j := 4 * (j / 4) + w) (by omega)) k hk).2
      dsimp only at rt
      rw [show 32 * rr H k + 4 * (j / 4) + w = pos H (4 * (j / 4) + w) k by rw [pos_eq]; omega, rt]
      refine congrArg _ (congrArg List.sum (List.map_congr_left fun e he => ?_))
      have he' := TlI_lt k hk e he
      rw [pos_eq, hW1 _ (rr_lt hH he') _ (by omega), ← Nat.add_assoc]
    have fp := lsum_fsum (TlI k) (Finset.range 4) (fun w => ((c4z (j % 4) w : ℤ) : ZMod (2 ^ np - 1)))
      (fun w k0 => f k0 w)
    have eG : ((TlI k).map fun e => ((e.2 : ℤ) : ZMod (2 ^ np - 1)) * ∑ w ∈ Finset.range 4,
        ((c4z (j % 4) w : ℤ) : ZMod (2 ^ np - 1)) * f e.1 w).sum =
        ((TlI k).map fun e => ((e.2 : ℤ) : ZMod (2 ^ np - 1)) * G e.1).sum := rfl
    rw [Finset.sum_congr rfl pl, fp, eG]
    have n1 : ∀ k1 < 64, ∑ w ∈ Finset.range 4, ((c4z w (j % 4) : ℤ) : ZMod (2 ^ np - 1)) *
        resN np (Native.applyGen (Native.mkCtx ()) .xi v) (98580 + 24 * rr H k1 + 4 * (j / 4) + w) =
        hN np ^ 3 * (2 * ((Tl k1).map fun e => ((e.2 : ℤ) : ZMod (2 ^ np - 1)) * G e.1).sum) := by
      intro k1 hk1
      have e1 : ∀ w ∈ Finset.range 4, ((c4z w (j % 4) : ℤ) : ZMod (2 ^ np - 1)) *
          resN np (Native.applyGen (Native.mkCtx ()) .xi v) (98580 + 24 * rr H k1 + 4 * (j / 4) + w) =
          hN np ^ 3 * (((c4z w (j % 4) : ℤ) : ZMod (2 ^ np - 1)) * ((Tl k1).map fun e =>
            ((e.2 : ℤ) : ZMod (2 ^ np - 1)) * ∑ a ∈ Finset.range 4,
              ((c4z a w : ℤ) : ZMod (2 ^ np - 1)) * f e.1 a).sum) := by
        intro w hw
        have hw' := Finset.mem_range.1 hw
        rw [Nat.add_assoc, xi_resW hnp v hH hk1 (by omega : 4 * (j / 4) + w < 24),
          show (4 * (j / 4) + w) % 4 = w by omega, show (4 * (j / 4) + w) / 4 = j / 4 by omega]
        ring
      have fq := lsum_fsum (Tl k1) (Finset.range 4) (fun w => ((c4z w (j % 4) : ℤ) : ZMod (2 ^ np - 1)))
        (fun w k0 => ∑ a ∈ Finset.range 4, ((c4z a w : ℤ) : ZMod (2 ^ np - 1)) * f k0 a)
      have sm := lsum_smul (Tl k1) 2 G
      rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, fq, ← sm]
      refine congrArg _ (congrArg List.sum (List.map_congr_left fun e _ => ?_))
      rw [c4_sq hu (f e.1)]
    rw [xi_resW hnp _ hH hk hj]
    have n2 : ((Tl k).map fun e => ((e.2 : ℤ) : ZMod (2 ^ np - 1)) * ∑ w ∈ Finset.range 4,
        ((c4z w (j % 4) : ℤ) : ZMod (2 ^ np - 1)) *
          resN np (Native.applyGen (Native.mkCtx ()) .xi v) (98580 + 24 * rr H e.1 + 4 * (j / 4) + w)).sum =
        ((Tl k).map fun e => ((e.2 : ℤ) : ZMod (2 ^ np - 1)) * (hN np ^ 3 * (2 *
          ((Tl e.1).map fun e' => ((e'.2 : ℤ) : ZMod (2 ^ np - 1)) * G e'.1).sum))).sum :=
      congrArg List.sum (List.map_congr_left fun e he => by rw [n1 e.1 (Tl_lt k hk e he)])
    have s1 := lsum_smul (Tl k) (hN np ^ 3)
      (fun k1 => 2 * ((Tl k1).map fun e' => ((e'.2 : ℤ) : ZMod (2 ^ np - 1)) * G e'.1).sum)
    have s2 := lsum_smul (Tl k) 2
      (fun k1 => ((Tl k1).map fun e' => ((e'.2 : ℤ) : ZMod (2 ^ np - 1)) * G e'.1).sum)
    rw [n2, s1, s2, ← lsum_compL Tl Tl G k,
      ← sum_coef _ (compL_lt64 Tl_lt (Tl_lt k hk)) G, ← sum_coef _ (TlI_lt k hk) G]
    have n3 : ∀ k0 ∈ Finset.range 64, ((coef (compL Tl Tl k) k0 : ℤ) : ZMod (2 ^ np - 1)) * G k0 =
        4 * (((coef (TlI k) k0 : ℤ) : ZMod (2 ^ np - 1)) * G k0) := by
      intro k0 hk0
      rw [Tl_sq k hk k0 (Finset.mem_range.1 hk0)]
      push_cast
      ring
    rw [Finset.sum_congr rfl n3, ← Finset.mul_sum]
    have h8 : (8 : ZMod (2 ^ np - 1)) * hN np ^ 3 = 1 := by
      rw [show (8 : ZMod (2 ^ np - 1)) * hN np ^ 3 = (2 * hN np) ^ 3 by ring, h2, one_pow]
    linear_combination (-(hN np ^ 3 * ∑ k0 ∈ Finset.range 64,
      ((coef (TlI k) k0 : ℤ) : ZMod (2 ^ np - 1)) * G k0)) * h8
  · have hvp : valW.testBit p = false := by
      rw [testBit_valW]
      simp only [decide_eq_false_iff_not]
      omega
    have hs : Benes.swp 512 mpin p < SX ∧ Benes.swp 512 mpin p % 32 = p % 32 := by
      have hv := mpin_valid
      unfold Benes.swp
      split_ifs with h1 h2
      · have := (hv p h1).1
        exact ⟨this, by omega⟩
      · exact ⟨by omega, by omega⟩
      · exact ⟨hpS, rfl⟩
    set q := Benes.swp 512 mpin p with hq
    have hvq : valW.testBit q = false := by
      rw [testBit_valW]
      simp only [decide_eq_false_iff_not]
      omega
    have hv := Benes.stagesValid_of_netOK (pout_lab hp).1
    have hsS := Benes.benesInv_lt hv hs.1
    have hsm := (pout_col hp hsS).2
    rw [Benes.benesPerm_benesInv hv] at hsm
    have z3 : resPN np SX (wht4G O (O.net SX 17 PN (O.neg SX doutM W))) q = 0 := by
      rw [wht4G_eq, hO.bfly_res SX_eq (by decide) valW_lt clW8 c7 hs.1, hvq, ite_eq_left rfl,
        hO.bfly_res SX_eq (by decide) valW_lt clW7 c6 hs.1, hvq, ite_eq_left rfl,
        hO.bfly_res SX_eq (by decide) valW_lt clW6 c5 hs.1, hvq, ite_eq_left rfl,
        hO.bfly_res SX_eq (by decide) valW_lt clW5 b1 hs.1, hvq, ite_eq_left rfl,
        hO.net_res SX_eq hPN b0 hs.1, hPI _ hs.1, hO.neg_res doutM_lt hW3 hsS,
        hW2 _ hsS (by omega)]
      simp
    rw [hO.half_res (by decide) (by decide) b4 hpS, outW01T hO b3 hpS hvp,
      hO.neg_res dinM_lt b2 hpS, pinWG_eq, res_dsw_rep hO mpin_valid c8' hpS, ← hq, z3]
    simp

end XiInvAux

open XiInvAux XiAux

theorem xiInv_sound {np : ℕ} {O : POps} (hO : PLaw np O) (hnp : 2 ≤ np) {F : Fix} (hK : KeyBind F)
    (hG : KeysGood) (hx : xiOK F = true) (hp : poutOK F = true) {XN PN : ℕ}
    (hXN : netOK 17 XN = true)
    (hXI : ∀ r < SX, Benes.benesPerm 17 XN r = Benes.benesInv 17 F.xiNet r)
    (hPN : netOK 17 PN = true) (hPI : ∀ r < SX, Benes.benesPerm 17 PN r = Benes.benesInv 17 F.pout r)
    {v : Native.DVec} {t : St} (ht : RepN np v t) (f : Bool) :
    RepN np (Native.applyGen (Native.mkCtx ()) .xi (Native.applyGen (Native.mkCtx ()) .xi v))
      (f, xiInvG O F XN PN t.2.1 t.2.2.1 t.2.2.2) := by
  obtain ⟨hX1, hX2, hX3, hA1, hA2, hA3, hW1, hW2, hW3⟩ := ht
  obtain ⟨x1, x2, x3⟩ := xiInv_X hO hnp hK hG hx hXN hXI hX1 hX2 hX3
  obtain ⟨w1, w2, w3⟩ := xiInv_W hO hnp hp hPN hPI hW1 hW2 hW3
  exact ⟨x1, x2, x3, fun i hi j hj => xiInv_A hO hnp hA1 hA3 hi hj,
    fun p hp hv => xiInvG_resA_zero hO hA3 hp hv (hA2 p hp hv), xiInvG_bdA hO hA3, w1, w2, w3⟩

theorem xiInv_sound_rev {np : ℕ} {O : POps} (hO : PLaw np O) (hnp : 2 ≤ np) {F : Fix}
    (hK : KeyBind F) (hG : KeysGood) (hx : xiOK F = true) (hp : poutOK F = true)
    {v : Native.DVec} {t : St} (ht : RepN np v t) (f : Bool) :
    RepN np (Native.applyGen (Native.mkCtx ()) .xi (Native.applyGen (Native.mkCtx ()) .xi v))
      (f, xiInvG O F (YModel.netRev 17 F.xiNet) (YModel.netRev 17 F.pout) t.2.1 t.2.2.1 t.2.2.2) :=
  xiInv_sound hO hnp hK hG hx hp (YModel.Sch.netOK_netRev (xiOK_split hx).1)
    (fun r _ => YModel.Sch.benesPerm_netRev r) (YModel.Sch.netOK_netRev (pout_lab hp).1)
    (fun r _ => YModel.Sch.benesPerm_netRev r) ht f

end CFSG.KC.KStep

end
