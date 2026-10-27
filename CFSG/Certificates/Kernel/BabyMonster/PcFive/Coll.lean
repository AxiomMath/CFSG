module

public import Certificates.Data.Kernel.BabyMonster.PcFive
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KC.BM.PcFive

variable {G : Type*} [Group G]

structure QRel (m : CM) (q : Fin 4 → G) (z : G) : Prop where
  z5 : z ^ 5 = 1
  q5 : ∀ i, q i ^ 5 = 1
  zc : ∀ i, z * q i = q i * z
  s01 : q 1 * q 0 = q 0 * q 1 * z ^ m.m01
  s02 : q 2 * q 0 = q 0 * q 2 * z ^ m.m02
  s03 : q 3 * q 0 = q 0 * q 3 * z ^ m.m03
  s12 : q 2 * q 1 = q 1 * q 2 * z ^ m.m12
  s13 : q 3 * q 1 = q 1 * q 3 * z ^ m.m13
  s23 : q 3 * q 2 = q 2 * q 3 * z ^ m.m23

@[expose] def nfQ (q : Fin 4 → G) (z : G) (a : QV) : G :=
  q 0 ^ a.a0 * q 1 ^ a.a1 * q 2 ^ a.a2 * q 3 ^ a.a3 * z ^ a.c

theorem pow_mod_five {g : G} (h : g ^ 5 = 1) (n : ℕ) : g ^ n = g ^ (n % 5) := by
  conv_lhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, h, one_pow, one_mul]

theorem swap_pow {a b z : G} {m : ℕ} (ha : z * a = a * z) (hb : z * b = b * z)
    (h : b * a = a * b * z ^ m) (k l : ℕ) : b ^ k * a ^ l = a ^ l * b ^ k * z ^ (l * k * m) := by
  have hza : ∀ n, z ^ n * a = a * z ^ n := fun n => ((Commute.pow_left ha n).eq)
  have hzb : ∀ n, z ^ n * b = b * z ^ n := fun n => ((Commute.pow_left hb n).eq)
  have h1 : ∀ l : ℕ, b * a ^ l = a ^ l * b * z ^ (l * m) := by
    intro l
    induction l with
    | zero => simp
    | succ l ih =>
      calc b * a ^ (l + 1) = (b * a ^ l) * a := by rw [pow_succ, mul_assoc]
        _ = a ^ l * b * (z ^ (l * m) * a) := by rw [ih]; simp only [mul_assoc]
        _ = a ^ l * (b * a) * z ^ (l * m) := by rw [hza]; simp only [mul_assoc]
        _ = a ^ (l + 1) * b * z ^ ((l + 1) * m) := by
          rw [h, pow_succ, add_mul, one_mul, pow_add]
          simp only [mul_assoc]
          rw [← pow_add, ← pow_add, add_comm]
  have hzbk : ∀ n k : ℕ, z ^ n * b ^ k = b ^ k * z ^ n := fun n k =>
    ((Commute.pow_right (Commute.pow_left hb n) k).eq)
  induction k with
  | zero => simp
  | succ k ih =>
    calc b ^ (k + 1) * a ^ l = b * (b ^ k * a ^ l) := by rw [pow_succ', mul_assoc]
      _ = (b * a ^ l) * b ^ k * z ^ (l * k * m) := by rw [ih]; simp only [mul_assoc]
      _ = a ^ l * b * (z ^ (l * m) * b ^ k) * z ^ (l * k * m) := by
        rw [h1]; simp only [mul_assoc]
      _ = a ^ l * b ^ (k + 1) * z ^ (l * (k + 1) * m) := by
        rw [hzbk, pow_succ' b k]
        simp only [mul_assoc]
        rw [← pow_add]
        congr 4
        ring

section Q

variable {m : CM} {q : Fin 4 → G} {z : G}

theorem QRel.zq (h : QRel m q z) (i : Fin 4) (n l : ℕ) : z ^ n * q i ^ l = q i ^ l * z ^ n :=
  (Commute.pow_pow (h.zc i) n l).eq

theorem QRel.zq_assoc (h : QRel m q z) (i : Fin 4) (n l : ℕ) (X : G) :
    z ^ n * (q i ^ l * X) = q i ^ l * (z ^ n * X) := by
  rw [← mul_assoc, h.zq, mul_assoc]

theorem pow_pow_assoc (g : G) (a b : ℕ) (X : G) : g ^ a * (g ^ b * X) = g ^ (a + b) * X := by
  rw [← mul_assoc, ← pow_add]

theorem swap_assoc {a b z : G} {m : ℕ} (ha : z * a = a * z) (hb : z * b = b * z)
    (h : b * a = a * b * z ^ m) (k l : ℕ) (X : G) :
    b ^ k * (a ^ l * X) = a ^ l * (b ^ k * (z ^ (l * k * m) * X)) := by
  rw [← mul_assoc, swap_pow ha hb h]
  simp only [mul_assoc]

theorem nfQ_mul (h : QRel m q z) (a b : QV) : nfQ q z a * nfQ q z b = nfQ q z (mulQ m a b) := by
  have w01 := swap_assoc (h.zc 0) (h.zc 1) h.s01
  have w02 := swap_assoc (h.zc 0) (h.zc 2) h.s02
  have w03 := swap_assoc (h.zc 0) (h.zc 3) h.s03
  have w12 := swap_assoc (h.zc 1) (h.zc 2) h.s12
  have w13 := swap_assoc (h.zc 1) (h.zc 3) h.s13
  have w23 := swap_assoc (h.zc 2) (h.zc 3) h.s23
  have zz : ∀ (a b : ℕ) (X : G), z ^ a * (z ^ b * X) = z ^ (a + b) * X := pow_pow_assoc z
  have qq : ∀ (i : Fin 4) (a b : ℕ) (X : G), q i ^ a * (q i ^ b * X) = q i ^ (a + b) * X :=
    fun i => pow_pow_assoc (q i)
  have zq := h.zq_assoc
  unfold nfQ mulQ
  simp only [mul_assoc, w01, w02, w03, w12, w13, w23, zz, qq, zq, ← pow_add]
  rw [pow_mod_five (h.q5 0) (a.a0 + b.a0), pow_mod_five (h.q5 1) (a.a1 + b.a1),
    pow_mod_five (h.q5 2) (a.a2 + b.a2), pow_mod_five (h.q5 3) (a.a3 + b.a3), pow_mod_five h.z5]
  congr 6
  ring

theorem nfQ_one : nfQ q z QV.one = 1 := by simp [nfQ, QV.one]

theorem nfQ_pow (h : QRel m q z) (r : QV) : ∀ k : ℕ, nfQ q z r ^ k = nfQ q z (powQ m r k)
  | 0 => by rw [pow_zero, powQ, nfQ_one]
  | k + 1 => by rw [pow_succ, nfQ_pow h r k, powQ, nfQ_mul h]

theorem map_nfQ (h : QRel m q z) {f : G →* G} {A : QAct} (h0 : f (q 0) = nfQ q z A.r0)
    (h1 : f (q 1) = nfQ q z A.r1) (h2 : f (q 2) = nfQ q z A.r2) (h3 : f (q 3) = nfQ q z A.r3)
    (hz : f z = nfQ q z A.rz) (a : QV) : f (nfQ q z a) = nfQ q z (applyQ m A a) := by
  unfold applyQ
  rw [← nfQ_mul h, ← nfQ_mul h, ← nfQ_mul h, ← nfQ_mul h, ← nfQ_pow h, ← nfQ_pow h,
    ← nfQ_pow h, ← nfQ_pow h, ← nfQ_pow h, ← h0, ← h1, ← h2, ← h3, ← hz]
  unfold nfQ
  simp only [map_mul, map_pow]

@[expose] def conjInv (g : G) : G →* G := (MulAut.conj g⁻¹).toMonoidHom

theorem conjInv_apply (g y : G) : conjInv g y = g⁻¹ * y * g := by
  simp [conjInv, MulAut.conj_apply]

theorem conj_nfQ (h : QRel m q z) {g : G} {A : QAct} (h0 : g⁻¹ * q 0 * g = nfQ q z A.r0)
    (h1 : g⁻¹ * q 1 * g = nfQ q z A.r1) (h2 : g⁻¹ * q 2 * g = nfQ q z A.r2)
    (h3 : g⁻¹ * q 3 * g = nfQ q z A.r3) (hz : g⁻¹ * z * g = nfQ q z A.rz) (a : QV) :
    g⁻¹ * nfQ q z a * g = nfQ q z (applyQ m A a) := by
  rw [← conjInv_apply]
  exact map_nfQ h (by rw [conjInv_apply, h0]) (by rw [conjInv_apply, h1])
    (by rw [conjInv_apply, h2]) (by rw [conjInv_apply, h3]) (by rw [conjInv_apply, hz]) a

end Q

theorem decQ_red (n : ℕ) : (decQ n).red := by
  unfold decQ QV.red
  refine ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

@[expose] def encQ (a : QV) : ℕ := 625 * a.a0 + 125 * a.a1 + 25 * a.a2 + 5 * a.a3 + a.c

theorem decQ_encQ {a : QV} (h : a.red) : decQ (encQ a) = a := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  unfold decQ encQ
  cases a
  simp only at h0 h1 h2 h3 h4 ⊢
  congr 1 <;> omega

theorem encQ_lt {a : QV} (h : a.red) : encQ a < 3125 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  unfold encQ
  omega

theorem QV.beq_eq {a b : QV} (h : a.beq b = true) : a = b := by
  unfold QV.beq at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  cases a
  cases b
  simp only at h0 h1 h2 h3 h4
  subst h0 h1 h2 h3 h4
  rfl

theorem QV.beq_self (a : QV) : a.beq a = true := by
  simp [QV.beq]

theorem mulQ_red (m : CM) (a b : QV) : (mulQ m a b).red := by
  unfold mulQ QV.red
  refine ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

theorem evalQF_red (F : QF) (a : QV) : (evalQF F a).red := by
  unfold evalQF QV.red
  refine ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

theorem allBelow_spec {f : ℕ → Bool} : ∀ {k : ℕ}, allBelow f k = true → ∀ n < k, f n = true
  | 0, _, n, hn => absurd hn (Nat.not_lt_zero n)
  | k + 1, h, n, hn => by
    unfold allBelow at h
    rw [Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
    · exact allBelow_spec h.2 n hn
    · exact h.1

theorem phi_spec (h : phiOK () = true) {a : QV} (ha : a.red) :
    evalQF phi1 a = applyQ cmFive xAct a ∧ evalQF phi2 a = evalQF phi1 (evalQF phi1 a) ∧
      evalQF phi3 a = evalQF phi2 (evalQF phi1 a) ∧
      evalQF phi4 a = evalQF phi3 (evalQF phi1 a) := by
  have h1 := allBelow_spec h _ (encQ_lt ha)
  rw [decQ_encQ ha] at h1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := h1
  exact ⟨QV.beq_eq e1, QV.beq_eq e2, QV.beq_eq e3, QV.beq_eq e4⟩

structure PcHyp (x : G) (q : Fin 4 → G) (z : G) : Prop where
  rel : QRel cmFive q z
  x5 : x ^ 5 = 1
  x0 : x⁻¹ * q 0 * x = nfQ q z xAct.r0
  x1 : x⁻¹ * q 1 * x = nfQ q z xAct.r1
  x2 : x⁻¹ * q 2 * x = nfQ q z xAct.r2
  x3 : x⁻¹ * q 3 * x = nfQ q z xAct.r3
  xz : x⁻¹ * z * x = nfQ q z xAct.rz

@[expose] def psi (x : G) (q : Fin 4 → G) (z : G) (v : V6) : G := x ^ v.e * nfQ q z v.q

variable {x : G} {q : Fin 4 → G} {z : G}

theorem PcHyp.conjX (H : PcHyp x q z) (a : QV) :
    x⁻¹ * nfQ q z a * x = nfQ q z (applyQ cmFive xAct a) :=
  conj_nfQ H.rel H.x0 H.x1 H.x2 H.x3 H.xz a

theorem conj_pow_succ (g y : G) (k : ℕ) :
    (g ^ (k + 1))⁻¹ * y * g ^ (k + 1) = (g ^ k)⁻¹ * (g⁻¹ * y * g) * g ^ k := by
  rw [pow_succ', mul_inv_rev]
  group

theorem PcHyp.conjX_pow (H : PcHyp x q z) (hφ : phiOK () = true) {k : ℕ} (hk : k < 5) {a : QV}
    (ha : a.red) : (x ^ k)⁻¹ * nfQ q z a * x ^ k = nfQ q z (phiAt k a) := by
  have g1 : ∀ b : QV, b.red → x⁻¹ * nfQ q z b * x = nfQ q z (evalQF phi1 b) := fun b hb => by
    rw [H.conjX, (phi_spec hφ hb).1]
  have g2 : ∀ b : QV, b.red → (x ^ 2)⁻¹ * nfQ q z b * x ^ 2 = nfQ q z (evalQF phi2 b) :=
    fun b hb => by
      rw [conj_pow_succ, pow_one, g1 b hb, g1 _ (evalQF_red _ _), (phi_spec hφ hb).2.1]
  have g3 : ∀ b : QV, b.red → (x ^ 3)⁻¹ * nfQ q z b * x ^ 3 = nfQ q z (evalQF phi3 b) :=
    fun b hb => by
      rw [conj_pow_succ, g1 b hb, g2 _ (evalQF_red _ _), (phi_spec hφ hb).2.2.1]
  have g4 : ∀ b : QV, b.red → (x ^ 4)⁻¹ * nfQ q z b * x ^ 4 = nfQ q z (evalQF phi4 b) :=
    fun b hb => by
      rw [conj_pow_succ, g1 b hb, g3 _ (evalQF_red _ _), (phi_spec hφ hb).2.2.2]
  interval_cases k
  · simp [phiAt]
  · rw [pow_one]
    exact g1 a ha
  · exact g2 a ha
  · exact g3 a ha
  · exact g4 a ha

theorem mulV_red (v w : V6) : (mulV v w).red := ⟨Nat.mod_lt _ (by norm_num), mulQ_red _ _ _⟩

theorem one_red : V6.one.red := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [V6.one, QV.one]

theorem powV_red (v : V6) : ∀ k, (powV v k).red
  | 0 => one_red
  | _ + 1 => mulV_red _ _

theorem dec_red (i : ℕ) : (dec i).red := ⟨Nat.mod_lt _ (by norm_num), decQ_red _⟩

@[expose] def enc (v : V6) : ℕ := 3125 * v.e + encQ v.q

theorem dec_enc {v : V6} (h : v.red) : dec (enc v) = v := by
  have hq := encQ_lt h.2
  have he := h.1
  unfold dec enc
  have e1 : (3125 * v.e + encQ v.q) / 3125 % 5 = v.e := by omega
  have e2 : (3125 * v.e + encQ v.q) % 3125 = encQ v.q := by omega
  rw [e1, e2, decQ_encQ h.2]

theorem enc_lt {v : V6} (h : v.red) : enc v < 15625 := by
  have hq := encQ_lt h.2
  have he := h.1
  unfold enc
  omega

theorem enc_dec {i : ℕ} (hi : i < 15625) : enc (dec i) = i := by
  unfold enc dec encQ decQ
  simp only
  omega

theorem V6.beq_eq {v w : V6} (h : v.beq w = true) : v = w := by
  unfold V6.beq at h
  rw [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h1, h2⟩ := h
  cases v
  cases w
  simp only at h1 h2
  rw [h1, QV.beq_eq h2]

theorem V6.beq_self (v : V6) : v.beq v = true := by
  simp [V6.beq, QV.beq_self]

theorem psi_one : psi x q z V6.one = 1 := by
  simp [psi, V6.one, nfQ_one]

theorem PcHyp.psi_mul (H : PcHyp x q z) (hφ : phiOK () = true) {v w : V6} (hv : v.red)
    (hw : w.red) : psi x q z v * psi x q z w = psi x q z (mulV v w) := by
  unfold psi mulV
  simp only
  rw [← nfQ_mul H.rel, ← H.conjX_pow hφ hw.1 hv.2, ← pow_mod_five H.x5, pow_add]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem PcHyp.psi_pow (H : PcHyp x q z) (hφ : phiOK () = true) {v : V6} (hv : v.red) :
    ∀ k, psi x q z v ^ k = psi x q z (powV v k)
  | 0 => by rw [pow_zero, powV, psi_one]
  | k + 1 => by rw [pow_succ, H.psi_pow hφ hv k, powV, H.psi_mul hφ (powV_red _ _) hv]

theorem PcHyp.conj_alpha (H : PcHyp x q z) (hφ : phiOK () = true) {g : G} {ws : List ℕ}
    (hx : g * x * g⁻¹ = psi x q z (dec (nth ws 0)))
    (h0 : g * q 0 * g⁻¹ = psi x q z (dec (nth ws 1)))
    (h1 : g * q 1 * g⁻¹ = psi x q z (dec (nth ws 2)))
    (h2 : g * q 2 * g⁻¹ = psi x q z (dec (nth ws 3)))
    (h3 : g * q 3 * g⁻¹ = psi x q z (dec (nth ws 4)))
    (hz : g * z * g⁻¹ = psi x q z (dec (nth ws 5))) (v : V6) :
    g * psi x q z v * g⁻¹ = psi x q z (alphaV ws v) := by
  unfold alphaV
  rw [← H.psi_mul hφ (mulV_red _ _) (powV_red _ _), ← H.psi_mul hφ (mulV_red _ _) (powV_red _ _),
    ← H.psi_mul hφ (mulV_red _ _) (powV_red _ _), ← H.psi_mul hφ (mulV_red _ _) (powV_red _ _),
    ← H.psi_mul hφ (powV_red _ _) (powV_red _ _), ← H.psi_pow hφ (dec_red _),
    ← H.psi_pow hφ (dec_red _), ← H.psi_pow hφ (dec_red _), ← H.psi_pow hφ (dec_red _),
    ← H.psi_pow hφ (dec_red _), ← H.psi_pow hφ (dec_red _), ← hx, ← h0, ← h1, ← h2, ← h3, ← hz,
    ← MulAut.conj_apply]
  unfold psi nfQ
  simp only [map_mul, map_pow, MulAut.conj_apply, mul_assoc]

end CFSG.KC.BM.PcFive

end
