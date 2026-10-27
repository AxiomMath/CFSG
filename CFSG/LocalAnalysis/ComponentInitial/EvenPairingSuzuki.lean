module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteLinearized
public import Mathlib.FieldTheory.Finite.Trace

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Polynomial

theorem not_dvd_suzukiWeight {a i j : ℕ} (ha : 2 ≤ a) (hi : i < 2 * a + 1) (hj : j < 2 * a + 1) :
    ¬ 2 ^ (2 * a + 1) - 1 ∣ (2 ^ (a + 1) + 1) * 2 ^ i + 2 ^ j := by
  intro h
  set n := 2 * a + 1 with hn
  set N := 2 ^ n - 1 with hN
  have hNpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2n : 2 ^ n = N + 1 := by omega
  obtain ⟨k, hk, hdvd⟩ : ∃ k, k ≤ 2 * a ∧ N ∣ 2 ^ (a + 1) + 1 + 2 ^ k := by
    have h' : N ∣ ((2 ^ (a + 1) + 1) * 2 ^ i + 2 ^ j) * 2 ^ (n - i) :=
      Dvd.dvd.mul_right h _
    have hsplit : ((2 ^ (a + 1) + 1) * 2 ^ i + 2 ^ j) * 2 ^ (n - i) =
        (2 ^ (a + 1) + 1) * 2 ^ n + 2 ^ (j + (n - i)) := by
      rw [add_mul, mul_assoc, ← pow_add, ← pow_add, Nat.add_sub_cancel' hi.le]
    rw [hsplit] at h'
    rcases le_or_gt i j with hij | hij
    · refine ⟨j - i, by omega, ?_⟩
      have he : 2 ^ (j + (n - i)) = 2 ^ (j - i) * 2 ^ n := by
        rw [← pow_add]
        congr 1
        omega
      rw [he, ← add_mul, h2n, mul_add, mul_one] at h'
      exact (Nat.dvd_add_right (dvd_mul_left N _)).mp h'
    · refine ⟨j + (n - i), by omega, ?_⟩
      rw [h2n, mul_add, mul_one, add_assoc] at h'
      exact (Nat.dvd_add_right (dvd_mul_left N _)).mp h'
  have hle := Nat.le_of_dvd (by positivity) hdvd
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
  have hX : 2 ^ (m + 2 + 1) = 8 * 2 ^ m := by rw [pow_add, pow_add]; ring
  have hk' : 2 ^ k ≤ 16 * 4 ^ m := by
    calc 2 ^ k ≤ 2 ^ (2 * (m + 2)) := Nat.pow_le_pow_right (by norm_num) hk
      _ = 16 * 4 ^ m := by rw [show 2 * (m + 2) = 2 * m + 4 by ring, pow_add, pow_mul]; ring
  have hY : 2 ^ n = 32 * 4 ^ m := by
    rw [hn, show 2 * (m + 2) + 1 = 2 * m + 5 by ring, pow_add, pow_mul]; ring
  have hXY : 2 ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by norm_num) m
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

theorem seven_dvd_suzukiWeight_iff (i j : Fin 3) :
    7 ∣ (2 ^ (1 + 1) + 1) * 2 ^ (i : ℕ) + 2 ^ (j : ℕ) ↔
      (i, j) = (0, 1) ∨ (i, j) = (1, 2) ∨ (i, j) = (2, 0) := by
  revert i j
  decide

section Torus

variable {K : Type*} [Field K]

theorem sub_one_dvd_of_torus_invariant {p n e : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hK : Nat.card K = p ^ n) {B : K →+ K →+ K}
    (hB : ∀ (l : Kˣ) (w v : K), B ((l : K) ^ e * w) ((l : K) * v) = B w v)
    {c : Fin n → Fin n → K}
    (hc : ∀ w v, B w v = ∑ i, ∑ j, c i j * (w ^ p ^ (i : ℕ) * v ^ p ^ (j : ℕ)))
    {i j : Fin n} (hij : c i j ≠ 0) : p ^ n - 1 ∣ e * p ^ (i : ℕ) + p ^ (j : ℕ) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos n).ne')
  have : Fintype K := Fintype.ofFinite K
  have hlt : p ^ (n - 1) < Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, hK]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hcoef : ∀ l : Kˣ, c i j * (l : K) ^ (e * p ^ (i : ℕ) + p ^ (j : ℕ)) = c i j := by
    intro l
    have h := eq_zero_of_forall_sum_sum_mul_pow_eq_zero hlt
      (a := fun i j => c i j * (l : K) ^ (e * p ^ (i : ℕ) + p ^ (j : ℕ)) - c i j) fun w v => by
        have h1 := hB l w v
        rw [hc, hc] at h1
        simp only [sub_mul, Finset.sum_sub_distrib]
        rw [sub_eq_zero, ← h1]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    exact sub_eq_zero.mp (congrFun (congrFun h i) j)
  have hpow : ∀ l : Kˣ, l ^ (e * p ^ (i : ℕ) + p ^ (j : ℕ)) = 1 := fun l => by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact (mul_eq_left₀ hij).mp (hcoef l)
  have hexp := Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  rwa [IsCyclic.exponent_eq_card, Nat.card_units, hK] at hexp

@[expose] noncomputable def toFieldPairing [Algebra (ZMod 2) K] (b : K →+ K →+ ZMod 2) :
    K →+ K →+ K :=
  b.compr₂ (algebraMap (ZMod 2) K).toAddMonoidHom

@[simp] theorem toFieldPairing_apply [Algebra (ZMod 2) K] (b : K →+ K →+ ZMod 2) (w v : K) :
    toFieldPairing b w v = algebraMap (ZMod 2) K (b w v) :=
  rfl

theorem toFieldPairing_injective [Algebra (ZMod 2) K] :
    Function.Injective (toFieldPairing (K := K)) := fun b b' h => by
  ext w v
  exact (algebraMap (ZMod 2) K).injective (by rw [← toFieldPairing_apply, h, toFieldPairing_apply])

theorem suzuki_torus_invariant_eq_zero [Algebra (ZMod 2) K] {a : ℕ} (ha : 2 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (b : K →+ K →+ ZMod 2)
    (hb : ∀ (l : Kˣ) (w v : K), b ((l : K) ^ (2 ^ (a + 1) + 1) * w) ((l : K) * v) = b w v) :
    b = 0 := by
  obtain ⟨c, hc, -⟩ :=
    (finite_field_linearized_map_bases Nat.prime_two (by omega) hK).2.1 (toFieldPairing b)
  have hc0 : ∀ i j, c i j = 0 := fun i j => by
    by_contra hij
    exact not_dvd_suzukiWeight ha i.2 j.2 (sub_one_dvd_of_torus_invariant Nat.prime_two
      (by omega) hK (B := toFieldPairing b) (fun l w v => by simp [hb]) (fun w v => hc w v) hij)
  refine toFieldPairing_injective ?_
  ext w v
  rw [hc, toFieldPairing_apply, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, map_zero]
  simp [hc0]

end Torus

@[expose] def suzukiPairingSpace (a : ℕ) (K : Type*) [Field K] :
    Submodule (ZMod 2) (K →+ K →+ ZMod 2) where
  carrier := {b | (∀ (l : Kˣ) (w v : K),
      b ((l : K) ^ (2 ^ (a + 1) + 1) * w) ((l : K) * v) = b w v) ∧
    ∀ x y z : K, b (x ^ 2 ^ (a + 1) * y + y ^ 2 ^ (a + 1) * x) z +
      b (y ^ 2 ^ (a + 1) * z + z ^ 2 ^ (a + 1) * y) x +
      b (z ^ 2 ^ (a + 1) * x + x ^ 2 ^ (a + 1) * z) y = 0}
  add_mem' {b b'} hb hb' := ⟨fun l w v => by
      simp only [AddMonoidHom.add_apply, hb.1 l w v, hb'.1 l w v], fun x y z => by
      simp only [AddMonoidHom.add_apply]
      linear_combination hb.2 x y z + hb'.2 x y z⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => by simp⟩
  smul_mem' r b hb := ⟨fun l w v => by
      simp only [AddMonoidHom.smul_apply, hb.1 l w v], fun x y z => by
      simp only [AddMonoidHom.smul_apply, smul_eq_mul]
      rw [← mul_add, ← mul_add, hb.2 x y z, mul_zero]⟩

theorem mem_suzukiPairingSpace {a : ℕ} {K : Type*} [Field K] {b : K →+ K →+ ZMod 2} :
    b ∈ suzukiPairingSpace a K ↔ (∀ (l : Kˣ) (w v : K),
      b ((l : K) ^ (2 ^ (a + 1) + 1) * w) ((l : K) * v) = b w v) ∧
    ∀ x y z : K, b (x ^ 2 ^ (a + 1) * y + y ^ 2 ^ (a + 1) * x) z +
      b (y ^ 2 ^ (a + 1) * z + z ^ 2 ^ (a + 1) * y) x +
      b (z ^ 2 ^ (a + 1) * x + x ^ 2 ^ (a + 1) * z) y = 0 :=
  Iff.rfl

section DegreeThree

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]

theorem charP_two_of_algebra : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

@[expose] noncomputable def suzukiTracePairing (c : K) : K →+ K →+ ZMod 2 where
  toFun w :=
    { toFun := fun v => Algebra.trace (ZMod 2) K (c * w * v ^ 2)
      map_zero' := by simp
      map_add' := fun v v' => by
        have := charP_two_of_algebra (K := K)
        rw [CharTwo.add_sq, mul_add, map_add] }
  map_zero' := by ext; simp
  map_add' w w' := by ext v; simp [mul_add, add_mul]

@[simp] theorem suzukiTracePairing_apply (c w v : K) :
    suzukiTracePairing c w v = Algebra.trace (ZMod 2) K (c * w * v ^ 2) :=
  rfl

variable (hK : Nat.card K = 2 ^ 3)
include hK

omit [Field K] [Algebra (ZMod 2) K] in
theorem finite_of_card_eight : Finite K :=
  Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)

theorem finrank_eq_three_of_card_eight : Module.finrank (ZMod 2) K = 3 := by
  have := finite_of_card_eight hK
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [hK, Nat.card_zmod] at h
  exact (Nat.pow_right_injective le_rfl h).symm

omit [Algebra (ZMod 2) K] in
theorem pow_eight_of_card_eight (u : K) : u ^ 8 = u := by
  have := finite_of_card_eight hK
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card u
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem algebraMap_trace_of_card_eight (u : K) :
    algebraMap (ZMod 2) K (Algebra.trace (ZMod 2) K u) = u + u ^ 2 + u ^ 4 := by
  have := finite_of_card_eight hK
  rw [FiniteField.algebraMap_trace_eq_sum_pow, finrank_eq_three_of_card_eight hK, Nat.card_zmod]
  simp [Finset.sum_range_succ]

omit [Field K] [Algebra (ZMod 2) K] in
theorem two_pow_two_lt_card_of_card_eight [Fintype K] : 2 ^ (3 - 1) < Fintype.card K := by
  rw [← Nat.card_eq_fintype_card, hK]
  norm_num

theorem exists_eq_trace_of_torus_invariant (b : K →+ K →+ ZMod 2)
    (hb : ∀ (l : Kˣ) (w v : K), b ((l : K) ^ (2 ^ (1 + 1) + 1) * w) ((l : K) * v) = b w v) :
    ∃ c : K, ∀ w v, b w v = Algebra.trace (ZMod 2) K (c * w * v ^ 2) := by
  have hz : ∀ t : ZMod 2, t ^ 2 = t := by decide
  have := charP_two_of_algebra (K := K)
  have := finite_of_card_eight hK
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlt := two_pow_two_lt_card_of_card_eight hK
  obtain ⟨c, hc, -⟩ :=
    (finite_field_linearized_map_bases Nat.prime_two (by norm_num) hK).2.1 (toFieldPairing b)
  have hc0 : ∀ i j, ¬ ((i, j) = (0, 1) ∨ (i, j) = (1, 2) ∨ (i, j) = (2, 0)) → c i j = 0 :=
    fun i j hij => by
      by_contra h
      exact hij ((seven_dvd_suzukiWeight_iff i j).mp (sub_one_dvd_of_torus_invariant
        Nat.prime_two (by norm_num) hK (B := toFieldPairing b)
        (fun l w v => by rw [toFieldPairing_apply, toFieldPairing_apply, hb])
        (fun w v => hc w v) h))
  have hB : ∀ w v, algebraMap (ZMod 2) K (b w v) =
      c 0 1 * (w * v ^ 2) + c 1 2 * (w ^ 2 * v ^ 4) + c 2 0 * (w ^ 4 * v) := by
    intro w v
    rw [← toFieldPairing_apply, hc]
    simp only [Fin.sum_univ_three]
    rw [hc0 0 0 (by decide), hc0 0 2 (by decide), hc0 1 0 (by decide), hc0 1 1 (by decide),
      hc0 2 1 (by decide), hc0 2 2 (by decide)]
    simp
  have hsq : ∀ x : K, (c 0 1 * x + c 1 2 * x ^ 2 + c 2 0 * x ^ 4) ^ 2 =
      c 0 1 * x + c 1 2 * x ^ 2 + c 2 0 * x ^ 4 := fun x => by
    have h := hB x 1
    simp only [one_pow, mul_one] at h
    rw [← h, ← map_pow, hz]
  have h0 := eq_zero_of_forall_sum_mul_pow_eq_zero (n := 3) hlt
    (a := ![c 2 0 ^ 2 - c 0 1, c 0 1 ^ 2 - c 1 2, c 1 2 ^ 2 - c 2 0]) fun x => by
      have h := hsq x
      rw [CharTwo.add_sq, CharTwo.add_sq] at h
      have hx8 := pow_eight_of_card_eight hK x
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one,
        Fin.val_two, pow_zero, pow_one]
      linear_combination h - c 2 0 ^ 2 * hx8
  have e1 : c 0 1 = c 2 0 ^ 2 := (sub_eq_zero.mp (congrFun h0 0)).symm
  have e2 : c 1 2 = c 0 1 ^ 2 := (sub_eq_zero.mp (congrFun h0 1)).symm
  have e3 : c 2 0 = c 1 2 ^ 2 := (sub_eq_zero.mp (congrFun h0 2)).symm
  refine ⟨c 0 1, fun w v => (algebraMap (ZMod 2) K).injective ?_⟩
  rw [hB, algebraMap_trace_of_card_eight hK, e2, e3, e2]
  have hv := pow_eight_of_card_eight hK v
  linear_combination (-(c 0 1 ^ 4 * w ^ 4)) * hv

omit [Algebra (ZMod 2) K] hK in
theorem trace_jacobi_sum [Algebra (ZMod 2) K] (c x y z : K) :
    Algebra.trace (ZMod 2) K (c * (x ^ 4 * y + y ^ 4 * x) * z ^ 2) +
      Algebra.trace (ZMod 2) K (c * (y ^ 4 * z + z ^ 4 * y) * x ^ 2) +
      Algebra.trace (ZMod 2) K (c * (z ^ 4 * x + x ^ 4 * z) * y ^ 2) =
    Algebra.trace (ZMod 2) K (c * ((x ^ 4 * y + y ^ 4 * x) * z ^ 2 +
      (y ^ 4 * z + z ^ 4 * y) * x ^ 2 + (z ^ 4 * x + x ^ 4 * z) * y ^ 2)) := by
  rw [← map_add, ← map_add]
  congr 1
  ring

omit [Algebra (ZMod 2) K] in
theorem suzukiJacobiDet_sq [CharP K 2] (x y z : K) :
    ((x ^ 4 * y + y ^ 4 * x) * z ^ 2 + (y ^ 4 * z + z ^ 4 * y) * x ^ 2 +
      (z ^ 4 * x + x ^ 4 * z) * y ^ 2) ^ 2 =
    (x ^ 4 * y + y ^ 4 * x) * z ^ 2 + (y ^ 4 * z + z ^ 4 * y) * x ^ 2 +
      (z ^ 4 * x + x ^ 4 * z) * y ^ 2 := by
  have hx := pow_eight_of_card_eight hK x
  have hy := pow_eight_of_card_eight hK y
  have hz := pow_eight_of_card_eight hK z
  simp only [CharTwo.add_sq, mul_pow]
  linear_combination (y ^ 2 * z ^ 4 + z ^ 2 * y ^ 4) * hx + (z ^ 2 * x ^ 4 + x ^ 2 * z ^ 4) * hy +
    (x ^ 2 * y ^ 4 + y ^ 2 * x ^ 4) * hz

omit [Algebra (ZMod 2) K] in
theorem suzukiJacobiDet_eq_zero_or_one [CharP K 2] (x y z : K) :
    (x ^ 4 * y + y ^ 4 * x) * z ^ 2 + (y ^ 4 * z + z ^ 4 * y) * x ^ 2 +
      (z ^ 4 * x + x ^ 4 * z) * y ^ 2 = 0 ∨
    (x ^ 4 * y + y ^ 4 * x) * z ^ 2 + (y ^ 4 * z + z ^ 4 * y) * x ^ 2 +
      (z ^ 4 * x + x ^ 4 * z) * y ^ 2 = 1 := by
  have h := suzukiJacobiDet_sq hK x y z
  set d := (x ^ 4 * y + y ^ 4 * x) * z ^ 2 + (y ^ 4 * z + z ^ 4 * y) * x ^ 2 +
    (z ^ 4 * x + x ^ 4 * z) * y ^ 2
  have h' : d * (d - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

omit [Algebra (ZMod 2) K] in
theorem exists_suzukiJacobiDet_eq_one [CharP K 2] : ∃ x y z : K,
    (x ^ 4 * y + y ^ 4 * x) * z ^ 2 + (y ^ 4 * z + z ^ 4 * y) * x ^ 2 +
      (z ^ 4 * x + x ^ 4 * z) * y ^ 2 = 1 := by
  have := finite_of_card_eight hK
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlt := two_pow_two_lt_card_of_card_eight hK
  classical
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset K)) (t := Finset.univ) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
      exact (Finset.card_le_two).trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  by_contra hne
  push Not at hne
  have h0 := eq_zero_of_forall_sum_mul_pow_eq_zero (n := 3) hlt
    (a := ![ω ^ 4 + ω ^ 2, ω + ω ^ 4, ω + ω ^ 2]) fun z => by
      have h := (suzukiJacobiDet_eq_zero_or_one hK 1 ω z).resolve_right (hne 1 ω z)
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one,
        Fin.val_two, pow_zero, pow_one]
      linear_combination h
  have h3 : ω + ω ^ 2 = 0 := by simpa using congrFun h0 2
  have h2 : ω * (ω + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp h2 with h | h
  · exact hω.1 h
  · exact hω.2 (by rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq])

theorem trace_jacobi_iff (c : K) : (∀ x y z : K,
    Algebra.trace (ZMod 2) K (c * (x ^ 4 * y + y ^ 4 * x) * z ^ 2) +
      Algebra.trace (ZMod 2) K (c * (y ^ 4 * z + z ^ 4 * y) * x ^ 2) +
      Algebra.trace (ZMod 2) K (c * (z ^ 4 * x + x ^ 4 * z) * y ^ 2) = 0) ↔
    Algebra.trace (ZMod 2) K c = 0 := by
  have := charP_two_of_algebra (K := K)
  simp only [trace_jacobi_sum]
  constructor
  · intro h
    obtain ⟨x, y, z, hxyz⟩ := exists_suzukiJacobiDet_eq_one hK
    simpa [hxyz] using h x y z
  · intro h x y z
    rcases suzukiJacobiDet_eq_zero_or_one hK x y z with h0 | h1
    · rw [h0, mul_zero, map_zero]
    · rw [h1, mul_one, h]

theorem mem_suzukiPairingSpace_one_iff (b : K →+ K →+ ZMod 2) :
    b ∈ suzukiPairingSpace 1 K ↔ ∃ c : K, Algebra.trace (ZMod 2) K c = 0 ∧
      ∀ w v, b w v = Algebra.trace (ZMod 2) K (c * w * v ^ 2) := by
  have := finite_of_card_eight hK
  have : Fintype K := Fintype.ofFinite K
  rw [mem_suzukiPairingSpace]
  constructor
  · rintro ⟨hT, hJ⟩
    obtain ⟨c, hc⟩ := exists_eq_trace_of_torus_invariant hK b hT
    refine ⟨c, (trace_jacobi_iff hK c).mp fun x y z => ?_, hc⟩
    have h := hJ x y z
    simp only [hc, show (2 : ℕ) ^ (1 + 1) = 4 from rfl] at h
    exact h
  · rintro ⟨c, hc0, hc⟩
    refine ⟨fun l w v => ?_, fun x y z => ?_⟩
    · have h7 : (l : K) ^ 7 = 1 := by
        have h := FiniteField.pow_card_sub_one_eq_one (l : K) l.ne_zero
        rwa [← Nat.card_eq_fintype_card, hK] at h
      rw [hc, hc]
      congr 1
      rw [show 2 ^ (1 + 1) + 1 = 5 from rfl]
      linear_combination (c * w * v ^ 2) * h7
    · simp only [hc, show (2 : ℕ) ^ (1 + 1) = 4 from rfl]
      exact (trace_jacobi_iff hK c).mpr hc0 x y z

theorem eq_of_trace_pairing_eq {c c' : K}
    (h : ∀ w v, Algebra.trace (ZMod 2) K (c * w * v ^ 2) =
      Algebra.trace (ZMod 2) K (c' * w * v ^ 2)) : c = c' := by
  have := finite_of_card_eight hK
  have : Fintype K := Fintype.ofFinite K
  have hlt := two_pow_two_lt_card_of_card_eight hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 := eq_zero_of_forall_sum_mul_pow_eq_zero (n := 3) hlt
    (a := ![c - c', c ^ 2 - c' ^ 2, c ^ 4 - c' ^ 4]) fun w => by
      have h1 := congrArg (algebraMap (ZMod 2) K) (h w 1)
      rw [algebraMap_trace_of_card_eight hK, algebraMap_trace_of_card_eight hK] at h1
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one,
        Fin.val_two, pow_zero, pow_one]
      linear_combination h1
  exact sub_eq_zero.mp (by simpa using congrFun h0 0)

omit hK in
@[expose] noncomputable def suzukiTracePairingHom : K →ₗ[ZMod 2] (K →+ K →+ ZMod 2) where
  toFun := suzukiTracePairing
  map_add' c c' := by
    ext w v
    simp [add_mul]
  map_smul' r c := by
    ext w v
    simp only [suzukiTracePairing_apply, AddMonoidHom.smul_apply, RingHom.id_apply,
      smul_mul_assoc, map_smul]

omit hK in
@[simp] theorem suzukiTracePairingHom_apply (c : K) :
    suzukiTracePairingHom c = suzukiTracePairing c :=
  rfl

theorem trace_surjective_of_card_eight : Function.Surjective (Algebra.trace (ZMod 2) K) := by
  intro t
  refine ⟨algebraMap (ZMod 2) K t, ?_⟩
  rw [Algebra.trace_algebraMap, finrank_eq_three_of_card_eight hK]
  revert t
  decide

theorem suzukiPairingSpace_one_eq_map : suzukiPairingSpace 1 K =
    (LinearMap.ker (Algebra.trace (ZMod 2) K)).map suzukiTracePairingHom := by
  ext b
  rw [mem_suzukiPairingSpace_one_iff hK, Submodule.mem_map]
  constructor
  · rintro ⟨c, hc0, hc⟩
    exact ⟨c, hc0, by ext w v; simp [hc]⟩
  · rintro ⟨c, hc0, rfl⟩
    exact ⟨c, hc0, fun w v => rfl⟩

theorem card_ker_trace_of_card_eight :
    Nat.card (LinearMap.ker (Algebra.trace (ZMod 2) K)) = 4 := by
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (Algebra.trace (ZMod 2) K).toAddMonoidHom.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _
    (trace_surjective_of_card_eight hK)).toEquiv, Nat.card_zmod, hK] at h1
  have h2 : Nat.card (LinearMap.ker (Algebra.trace (ZMod 2) K)) =
      Nat.card (Algebra.trace (ZMod 2) K).toAddMonoidHom.ker := rfl
  omega

theorem finrank_ker_trace_of_card_eight :
    Module.finrank (ZMod 2) (LinearMap.ker (Algebra.trace (ZMod 2) K)) = 2 := by
  have := finite_of_card_eight hK
  have : Module.Finite (ZMod 2) (LinearMap.ker (Algebra.trace (ZMod 2) K)) :=
    Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := LinearMap.ker (Algebra.trace (ZMod 2) K))
  rw [card_ker_trace_of_card_eight hK, Nat.card_zmod,
    show (4 : ℕ) = 2 ^ 2 from rfl] at h
  exact (Nat.pow_right_injective le_rfl h).symm

theorem finrank_suzukiPairingSpace_one : Module.finrank (ZMod 2) (suzukiPairingSpace 1 K) = 2 := by
  have hinj : Function.Injective (suzukiTracePairingHom (K := K)) := fun c c' h =>
    eq_of_trace_pairing_eq hK fun w v => by
      have := DFunLike.congr_fun (DFunLike.congr_fun h w) v
      simpa using this
  rw [suzukiPairingSpace_one_eq_map hK,
    ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _),
    finrank_ker_trace_of_card_eight hK]

end DegreeThree

theorem even_suzuki_torus_invariant_jacobi_pairings {a : ℕ} (_ha : 1 ≤ a) {K : Type*} [Field K]
    [Algebra (ZMod 2) K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (2 ≤ a → suzukiPairingSpace a K = ⊥) ∧
    (a = 1 →
      (∀ b : K →+ K →+ ZMod 2, b ∈ suzukiPairingSpace a K ↔
        ∃ c : K, Algebra.trace (ZMod 2) K c = 0 ∧
          ∀ w v, b w v = Algebra.trace (ZMod 2) K (c * w * v ^ 2)) ∧
      (∀ c c' : K, (∀ w v, Algebra.trace (ZMod 2) K (c * w * v ^ 2) =
        Algebra.trace (ZMod 2) K (c' * w * v ^ 2)) → c = c') ∧
      Module.finrank (ZMod 2) (suzukiPairingSpace a K) = 2 ∧
      ∀ u : K, algebraMap (ZMod 2) K (Algebra.trace (ZMod 2) K u) = u + u ^ 2 + u ^ 4) := by
  refine ⟨fun ha2 => eq_bot_iff.mpr fun b hb =>
    (Submodule.mem_bot _).mpr (suzuki_torus_invariant_eq_zero ha2 hK b hb.1), ?_⟩
  rintro rfl
  exact ⟨mem_suzukiPairingSpace_one_iff hK, fun c c' h => eq_of_trace_pairing_eq hK h,
    finrank_suzukiPairingSpace_one hK, algebraMap_trace_of_card_eight hK⟩

end CFSG.LocalAnalysis.ComponentInitial
