module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5U4WLin
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3UAlg

public section

namespace CFSG.OddStandard.GH71.S55.C5U

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3U

theorem not_dvd_sub_one_of_dvd_sq_add_one {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : 1 ≤ N)
    (hpN : p ∣ N ^ 2 + 1) : ¬ p ∣ N - 1 := by
  intro h1
  have e : (N - 1) * (N + 1) + 2 = N ^ 2 + 1 := by
    zify [hN]
    ring
  rw [← e] at hpN
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
    ((Nat.dvd_add_right (h1.mul_right _)).1 hpN))

theorem not_dvd_add_one_of_dvd_sq_add_one {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : 1 ≤ N)
    (hpN : p ∣ N ^ 2 + 1) : ¬ p ∣ N + 1 := by
  intro h1
  have e : (N + 1) * (N - 1) + 2 = N ^ 2 + 1 := by
    zify [hN]
    ring
  rw [← e] at hpN
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
    ((Nat.dvd_add_right (h1.mul_right _)).1 hpN))

theorem natCast_ne_zero_of_dvd_sq_add_one {K : Type} [Field K] {r f p : ℕ} [CharP K r]
    (hr : r.Prime) (hf : 1 ≤ f) (hp : p.Prime) (hpq : p ∣ (r ^ f) ^ 2 + 1) : (p : K) ≠ 0 := by
  intro h0
  rw [CharP.cast_eq_zero_iff K r] at h0
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hr hp).1 h0
  have h1 : r ∣ (r ^ f) ^ 2 := dvd_pow (dvd_pow_self r (by omega)) two_ne_zero
  exact hr.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 hpq))

variable {r f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData r f K) {n : ℕ}

theorem stdHermForm_mulVec_mulVec {A : Matrix (Fin n) (Fin n) K} (hA : (A.map h.bar)ᵀ * A = 1)
    (x y : Fin n → K) : stdHermForm h n (A *ᵥ x) (A *ᵥ y) = stdHermForm h n x y := by
  have hbarmv : (fun i => h.bar ((A *ᵥ x) i)) = (A.map h.bar) *ᵥ (fun i => h.bar (x i)) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [stdHermForm_eq_dotProduct, stdHermForm_eq_dotProduct, hbarmv, Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hA, Matrix.vecMul_one]

theorem exists_isotropic_invariant [NeZero n] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ (r ^ f) ^ 2 + 1) {A : Matrix (Fin n) (Fin n) K} (hAu : (A.map h.bar)ᵀ * A = 1)
    (hAp : A ^ p = 1) (hA1 : A ≠ 1) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ v ∈ W, ∀ w ∈ W, stdHermForm h n v w = 0) ∧
      ∀ w ∈ W, A *ᵥ w ∈ W := by
  have : Fact r.Prime := ⟨h.prime⟩
  have : CharP K r := h.charP
  have := h.finite
  have := Fintype.ofFinite K
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_dvd_sq_add_one h.prime h.one_le hp hpq
  set N := r ^ f with hN
  have hN1 : 1 < N := Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt
  have hpN1 := not_dvd_sub_one_of_dvd_sq_add_one hp hp2 hN1.le hpq
  have hpN2 := not_dvd_add_one_of_dvd_sq_add_one hp hp2 hN1.le hpq
  set B := A ^ (N ^ 2) with hB
  have hAQ : A ^ (N ^ 2 + 1) = 1 := by
    obtain ⟨c, hc⟩ := hpq
    rw [hc, pow_mul, hAp, one_pow]
  have hAB : A * B = 1 := by rw [hB, ← pow_succ']; exact hAQ
  have hBA : B * A = 1 := by rw [hB, ← pow_succ]; exact hAQ
  have hcomm : Commute A B := Commute.self_pow A _
  have frob : ∀ e : ℕ, (A + B) ^ r ^ e = A ^ r ^ e + B ^ r ^ e := fun e =>
    add_pow_char_pow_of_commute r e hcomm
  have hBB : B ^ (N ^ 2) = A := by
    have h1 : B ^ (N ^ 2) * B = 1 := by
      change B ^ (N ^ 2) * A ^ (N ^ 2) = 1
      rw [← hcomm.symm.mul_pow, hBA, one_pow]
    calc B ^ (N ^ 2) = B ^ (N ^ 2) * (B * A) := by rw [hBA, mul_one]
      _ = A := by rw [← mul_assoc, h1, one_mul]
  have hTQ : (A + B) ^ Fintype.card K = A + B := by
    have hc : Fintype.card K = r ^ (f * 2) := by
      rw [← Nat.card_eq_fintype_card, h.card_eq_sq, ← pow_mul]
    rw [hc, frob, pow_mul, ← hN, ← hB, hBB, add_comm]
  by_cases hTN : (A + B) ^ N = A + B
  · exfalso
    have hfr : A ^ N + B ^ N = A + B := by rw [← hTN, hN, frob]
    set a := A ^ N with ha
    set d := A ^ (N - 1) with hd
    have hda : d * A = a := by rw [hd, ← pow_succ, Nat.sub_add_cancel hN1.le]
    have hAd : A * d = a := by rw [hd, ← pow_succ', Nat.sub_add_cancel hN1.le]
    have haB : a * B = d := by rw [← hda, mul_assoc, hAB, mul_one]
    have haBN : a * B ^ N = 1 := by rw [ha, ← hcomm.mul_pow, hAB, one_pow]
    have e1 : a * (a + B ^ N) = a * (A + B) := by rw [hfr]
    rw [mul_add, mul_add, haBN, haB] at e1
    have key : (A ^ (N + 1) - 1) * (d - 1) = 0 := by
      have hcd : A ^ (N + 1) * d = a * a := by rw [pow_succ, mul_assoc, hAd]
      calc (A ^ (N + 1) - 1) * (d - 1) = A ^ (N + 1) * d - A ^ (N + 1) - d + 1 := by
            noncomm_ring
        _ = a * a + 1 - (a * A + d) := by rw [hcd, pow_succ]; abel
        _ = 0 := by rw [e1, sub_self]
    obtain ⟨k, hk⟩ := exists_pow_pow_eq hp hAp hpN2
    obtain ⟨j, hj⟩ := exists_pow_pow_eq hp hAp hpN1
    have hAd0 : (A - 1) * (d - 1) = 0 := by
      have e2 := geom_sum_mul (A ^ (N + 1)) k
      rw [hk] at e2
      rw [← e2, mul_assoc, key, mul_zero]
    have hdd : (d - 1) * (d - 1) = 0 := by
      have e3 := geom_sum_mul A (N - 1)
      rw [← hd] at e3
      rw [show (d - 1) * (d - 1) = (∑ i ∈ Finset.range (N - 1), A ^ i) * (A - 1) * (d - 1) by
        rw [e3], mul_assoc, hAd0, mul_zero]
    have hdp : d ^ p = 1 := by rw [hd, ← pow_mul, mul_comm, pow_mul, hAp, one_pow]
    have hd1 : d = 1 := eq_one_of_pow_eq_one_of_sq hpK hdp hdd
    exact hA1 (by rw [← hj, ← hd, hd1, one_pow])
  · obtain ⟨β, hβN, hdet⟩ := exists_det_eq_zero hN1 hTQ hTN
    set M := (A + B) - algebraMap K (Matrix (Fin n) (Fin n) K) β with hM
    have hmem : ∀ v, M *ᵥ v = 0 ↔ (A + B) *ᵥ v = β • v := by
      intro v
      rw [hM, sub_mulVec, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec, sub_eq_zero]
    refine ⟨LinearMap.ker (Matrix.toLin' M), ?_, ?_, ?_⟩
    · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
      exact (Submodule.ne_bot_iff _).2 ⟨v, by rwa [LinearMap.mem_ker, Matrix.toLin'_apply], hv0⟩
    · intro v hv w hw
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, hmem] at hv hw
      have hadjA : ∀ x y, stdHermForm h n (A *ᵥ x) y = stdHermForm h n x (B *ᵥ y) := by
        intro x y
        conv_lhs => rw [show y = A *ᵥ (B *ᵥ y) by rw [mulVec_mulVec, hAB, one_mulVec]]
        exact stdHermForm_mulVec_mulVec h hAu x (B *ᵥ y)
      have hadjB : ∀ x y, stdHermForm h n (B *ᵥ x) y = stdHermForm h n x (A *ᵥ y) := by
        intro x y
        rw [← bar_stdHermForm h, ← hadjA, bar_stdHermForm h]
      have hT : stdHermForm h n ((A + B) *ᵥ v) w = stdHermForm h n v ((A + B) *ᵥ w) := by
        rw [add_mulVec, add_mulVec, map_add, LinearMap.add_apply, hadjA, hadjB, map_add,
          add_comm]
      rw [hv, hw, stdHermForm_smul_left, stdHermForm_smul_right] at hT
      have hβ' : h.bar β ≠ β := by rwa [h.bar_apply]
      have e4 := sub_eq_zero.2 hT
      rw [← sub_mul] at e4
      exact (mul_eq_zero.1 e4).resolve_left (sub_ne_zero.2 hβ')
    · intro w hw
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hw ⊢
      have hMA : M * A = A * M := by
        rw [hM, sub_mul, mul_sub, add_mul, mul_add, hcomm.eq, Algebra.commutes]
      rw [mulVec_mulVec, hMA, ← mulVec_mulVec, hw, mulVec_zero]

end CFSG.OddStandard.GH71.S55.C5U
