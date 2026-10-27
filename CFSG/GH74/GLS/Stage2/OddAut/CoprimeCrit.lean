module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Matrix.Basic

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Matrix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_mulVec_ne_zero {M : Matrix ι ι K} (hM : M ≠ 0) : ∃ v, M *ᵥ v ≠ 0 := by
  by_contra h
  push Not at h
  apply hM
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

theorem exists_mem_ker_range_of_nilpotent {N : Matrix ι ι K} {n : ℕ} (hN : N ^ n = 0)
    (hne : N ≠ 0) :
    ∃ e : ι → K, e ≠ 0 ∧ N *ᵥ e = 0 ∧ ∃ v, N *ᵥ v = e := by
  classical
  have hex : ∃ k, N ^ k = 0 := ⟨n, hN⟩
  set k := Nat.find hex with hk
  have hk0 : N ^ k = 0 := Nat.find_spec hex
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    rw [this, pow_zero] at hk0
    apply hne
    ext i j
    have : (1 : Matrix ι ι K) i i = 0 := by rw [hk0]; rfl
    simp at this
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k = 1 := by omega
    rw [this, pow_one] at hk0
    exact hne hk0
  have hmin : N ^ (k - 1) ≠ 0 := Nat.find_min hex (by omega)
  obtain ⟨v, hv⟩ := exists_mulVec_ne_zero hmin
  refine ⟨N ^ (k - 1) *ᵥ v, hv, ?_, N ^ (k - 2) *ᵥ v, ?_⟩
  · rw [Matrix.mulVec_mulVec, ← pow_succ', show k - 1 + 1 = k by omega, hk0, Matrix.zero_mulVec]
  · rw [Matrix.mulVec_mulVec, ← pow_succ', show k - 2 + 1 = k - 1 by omega]

theorem eq_one_of_commute_nilpotent_ker {A' N : Matrix ι ι K} {n m : ℕ} (hAN : A' * N = N * A')
    (hN : N ^ n = 0) (hker : ∀ v, N *ᵥ v = 0 → A' *ᵥ v = v) (hA : A' ^ m = 1) (hm : (m : K) ≠ 0) :
    A' = 1 := by
  classical
  by_contra hne
  have hT : A' - 1 ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨v, hv⟩ := exists_mulVec_ne_zero hT
  have hcomm : ∀ j : ℕ, (A' - 1) * N ^ j = N ^ j * (A' - 1) := by
    intro j
    have : Commute (A' - 1) N := by
      rw [Commute, SemiconjBy, sub_mul, mul_sub, hAN, one_mul, mul_one]
    exact (this.pow_right j).eq
  have hex : ∃ k, N ^ k *ᵥ ((A' - 1) *ᵥ v) = 0 := ⟨n, by rw [hN, Matrix.zero_mulVec]⟩
  set k := Nat.find hex with hk
  have hk0 : N ^ k *ᵥ ((A' - 1) *ᵥ v) = 0 := Nat.find_spec hex
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    rw [this, pow_zero, Matrix.one_mulVec] at hk0
    exact hv hk0
  have hmin : N ^ (k - 1) *ᵥ ((A' - 1) *ᵥ v) ≠ 0 := Nat.find_min hex (by omega)
  set w := N ^ (k - 1) *ᵥ ((A' - 1) *ᵥ v) with hw
  have hNw : N *ᵥ w = 0 := by
    rw [hw, Matrix.mulVec_mulVec, ← pow_succ', show k - 1 + 1 = k by omega, hk0]
  have hAw : A' *ᵥ w = w := hker w hNw
  set u := N ^ (k - 1) *ᵥ v with hu
  have hwu : (A' - 1) *ᵥ u = w := by
    rw [hu, hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hcomm]
  have hpow : ∀ i : ℕ, A' ^ i *ᵥ w = w := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hAw, ih]
  have hgeom := geom_sum_mul A' m
  rw [hA, sub_self] at hgeom
  have h1 := congrArg (fun M : Matrix ι ι K => M *ᵥ u) hgeom
  simp only [← Matrix.mulVec_mulVec, hwu, Matrix.zero_mulVec] at h1
  have h2 : (∑ i ∈ Finset.range m, A' ^ i) *ᵥ w = (m : K) • w := by
    rw [Matrix.sum_mulVec]
    simp only [hpow, Finset.sum_const, Finset.card_range]
    exact (Nat.cast_smul_eq_nsmul K m w).symm
  rw [h2] at h1
  exact hmin ((smul_eq_zero.mp h1).resolve_left hm)

end CFSG.GH74.GLS.Stage2.OddAut
