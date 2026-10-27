module

import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix QuadraticMap

variable {K : Type} [Field K]

private theorem two_ne_zero_of_ringChar_ne_two [Finite K] (hK : ringChar K ≠ 2) :
    (2 : K) ≠ 0 := by
  intro h
  exact hK (by
    haveI : CharP K 2 := CFSG.GroupTheory.WeirSylow.charP_two_of_two_eq_zero h
    exact ringChar.eq K 2)

private theorem polarBilin_toQuadraticForm'_one_nondegenerate [Finite K]
    (hK : ringChar K ≠ 2) :
    (polarBilin (Matrix.toQuadraticForm' (1 : Matrix (Fin 3) (Fin 3) K))).Nondegenerate := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_ringChar_ne_two hK
  constructor
  · intro x hx
    funext i
    have h := hx (Pi.single i 1)
    simp only [polarBilin_apply_apply, TauCeti.polar_toQuadraticForm'_one,
      dotProduct_single_one] at h
    exact (mul_eq_zero.mp h).resolve_left h2
  · intro y hy
    funext j
    have h := hy (Pi.single j 1)
    simp only [polarBilin_apply_apply, TauCeti.polar_toQuadraticForm'_one, single_dotProduct,
      one_mul] at h
    exact (mul_eq_zero.mp h).resolve_left h2

private theorem natCard_orthogonalGroup_toQuadraticForm'_one [Finite K]
    (hK : ringChar K ≠ 2) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (Matrix.toQuadraticForm' (1 : Matrix (Fin 3) (Fin 3) K))) =
      2 * Nat.card K * (Nat.card K ^ 2 - 1) := by
  have hQ := polarBilin_toQuadraticForm'_one_nondegenerate (K := K) hK
  have hdim : Module.finrank K (Fin 3 → K) = 2 * 1 + 1 := by
    rw [Module.finrank_fin_fun]
  have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (K := K)
    (V := Fin 3 → K) hK hQ hdim
  simp only [pow_one, one_pow, Finset.Icc_self, Finset.prod_singleton] at hcard
  have hq : 1 ≤ Nat.card K ^ 2 :=
    one_le_pow₀ (le_of_lt (Finite.one_lt_card (α := K)))
  have hcast : ((2 * Nat.card K * (Nat.card K ^ 2 - 1) : ℕ) : ℤ) =
      2 * (Nat.card K : ℤ) * ((Nat.card K : ℤ) ^ 2 - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hq, Nat.cast_pow]
    norm_num
  rw [← hcast] at hcard
  exact_mod_cast hcard

private theorem dotProduct_mulVec_of_transpose_mul' {A : Matrix (Fin 3) (Fin 3) K}
    (hA : Aᵀ * A = 1) (x y : Fin 3 → K) : (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hA,
    Matrix.one_mulVec]

theorem exists_orthogonal_orderOf_eq [Finite K] (hK : ringChar K ≠ 2) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hdvd : ℓ ∣ Nat.card K * (Nat.card K ^ 2 - 1)) :
    ∃ A : Matrix.GeneralLinearGroup (Fin 3) K,
      (A : Matrix (Fin 3) (Fin 3) K)ᵀ * A = 1 ∧ orderOf A = ℓ := by
  let Q : QuadraticMap K (Fin 3 → K) K :=
    Matrix.toQuadraticForm' (1 : Matrix (Fin 3) (Fin 3) K)
  have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      2 * Nat.card K * (Nat.card K ^ 2 - 1) :=
    natCard_orthogonalGroup_toQuadraticForm'_one (K := K) hK
  have hdvdG : ℓ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [hcard]
    simpa only [mul_assoc] using dvd_mul_of_dvd_right hdvd 2
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Finite (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    Finite.of_injective (TauCeti.QuadraticMap.orthogonalToGeneralLinear Q)
      (TauCeti.QuadraticMap.orthogonalToGeneralLinear_injective Q)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
    (G := TauCeti.QuadraticMap.orthogonalGroup Q) ℓ hdvdG
  refine ⟨TauCeti.QuadraticMap.orthogonalToGeneralLinear Q g, ?_, ?_⟩
  · have h2 : (2 : K) ≠ 0 := two_ne_zero_of_ringChar_ne_two hK
    have hreg : IsSMulRegular K (2 : K) := by
      rw [isSMulRegular_iff_right_eq_zero_of_smul]
      intro m hm
      exact (mul_eq_zero.mp (by simpa only [smul_eq_mul] using hm)).resolve_left h2
    have hmem : LinearMap.toMatrix'
        (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)).toLinearMap ∈ Matrix.orthogonalGroup (Fin 3) K :=
      (TauCeti.toMatrix_mem_orthogonalGroup_iff K (Fin 3) hreg
        (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))).2 g.2
    have hmat := (Matrix.mem_orthogonalGroup_iff' (Fin 3) K).1 hmem
    rw [TauCeti.QuadraticMap.coe_orthogonalToGeneralLinear]
    exact hmat
  · rw [orderOf_injective (TauCeti.QuadraticMap.orthogonalToGeneralLinear Q)
      (TauCeti.QuadraticMap.orthogonalToGeneralLinear_injective Q) g, hg]

private theorem exists_pow_ne_zero_and_succ_eq_zero {N : Matrix (Fin 3) (Fin 3) K}
    (hNne : N ≠ 0) (hNil : ∃ k, N ^ (k + 1) = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ N ^ m ≠ 0 ∧ N ^ (m + 1) = 0 := by
  classical
  let m := Nat.find hNil
  have hm_spec : N ^ (m + 1) = 0 := Nat.find_spec hNil
  have hm_min : ∀ k < m, N ^ (k + 1) ≠ 0 := fun k hk => Nat.find_min hNil hk
  have hm_pos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    rw [hm0] at hm_spec
    exact hNne (by simpa using hm_spec)
  have hm1 : 1 ≤ m := hm_pos
  have hNm : N ^ m ≠ 0 := by
    have h := hm_min (m - 1) (by omega)
    rwa [Nat.sub_add_cancel hm1] at h
  exact ⟨m, hm1, hNm, hm_spec⟩

private theorem exists_isotropic_fixed_of_sub_nilpotent
    {M N : Matrix (Fin 3) (Fin 3) K} (hMorth : Mᵀ * M = 1) (hNdef : N = M - 1)
    (hNne : N ≠ 0) (hNil : ∃ k, N ^ (k + 1) = 0) :
    ∃ x : Fin 3 → K, x ≠ 0 ∧ x ⬝ᵥ x = 0 ∧ M *ᵥ x = x := by
  obtain ⟨m, hm1, hNm, hm_spec⟩ := exists_pow_ne_zero_and_succ_eq_zero hNne hNil
  obtain ⟨i, j, hij⟩ : ∃ i j, (N ^ m) i j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    exact hNm (by ext i j; exact h i j)
  let v : Fin 3 → K := Pi.single j 1
  have hvdef : v = (Pi.single j 1 : Fin 3 → K) := rfl
  have hv : N ^ m *ᵥ v ≠ 0 := by
    intro hzero
    have hcol : (N ^ m *ᵥ v) i = 0 := congrFun hzero i
    rw [hvdef, Matrix.mulVec_single_one, Matrix.col_apply] at hcol
    exact hij hcol
  let y : Fin 3 → K := N ^ (m - 1) *ᵥ v
  let x : Fin 3 → K := N ^ m *ᵥ v
  have hx_ne : x ≠ 0 := hv
  have hx_eq : x = N *ᵥ y := by
    change N ^ m *ᵥ v = N *ᵥ (N ^ (m - 1) *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← pow_succ', Nat.sub_add_cancel hm1]
  have hMN : M = N + 1 := by rw [hNdef, sub_add_cancel]
  have hNx : N *ᵥ x = 0 := by
    change N *ᵥ (N ^ m *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, ← pow_succ', hm_spec, Matrix.zero_mulVec]
  have hMy : M *ᵥ y = x + y := by
    rw [hMN, Matrix.add_mulVec, Matrix.one_mulVec, ← hx_eq]
  have hAx : M *ᵥ x = x := by
    rw [hMN, Matrix.add_mulVec, hNx, Matrix.one_mulVec, zero_add]
  have hiso : x ⬝ᵥ x = 0 := by
    have hdot := dotProduct_mulVec_of_transpose_mul' hMorth x y
    rw [hAx] at hdot
    have hxdiff : M *ᵥ y - y = x := by rw [hMy, add_sub_cancel_right]
    rw [show x ⬝ᵥ x = x ⬝ᵥ (M *ᵥ y - y) by rw [hxdiff], dotProduct_sub, hdot, sub_self]
  exact ⟨x, hx_ne, hiso, hAx⟩

theorem exists_orthogonal_orderOf_eq_ringChar_fixing_isotropic [Finite K]
    (hK : ringChar K ≠ 2) :
    ∃ A : Matrix.GeneralLinearGroup (Fin 3) K,
      (A : Matrix (Fin 3) (Fin 3) K)ᵀ * A = 1 ∧ orderOf A = ringChar K ∧
        ∃ x : Fin 3 → K, x ≠ 0 ∧ x ⬝ᵥ x = 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) *ᵥ x = x := by
  classical
  haveI : Fact (ringChar K).Prime := ⟨CharP.prime_ringChar K⟩
  letI : Fintype K := Fintype.ofFinite K
  have hq : ringChar K ∣ Nat.card K := by
    have hchar : ringChar K ∣ Fintype.card K :=
      (prime_dvd_char_iff_dvd_card (R := K) (ringChar K)).1 dvd_rfl
    simpa only [Nat.card_eq_fintype_card] using hchar
  have hdvd : ringChar K ∣ Nat.card K * (Nat.card K ^ 2 - 1) :=
    dvd_mul_of_dvd_left hq _
  obtain ⟨A, hAorth, hAord⟩ :=
    exists_orthogonal_orderOf_eq (K := K) hK (CharP.prime_ringChar K) hdvd
  let M : Matrix (Fin 3) (Fin 3) K := A
  let N : Matrix (Fin 3) (Fin 3) K := M - 1
  have hMr : M ^ ringChar K = 1 := by
    have h1 : A ^ ringChar K = 1 := by rw [← hAord]; exact pow_orderOf_eq_one A
    have := congrArg (fun u : Matrix.GeneralLinearGroup (Fin 3) K =>
      (u : Matrix (Fin 3) (Fin 3) K)) h1
    simpa [M] using this
  have hAne : A ≠ 1 := by
    intro hA1
    rw [hA1, orderOf_one] at hAord
    exact (CharP.prime_ringChar K).ne_one hAord.symm
  have hNne : N ≠ 0 := by
    intro hN0
    have hM1 : (A : Matrix (Fin 3) (Fin 3) K) = 1 := by simpa [M] using sub_eq_zero.mp hN0
    exact hAne (Units.ext hM1)
  have hNpow : N ^ ringChar K = 0 := by
    change (M - 1) ^ ringChar K = 0
    rw [sub_pow_char_of_commute (p := ringChar K) (Commute.one_right M), hMr, one_pow,
      sub_self]
  have hNil : ∃ k, N ^ (k + 1) = 0 :=
    ⟨ringChar K - 1, by rw [Nat.sub_add_cancel (CharP.prime_ringChar K).one_le, hNpow]⟩
  exact ⟨A, hAorth, hAord,
    exists_isotropic_fixed_of_sub_nilpotent hAorth rfl hNne hNil⟩

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
