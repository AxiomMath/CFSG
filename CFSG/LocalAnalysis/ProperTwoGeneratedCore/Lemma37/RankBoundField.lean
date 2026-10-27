module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

theorem exists_mul_self_eq_card_of_ringEquiv {K : Type*} [Field K] [Fintype K] (σ : K ≃+* K)
    (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) :
    ∃ r : ℕ, r * r = Fintype.card K ∧ ∀ x, σ x = x ^ r := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  obtain ⟨-, hp, -⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  let _ : Algebra (ZMod p) K := ZMod.algebra K p
  have hcomm : ∀ x : ZMod p, σ (algebraMap (ZMod p) K x) = algebraMap (ZMod p) K x := fun x =>
    congrArg (fun g : ZMod p →+* K => g x)
      (RingHom.ext_zmod ((σ : K →+* K).comp (algebraMap (ZMod p) K)) (algebraMap (ZMod p) K))
  let σ' : K ≃ₐ[ZMod p] K := AlgEquiv.ofRingEquiv (f := σ) hcomm
  set Φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K with hΦ
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) K).2 σ'
  have hnf : (n : ℕ) < Module.finrank (ZMod p) K := n.2
  have hn' : Φ ^ (n : ℕ) = σ' := hn
  generalize (n : ℕ) = m at hnf hn'
  clear hn n
  have happly : ∀ x : K, σ x = x ^ p ^ m := by
    intro x
    have h1 := congrArg (fun τ : K ≃ₐ[ZMod p] K => τ x) hn'
    simp only [AlgEquiv.coe_pow, hΦ, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      ZMod.card] at h1
    exact h1.symm
  have hcard : Fintype.card K = p ^ Module.finrank (ZMod p) K := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := K)
    rwa [ZMod.card] at h
  have hord : orderOf Φ = Module.finrank (ZMod p) K :=
    FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) K
  have hσ'2 : σ' ^ 2 = 1 := by
    ext x
    have h := congrArg (fun τ : K ≃+* K => τ x) hσ2
    simpa [pow_two, σ'] using h
  have hdvd : Module.finrank (ZMod p) K ∣ 2 * m := by
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    rw [mul_comm, pow_mul, hn', hσ'2]
  have hn0 : m ≠ 0 := by
    intro h0
    apply hσ1
    ext x
    rw [happly, h0, pow_zero, pow_one]
    rfl
  have h2n : 2 * m = Module.finrank (ZMod p) K := by
    obtain ⟨k, hk⟩ := hdvd
    rcases k with _ | _ | k
    · omega
    · omega
    · nlinarith
  refine ⟨p ^ m, ?_, happly⟩
  rw [← pow_add, hcard, ← h2n, two_mul]

theorem ringEquiv_eq_of_involution {K : Type*} [Field K] [Fintype K] {σ τ : K ≃+* K}
    (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1) : σ = τ := by
  obtain ⟨r, hr, hσr⟩ := exists_mul_self_eq_card_of_ringEquiv σ hσ1 hσ2
  obtain ⟨s, hs, hτs⟩ := exists_mul_self_eq_card_of_ringEquiv τ hτ1 hτ2
  have hrs : r = s := Nat.mul_self_inj.mp (hr.trans hs.symm)
  ext x
  rw [hσr, hτs, hrs]

theorem pow_card_div_two_eq_one_of_mul_apply_eq_sq {K : Type*} [Field K] [Fintype K]
    (hK : ringChar K ≠ 2) (σ : K ≃+* K) (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) {d c : K}
    (hd : d ≠ 0) (hc : σ c = c) (h : d * σ d = c ^ 2) : d ^ (Fintype.card K / 2) = 1 := by
  obtain ⟨r, hr, hσr⟩ := exists_mul_self_eq_card_of_ringEquiv σ hσ1 hσ2
  have hodd : Fintype.card K % 2 = 1 := FiniteField.odd_card_of_char_ne_two hK
  obtain ⟨s, rfl⟩ : ∃ s, r = 2 * s + 1 := by
    rcases Nat.even_or_odd r with ⟨s, hs⟩ | ⟨s, hs⟩
    · exfalso
      rw [← hr, hs] at hodd
      have : (s + s) * (s + s) = 2 * (2 * (s * s)) := by ring
      omega
    · exact ⟨s, hs⟩
  have hdiv : Fintype.card K / 2 = (2 * s + 2) * s := by
    rw [← hr]
    have : (2 * s + 1) * (2 * s + 1) = 2 * ((2 * s + 2) * s) + 1 := by ring
    rw [this]
    omega
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, mul_eq_zero] at h
    rcases h with h | h
    · exact hd h
    · exact hd (σ.injective (h.trans (map_zero σ).symm))
  have hcr : c ^ (2 * s) = 1 := by
    have h1 : c ^ (2 * s) * c = c := by rw [← pow_succ, ← hσr]; exact hc
    exact (mul_eq_right₀ hc0).mp h1
  have hd2 : d ^ (2 * s + 2) = c ^ 2 := by
    rw [pow_succ, ← hσr, mul_comm, h]
  rw [hdiv, pow_mul, hd2, ← pow_mul, hcr]

theorem det_pow_card_div_two_eq_one_of_mul_map_mem_center {K : Type*} [Field K] [Fintype K]
    (hK : ringChar K ≠ 2) (σ : K ≃+* K) (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1)
    (X : GL (Fin 2) K)
    (hX : X * Matrix.GeneralLinearGroup.map σ.toRingHom X ∈ Subgroup.center (GL (Fin 2) K)) :
    ((Matrix.GeneralLinearGroup.det X : Kˣ) : K) ^ (Fintype.card K / 2) = 1 := by
  set Y := Matrix.GeneralLinearGroup.map σ.toRingHom X with hY
  have hσσ : ∀ x : K, σ (σ x) = x := fun x => by
    have h := congrArg (fun τ : K ≃+* K => τ x) hσ2
    simpa using h
  have hs := hX
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hX
  obtain ⟨c, hc⟩ := hX
  have hYY : Matrix.GeneralLinearGroup.map σ.toRingHom Y = X := by
    ext i j
    simp [hY, hσσ]
  have hYX : Y * X = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    rw [hc]
    calc Y * X = X⁻¹ * (X * Y) * X := by group
      _ = X⁻¹ * X * (X * Y) := by
        rw [mul_assoc, (Subgroup.mem_center_iff.mp hs X).symm, ← mul_assoc]
      _ = X * Y := by group
  have hmap : Y * X =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map σ.toRingHom.toMonoidHom c) := by
    have h := congrArg (Matrix.GeneralLinearGroup.map σ.toRingHom) hc
    rw [Matrix.GeneralLinearGroup.map_scalar, map_mul, hYY] at h
    exact h.symm
  have hcσ : σ (c : K) = c := by
    have h := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0)
      (hYX.symm.trans hmap)
    simpa using h.symm
  have hdet : ((Matrix.GeneralLinearGroup.det X : Kˣ) : K) *
      σ ((Matrix.GeneralLinearGroup.det X : Kˣ) : K) = (c : K) ^ 2 := by
    have h := congrArg (fun g : GL (Fin 2) K => ((Matrix.GeneralLinearGroup.det g : Kˣ) : K)) hc
    simp only [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_mul, Units.val_mul,
      Units.val_pow_eq_pow_val] at h
    rw [h]
    congr 1
    simp only [hY, Matrix.GeneralLinearGroup.val_det_apply]
    exact RingHom.map_det σ.toRingHom _
  exact pow_card_div_two_eq_one_of_mul_apply_eq_sq hK σ hσ1 hσ2 (Units.ne_zero _) hcσ hdet

end CFSG.ProperTwoGeneratedCore.Lemma37
