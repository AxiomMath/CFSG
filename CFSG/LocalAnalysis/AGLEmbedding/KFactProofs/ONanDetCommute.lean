module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Action.Concrete
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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.AGLEmbedding

open Matrix

variable {F : Type*} [Field F] [Fintype F] {n : ℕ}

theorem exists_fixed_vector_of_not_modEq {p : ℕ} [Fact p.Prime]
    (P : Subgroup (GL (Fin n) F)) (hP : IsPGroup p P)
    (hn : ¬ Fintype.card F ^ n ≡ 1 [MOD p]) :
    ∃ v : Fin n → F, v ≠ 0 ∧ ∀ a ∈ P, ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v = v := by
  classical
  let V := Matrix (Fin n) (Fin 1) F
  have hcard : Nat.card V = Fintype.card F ^ n := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card (Fin n → Fin 1 → F) = _
    rw [Fintype.card_fun, Fintype.card_fun]
    simp
  have hmod := hP.card_modEq_card_fixedPoints V
  by_contra hcon
  push Not at hcon
  have hfix : MulAction.fixedPoints P V = {0} := by
    ext x
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hx0
      have hv : (fun i => x i 0) ≠ 0 := by
        intro h0
        apply hx0
        ext i j
        have : j = 0 := Subsingleton.elim _ _
        subst this
        exact congrFun h0 i
      obtain ⟨a, ha, hav⟩ := hcon _ hv
      apply hav
      have h1 := hx ⟨a, ha⟩
      funext i
      have h2 := congrFun (congrFun h1 i) 0
      change (((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * x) i 0 = x i 0 at h2
      rw [Matrix.mul_apply] at h2
      rw [Matrix.mulVec, dotProduct]
      exact h2
    · rintro rfl a
      exact smul_zero _
  have h1 : Nat.card ↥({0} : Set V) = 1 := by simp
  rw [hfix, h1, hcard] at hmod
  exact hn hmod

theorem exists_commute_det_eq {p : ℕ} [Fact p.Prime] (hpF : (p : F) ≠ 0)
    (P : Subgroup (GL (Fin n) F)) (hP : IsPGroup p P)
    (hn : ¬ Fintype.card F ^ n ≡ 1 [MOD p]) (μ : Fˣ) :
    ∃ c : GL (Fin n) F, (∀ a ∈ P, c * a = a * c) ∧ GeneralLinearGroup.det c = μ := by
  obtain ⟨v, hv0, hv⟩ := exists_fixed_vector_of_not_modEq P hP hn
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  let ψ : Fin n → F := Pi.single i (v i)⁻¹
  have hψ : ψ ⬝ᵥ v = 1 := by
    simp [ψ, hi]
  have : Fintype P := Fintype.ofFinite P
  have hNF : (Fintype.card P : F) ≠ 0 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := P)).1 hP
    rw [← Nat.card_eq_fintype_card, hk, Nat.cast_pow]
    exact pow_ne_zero _ hpF
  let w : Fin n → F :=
    (Fintype.card P : F)⁻¹ • ∑ a : P, ψ ᵥ* ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hw1 : w ⬝ᵥ v = 1 := by
    have h1 : ∀ a : P, (ψ ᵥ* ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) ⬝ᵥ v = 1 :=
      fun a => by rw [← dotProduct_mulVec, hv a a.2, hψ]
    simp only [w, smul_dotProduct, sum_dotProduct, h1, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, smul_eq_mul]
    exact inv_mul_cancel₀ hNF
  have hwP : ∀ b ∈ P, w ᵥ* ((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = w := by
    intro b hb
    simp only [w, smul_vecMul, sum_vecMul, vecMul_vecMul]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulRight (⟨b, hb⟩ : P)) _ _ (fun a => ?_)
    simp
  let u : Fin n → F := ((μ : F) - 1) • v
  let M : Matrix (Fin n) (Fin n) F := 1 + replicateCol (Fin 1) u * replicateRow (Fin 1) w
  have hdet : M.det = μ := by
    have h0 : M.det = 1 + w ⬝ᵥ u := det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) u w
    rw [h0]
    simp only [u]
    rw [dotProduct_smul, hw1, smul_eq_mul, mul_one]
    ring
  have hMu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact μ.isUnit
  refine ⟨hMu.unit, fun a ha => ?_, ?_⟩
  · apply Units.ext
    change M * ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * M
    simp only [M, add_mul, mul_add, one_mul, mul_one, Matrix.mul_assoc]
    rw [← replicateRow_vecMul, hwP a ha, ← Matrix.mul_assoc, ← replicateCol_mulVec]
    simp only [u, mulVec_smul, hv a ha]
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, IsUnit.unit_spec, hdet]

end CFSG.AGLEmbedding
