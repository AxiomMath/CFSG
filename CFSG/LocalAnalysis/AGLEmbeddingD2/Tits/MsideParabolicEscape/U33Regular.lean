module

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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33

open Matrix

variable {F : Type} [Field F]

theorem linearIndependent_orbit (ν : Matrix (Fin 3) (Fin 3) F) (hν3 : ν ^ 3 = 0)
    (w : Fin 3 → F) (hw : (ν ^ 2).mulVec w ≠ 0) :
    LinearIndependent F ![w, ν.mulVec w, (ν ^ 2).mulVec w] := by
  have h3 : ∀ v, (ν ^ 3).mulVec v = 0 := fun v => by rw [hν3]; simp
  have h2w : ν.mulVec ((ν ^ 2).mulVec w) = 0 := by
    rw [Matrix.mulVec_mulVec, ← pow_succ']
    exact h3 w
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • w + g 1 • ν.mulVec w + g 2 • (ν ^ 2).mulVec w = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hg
  have e1 : ν.mulVec (ν.mulVec w) = (ν ^ 2).mulVec w := by
    rw [Matrix.mulVec_mulVec, ← pow_two]
  have a2 : (ν ^ 2).mulVec (g 0 • w + g 1 • ν.mulVec w + g 2 • (ν ^ 2).mulVec w) = 0 := by
    rw [hg', Matrix.mulVec_zero]
  have hν2ν : (ν ^ 2).mulVec (ν.mulVec w) = 0 := by
    rw [Matrix.mulVec_mulVec, ← pow_succ]
    exact h3 w
  have hν2ν2 : (ν ^ 2).mulVec ((ν ^ 2).mulVec w) = 0 := by
    rw [Matrix.mulVec_mulVec, ← pow_add]
    have : ν ^ (2 + 2) = 0 := by
      rw [show 2 + 2 = 3 + 1 by norm_num, pow_succ, hν3, zero_mul]
    rw [this]
    simp
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hν2ν, hν2ν2, smul_zero, add_zero] at a2
  have g0 : g 0 = 0 := by
    by_contra h0
    exact hw (by simpa [h0] using a2)
  have a1 : ν.mulVec (g 0 • w + g 1 • ν.mulVec w + g 2 • (ν ^ 2).mulVec w) = 0 := by
    rw [hg', Matrix.mulVec_zero]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, h2w, smul_zero, add_zero, e1, g0, zero_smul,
    zero_add] at a1
  have g1 : g 1 = 0 := by
    by_contra h1
    exact hw (by simpa [h1] using a1)
  have a0 : g 2 • (ν ^ 2).mulVec w = 0 := by
    simpa [g0, g1] using hg'
  have g2 : g 2 = 0 := by
    by_contra h2
    exact hw (by simpa [h2] using a0)
  intro i
  fin_cases i <;> simp [g0, g1, g2]

theorem exists_vec_of_sq_ne_zero (ν : Matrix (Fin 3) (Fin 3) F) (h : ν ^ 2 ≠ 0) :
    ∃ w : Fin 3 → F, (ν ^ 2).mulVec w ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply h
  ext i j
  have := congrFun (hcon (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem exists_poly_of_commute (ν m : Matrix (Fin 3) (Fin 3) F) (hν3 : ν ^ 3 = 0)
    (hν2 : ν ^ 2 ≠ 0) (hm : m * ν = ν * m) :
    ∃ a b c : F, m = a • (1 : Matrix (Fin 3) (Fin 3) F) + b • ν + c • ν ^ 2 := by
  obtain ⟨w, hw⟩ := exists_vec_of_sq_ne_zero ν hν2
  have hli := linearIndependent_orbit ν hν3 w hw
  let bs : Module.Basis (Fin 3) F (Fin 3 → F) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hbs : ∀ i, bs i = ![w, ν.mulVec w, (ν ^ 2).mulVec w] i := fun i => by
    simp [bs]
  have hrepr := bs.sum_repr (m.mulVec w)
  rw [Fin.sum_univ_three, hbs, hbs, hbs] at hrepr
  set a := bs.repr (m.mulVec w) 0
  set b := bs.repr (m.mulVec w) 1
  set c := bs.repr (m.mulVec w) 2
  have hmw : m.mulVec w = a • w + b • ν.mulVec w + c • (ν ^ 2).mulVec w := by
    simpa using hrepr.symm
  refine ⟨a, b, c, ?_⟩
  set m' : Matrix (Fin 3) (Fin 3) F := a • (1 : Matrix (Fin 3) (Fin 3) F) + b • ν + c • ν ^ 2 with hm'
  have hm'ν : m' * ν = ν * m' := by
    rw [hm']
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, pow_two,
      mul_assoc]
  have hcm : ∀ v, m.mulVec (ν.mulVec v) = ν.mulVec (m.mulVec v) := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm]
  have hcm' : ∀ v, m'.mulVec (ν.mulVec v) = ν.mulVec (m'.mulVec v) := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm'ν]
  have hmw' : m'.mulVec w = a • w + b • ν.mulVec w + c • (ν ^ 2).mulVec w := by
    rw [hm']
    simp [Matrix.add_mulVec, Matrix.smul_mulVec]
  have hsq : ∀ v, (ν ^ 2).mulVec v = ν.mulVec (ν.mulVec v) := fun v => by
    rw [pow_two, ← Matrix.mulVec_mulVec]
  have heq : Matrix.toLin' m = Matrix.toLin' m' := by
    refine bs.ext fun i => ?_
    rw [hbs]
    simp only [Matrix.toLin'_apply]
    fin_cases i
    · simp [hmw, hmw']
    · show m.mulVec (ν.mulVec w) = m'.mulVec (ν.mulVec w)
      rw [hcm, hcm', hmw, hmw']
    · show m.mulVec ((ν ^ 2).mulVec w) = m'.mulVec ((ν ^ 2).mulVec w)
      rw [hsq, hcm, hcm, hcm', hcm', hmw, hmw']
  exact Matrix.toLin'.injective heq

theorem smul_combo_eq_zero (ν : Matrix (Fin 3) (Fin 3) F) (hν3 : ν ^ 3 = 0) (hν2 : ν ^ 2 ≠ 0)
    {p0 p1 p2 : F} (h : p0 • (1 : Matrix (Fin 3) (Fin 3) F) + p1 • ν + p2 • ν ^ 2 = 0) :
    p0 = 0 ∧ p1 = 0 ∧ p2 = 0 := by
  have f1 : ν * ν ^ 2 = 0 := by rw [← pow_succ']; exact hν3
  have f3 : ν ^ 2 * ν = 0 := by rw [← pow_succ]; exact hν3
  have f2 : ν ^ 2 * ν ^ 2 = 0 := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_succ, hν3, zero_mul]
  have f4 : ν * ν = ν ^ 2 := (pow_two ν).symm
  have e2 : (p0 • (1 : Matrix (Fin 3) (Fin 3) F) + p1 • ν + p2 • ν ^ 2) * ν ^ 2 =
      p0 • ν ^ 2 := by
    simp [add_mul, smul_mul_assoc, f1, f2]
  have hp0 : p0 = 0 := by
    rw [h, zero_mul] at e2
    by_contra hne
    exact hν2 ((smul_eq_zero.mp e2.symm).resolve_left hne)
  rw [hp0, zero_smul, zero_add] at h
  have e1 : (p1 • ν + p2 • ν ^ 2) * ν = p1 • ν ^ 2 := by
    simp [add_mul, smul_mul_assoc, f3, f4]
  have hp1 : p1 = 0 := by
    rw [h, zero_mul] at e1
    by_contra hne
    exact hν2 ((smul_eq_zero.mp e1.symm).resolve_left hne)
  rw [hp1, zero_smul, zero_add] at h
  have hp2 : p2 = 0 := by
    by_contra hne
    exact hν2 ((smul_eq_zero.mp h).resolve_left hne)
  exact ⟨hp0, hp1, hp2⟩

@[expose] def adj (σ : F →+* F) (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  (A.map σ)ᵀ

theorem adj_mul (σ : F →+* F) (A B : Matrix (Fin 3) (Fin 3) F) :
    adj σ (A * B) = adj σ B * adj σ A := by
  simp [adj, Matrix.map_mul, Matrix.transpose_mul]

theorem adj_add (σ : F →+* F) (A B : Matrix (Fin 3) (Fin 3) F) :
    adj σ (A + B) = adj σ A + adj σ B := by
  simp [adj, Matrix.map_add, Matrix.transpose_add]

theorem adj_smul (σ : F →+* F) (c : F) (A : Matrix (Fin 3) (Fin 3) F) :
    adj σ (c • A) = σ c • adj σ A := by
  ext i j
  simp [adj]

theorem adj_one (σ : F →+* F) : adj σ (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  simp [adj]

theorem adj_sub (σ : F →+* F) (A B : Matrix (Fin 3) (Fin 3) F) :
    adj σ (A - B) = adj σ A - adj σ B := by
  simp [adj, Matrix.map_sub, Matrix.transpose_sub]

theorem poly_mul (ν : Matrix (Fin 3) (Fin 3) F) (hν3 : ν ^ 3 = 0) (α0 α1 α2 a b c : F) :
    (α0 • (1 : Matrix (Fin 3) (Fin 3) F) + α1 • ν + α2 • ν ^ 2) *
        (a • (1 : Matrix (Fin 3) (Fin 3) F) + b • ν + c • ν ^ 2) =
      (α0 * a) • (1 : Matrix (Fin 3) (Fin 3) F) + (α0 * b + α1 * a) • ν +
        (α0 * c + α1 * b + α2 * a) • ν ^ 2 := by
  have f1 : ν * ν ^ 2 = 0 := by rw [← pow_succ']; exact hν3
  have f3 : ν ^ 2 * ν = 0 := by rw [← pow_succ]; exact hν3
  have f2 : ν ^ 2 * ν ^ 2 = 0 := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_succ, hν3, zero_mul]
  have f4 : ν * ν = ν ^ 2 := (pow_two ν).symm
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, f4, f1, f3, f2,
    smul_zero, add_zero, smul_smul]
  module

theorem unitary_poly_relations (σ : F →+* F) (y : Matrix (Fin 3) (Fin 3) F)
    (hy : adj σ y * y = 1) (hν3 : (y - 1) ^ 3 = 0) (hν2 : (y - 1) ^ 2 ≠ 0) (a b c : F)
    (hmu : adj σ (a • (1 : Matrix (Fin 3) (Fin 3) F) + b • (y - 1) + c • (y - 1) ^ 2) *
      (a • (1 : Matrix (Fin 3) (Fin 3) F) + b • (y - 1) + c • (y - 1) ^ 2) = 1) :
    σ a * a = 1 ∧ σ a * b = σ b * a ∧ σ a * c - σ b * b + (σ b + σ c) * a = 0 := by
  set ν : Matrix (Fin 3) (Fin 3) F := y - 1 with hν
  have hyν : y = 1 + ν := by rw [hν]; abel
  have hZ : y * (1 - ν + ν ^ 2) = 1 := by
    rw [hyν]
    have : (1 + ν) * (1 - ν + ν ^ 2) = 1 + ν ^ 3 := by noncomm_ring
    rw [this, hν3, add_zero]
  have hadjy : adj σ y = 1 - ν + ν ^ 2 := by
    calc adj σ y = adj σ y * (y * (1 - ν + ν ^ 2)) := by rw [hZ, mul_one]
      _ = (adj σ y * y) * (1 - ν + ν ^ 2) := by rw [mul_assoc]
      _ = 1 - ν + ν ^ 2 := by rw [hy, one_mul]
  have hadjν : adj σ ν = -ν + ν ^ 2 := by
    have : adj σ ν = adj σ y - 1 := by
      rw [hν, adj_sub, adj_one]
    rw [this, hadjy]
    abel
  have f1 : ν * ν ^ 2 = 0 := by rw [← pow_succ']; exact hν3
  have f3 : ν ^ 2 * ν = 0 := by rw [← pow_succ]; exact hν3
  have f2 : ν ^ 2 * ν ^ 2 = 0 := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_succ, hν3, zero_mul]
  have hadjν2 : adj σ (ν ^ 2) = ν ^ 2 := by
    rw [pow_two, adj_mul, hadjν]
    have : (-ν + ν ^ 2) * (-ν + ν ^ 2) = ν * ν - ν * ν ^ 2 - ν ^ 2 * ν + ν ^ 2 * ν ^ 2 := by
      noncomm_ring
    rw [this, f1, f3, f2, ← pow_two]
    abel
  have hadjm : adj σ (a • (1 : Matrix (Fin 3) (Fin 3) F) + b • ν + c • ν ^ 2) =
      σ a • (1 : Matrix (Fin 3) (Fin 3) F) + (-σ b) • ν + (σ b + σ c) • ν ^ 2 := by
    rw [adj_add, adj_add, adj_smul, adj_smul, adj_smul, adj_one, hadjν, hadjν2]
    module
  rw [hadjm, poly_mul ν hν3] at hmu
  have hcomb : (σ a * a - 1) • (1 : Matrix (Fin 3) (Fin 3) F) +
      (σ a * b + (-σ b) * a) • ν +
      (σ a * c + (-σ b) * b + (σ b + σ c) * a) • ν ^ 2 = 0 := by
    have : (σ a * a) • (1 : Matrix (Fin 3) (Fin 3) F) + (σ a * b + (-σ b) * a) • ν +
      (σ a * c + (-σ b) * b + (σ b + σ c) * a) • ν ^ 2 - 1 = 0 := sub_eq_zero.mpr hmu
    rw [← this]
    module
  obtain ⟨h0, h1, h2⟩ := smul_combo_eq_zero ν hν3 hν2 hcomb
  refine ⟨by linear_combination h0, by linear_combination h1, by linear_combination h2⟩

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33
