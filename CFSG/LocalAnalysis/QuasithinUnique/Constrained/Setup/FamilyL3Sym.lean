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
public import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
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

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix Module


section Isotropic

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem exists_isotropic {p : ℕ} [hp : Fact p.Prime] [CharP K p] (M : Matrix (Fin 3) (Fin 3) K) :
    ∃ e : Fin 3 → K, e ≠ 0 ∧ e ⬝ᵥ (M *ᵥ e) = 0 := by
  let F : MvPolynomial (Fin 3) K :=
    ∑ i, ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X i * MvPolynomial.X j
  have hdeg : F.totalDegree ≤ 2 := by
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    calc (MvPolynomial.C (M i j) * MvPolynomial.X i * MvPolynomial.X j).totalDegree
        ≤ (MvPolynomial.C (M i j) * MvPolynomial.X i).totalDegree +
            (MvPolynomial.X j : MvPolynomial (Fin 3) K).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ ((MvPolynomial.C (M i j) : MvPolynomial (Fin 3) K).totalDegree +
            (MvPolynomial.X i : MvPolynomial (Fin 3) K).totalDegree) +
            (MvPolynomial.X j : MvPolynomial (Fin 3) K).totalDegree :=
          Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
      _ ≤ 2 := by simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  have hdvd := char_dvd_card_solutions p
    (show F.totalDegree < Fintype.card (Fin 3) by rw [Fintype.card_fin]; omega)
  have heval : ∀ x : Fin 3 → K, MvPolynomial.eval x F = x ⬝ᵥ (M *ᵥ x) := by
    intro x
    simp only [F, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, dotProduct,
      mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  by_contra hcon
  push Not at hcon
  have hcard : ∀ [inst : Fintype {x : Fin 3 → K // MvPolynomial.eval x F = 0}],
      Fintype.card {x : Fin 3 → K // MvPolynomial.eval x F = 0} = 1 := by
    intro inst
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, by rw [heval]; simp⟩, fun ⟨x, hx⟩ => Subtype.ext ?_⟩
    by_contra hne
    exact hcon x hne (by rw [← heval]; exact hx)
  rw [@hcard _] at hdvd
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 hdvd)

end Isotropic

section Orth

variable {K : Type} [Field K]

theorem dotProduct_mulVec_symm {M : Matrix (Fin 3) (Fin 3) K} (hMs : Mᵀ = M)
    (x y : Fin 3 → K) : x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← hMs, Matrix.vecMul_transpose, hMs, dotProduct_comm]

theorem exists_orth_anisotropic (h2 : (2 : K) ≠ 0) {M : Matrix (Fin 3) (Fin 3) K}
    (hM : M.det ≠ 0) (hMs : Mᵀ = M) {e : Fin 3 → K} (he : e ≠ 0) :
    ∃ g : Fin 3 → K, e ⬝ᵥ (M *ᵥ g) = 0 ∧ g ⬝ᵥ (M *ᵥ g) ≠ 0 := by
  let B := Matrix.toBilin' M
  have hB : B.Nondegenerate :=
    Matrix.nondegenerate_toBilin'_iff.2 (Matrix.nondegenerate_of_det_ne_zero hM)
  have hBapply : ∀ x y, B x y = x ⬝ᵥ (M *ᵥ y) := fun x y => Matrix.toBilin'_apply' M x y
  let W : Submodule K (Fin 3 → K) := Submodule.span K {e}
  have hW : finrank K W = 1 := finrank_span_singleton he
  let O := B.orthogonal W
  have hO : finrank K O = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB, hW]; simp
  have hmemO : ∀ x, x ∈ O ↔ e ⬝ᵥ (M *ᵥ x) = 0 := by
    intro x
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      have := h e (Submodule.mem_span_singleton_self e)
      simpa [hBapply] using this
    · intro h y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      simp [hBapply, h]
  by_contra hcon
  push Not at hcon
  have hOO : O ≤ B.orthogonal O := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    have hxy : (x + y) ∈ O := O.add_mem hx hy
    have q1 := hcon x ((hmemO x).1 hx)
    have q2 := hcon y ((hmemO y).1 hy)
    have q3 := hcon (x + y) ((hmemO _).1 hxy)
    have hs := dotProduct_mulVec_symm hMs x y
    simp only [hBapply]
    have : (2 : K) * (y ⬝ᵥ (M *ᵥ x)) = 0 := by
      have e1 : (x + y) ⬝ᵥ (M *ᵥ (x + y)) =
          x ⬝ᵥ (M *ᵥ x) + y ⬝ᵥ (M *ᵥ y) + x ⬝ᵥ (M *ᵥ y) + y ⬝ᵥ (M *ᵥ x) := by
        simp [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
        ring
      rw [e1, q1, q2, hs] at q3
      linear_combination q3
    exact (mul_eq_zero.1 this).resolve_left h2
  have h1 := Submodule.finrank_mono hOO
  have h3 : finrank K (B.orthogonal O) = finrank K (Fin 3 → K) - finrank K O :=
    LinearMap.BilinForm.finrank_orthogonal hB O
  rw [h3, hO] at h1
  simp at h1

end Orth
section Nil

variable {K : Type} [Field K]

theorem exists_regular_nilpotent (h2 : (2 : K) ≠ 0) {M : Matrix (Fin 3) (Fin 3) K}
    (hM : M.det ≠ 0) (hMs : Mᵀ = M) {e : Fin 3 → K} (he : e ≠ 0) (hiso : e ⬝ᵥ (M *ᵥ e) = 0) :
    ∃ N : Matrix (Fin 3) (Fin 3) K, N * N * N = 0 ∧ N * N ≠ 0 ∧ Nᵀ * M = M * N := by
  obtain ⟨g, hg1, hg2⟩ := exists_orth_anisotropic h2 hM hMs he
  have hge : g ⬝ᵥ (M *ᵥ e) = 0 := by rw [dotProduct_mulVec_symm hMs, hg1]
  set c : K := g ⬝ᵥ (M *ᵥ g) with hc
  set S : Matrix (Fin 3) (Fin 3) K := vecMulVec g e + vecMulVec e g with hS
  have hMS : M * S = vecMulVec (M *ᵥ g) e + vecMulVec (M *ᵥ e) g := by
    rw [hS, Matrix.mul_add, mul_vecMulVec, mul_vecMulVec]
  have hSMS : S * M * S = c • vecMulVec e e := by
    rw [Matrix.mul_assoc, hMS, hS]
    simp only [Matrix.add_mul, Matrix.mul_add, vecMulVec_mul_vecMulVec, hg1, hiso, hge, zero_smul,
      vecMulVec_zero, zero_add, add_zero, vecMulVec_smul]
    rfl
  have hNN : S * M * (S * M) = c • vecMulVec e (e ᵥ* M) := by
    rw [← Matrix.mul_assoc, hSMS, Matrix.smul_mul, vecMulVec_mul]
  have hvec : (e ᵥ* M) ᵥ* (S * M) = 0 := by
    rw [← Matrix.vecMul_vecMul]
    have : (e ᵥ* M) ᵥ* S = 0 := by
      rw [hS, Matrix.vecMul_add, vecMul_vecMulVec, vecMul_vecMulVec,
        ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, hg1, hiso]
      simp
    rw [this, Matrix.zero_vecMul]
  have hneM : e ᵥ* M ≠ 0 := by
    intro h0
    apply he
    have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hM)
    calc e = e ᵥ* (M * M⁻¹) := by rw [h1, Matrix.vecMul_one]
      _ = (e ᵥ* M) ᵥ* M⁻¹ := (Matrix.vecMul_vecMul e M M⁻¹).symm
      _ = 0 := by rw [h0, Matrix.zero_vecMul]
  refine ⟨S * M, ?_, ?_, ?_⟩
  · rw [hNN, Matrix.smul_mul, vecMulVec_mul, hvec, vecMulVec_zero, smul_zero]
  · rw [hNN]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 he
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hneM
    intro h0
    have := congrFun (congrFun h0 i) j
    simp only [Matrix.smul_apply, vecMulVec_apply, Matrix.zero_apply, smul_eq_mul] at this
    exact mul_ne_zero hg2 (mul_ne_zero hi hj) this
  · have hSt : Sᵀ = S := by
      rw [hS, Matrix.transpose_add, transpose_vecMulVec, transpose_vecMulVec, add_comm]
    rw [Matrix.transpose_mul, hMs, hSt, Matrix.mul_assoc]

end Nil


section VGroup

variable {K : Type} [Field K] [Fintype K]

@[expose] def vMat (N : Matrix (Fin 3) (Fin 3) K) (a : K × K) : Matrix (Fin 3) (Fin 3) K :=
  1 + a.1 • N + (a.2 + a.1 ^ 2 / 2) • (N * N)

omit [Fintype K] in
theorem vMat_zero (N : Matrix (Fin 3) (Fin 3) K) : vMat N 0 = 1 := by
  simp [vMat]

omit [Fintype K] in
theorem vMat_add (h2 : (2 : K) ≠ 0) {N : Matrix (Fin 3) (Fin 3) K} (hN : N * N * N = 0)
    (a b : K × K) : vMat N (a + b) = vMat N a * vMat N b := by
  have h1 : N * (N * N) = 0 := by rw [← Matrix.mul_assoc]; exact hN
  have h3 : N * N * (N * N) = 0 := by rw [Matrix.mul_assoc, h1, Matrix.mul_zero]
  unfold vMat
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, h1, hN, h3, smul_zero, add_zero, Prod.fst_add, Prod.snd_add]
  have e1 : (a.2 + b.2 + (a.1 + b.1) ^ 2 / 2) =
      (b.2 + b.1 ^ 2 / 2) + (a.2 + a.1 ^ 2 / 2) + a.1 * b.1 := by
    field_simp
    ring
  rw [e1]
  module

theorem det_vMat (h2 : (2 : K) ≠ 0) {N : Matrix (Fin 3) (Fin 3) K} (hN : N * N * N = 0)
    (a : K × K) : (vMat N a).det = 1 := by
  have hadd : ∀ a b, (vMat N (a + b)).det = (vMat N a).det * (vMat N b).det := fun a b => by
    rw [vMat_add h2 hN, Matrix.det_mul]
  have hzero : (vMat N 0).det = 1 := by rw [vMat_zero, Matrix.det_one]
  have hne : (vMat N a).det ≠ 0 := by
    intro h0
    have := hadd a (-a)
    rw [add_neg_cancel, hzero, h0, zero_mul] at this
    exact one_ne_zero this
  have hpow : ∀ n : ℕ, (vMat N (n • a)).det = (vMat N a).det ^ n := by
    intro n
    induction n with
    | zero => simp [hzero]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hq : Fintype.card K • a = 0 := by
    obtain ⟨x, y⟩ := a
    simp [Prod.smul_mk]
  have h1 : (vMat N a).det ^ Fintype.card K = 1 := by
    rw [← hpow, hq, hzero]
  have h2' : (vMat N a).det ^ (Fintype.card K - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ hne
  have hq1 : 1 ≤ Fintype.card K := Fintype.card_pos
  calc (vMat N a).det = (vMat N a).det * (vMat N a).det ^ (Fintype.card K - 1) := by
        rw [h2', mul_one]
    _ = (vMat N a).det ^ Fintype.card K := by
        rw [← pow_succ']; congr 1; omega
    _ = 1 := h1

end VGroup

section Inverted

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem exists_inverted_vgroup {p : ℕ} [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0)
    (A : GL (Fin 3) K) (hA : (A : Matrix (Fin 3) (Fin 3) K)ᵀ = A) :
    ∃ v : K × K → SpecialLinearGroup (Fin 3) K,
      v 0 = 1 ∧ (∀ a b, v (a + b) = v a * v b) ∧
      (∀ a, (A : Matrix (Fin 3) (Fin 3) K) *
          (((v a)⁻¹).transpose : SpecialLinearGroup (Fin 3) K) *
          ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((v a)⁻¹ : SpecialLinearGroup (Fin 3) K)) ∧
      (∀ a, v a ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) → a = 0) := by
  set M : Matrix (Fin 3) (Fin 3) K := ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  set Am : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hAm
  have hAM : Am * M = 1 := by rw [hM, hAm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMA : M * Am = 1 := by rw [hM, hAm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hMs : Mᵀ = M := by
    have h1 : Mᵀ * Am = 1 := by
      have := congrArg Matrix.transpose hAM
      rw [Matrix.transpose_mul, hA, Matrix.transpose_one] at this
      exact this
    calc Mᵀ = Mᵀ * (Am * M) := by rw [hAM, Matrix.mul_one]
      _ = (Mᵀ * Am) * M := by rw [Matrix.mul_assoc]
      _ = M := by rw [h1, Matrix.one_mul]
  have hdetM : M.det ≠ 0 := by
    have := congrArg Matrix.det hAM
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h0
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  obtain ⟨e, he, hiso⟩ := exists_isotropic (p := p) M
  obtain ⟨N, hN3, hN2, hNs⟩ := exists_regular_nilpotent h2 hdetM hMs he hiso
  have hAN : Am * Nᵀ * M = N := by
    rw [Matrix.mul_assoc, hNs, ← Matrix.mul_assoc, hAM, Matrix.one_mul]
  have hconj : ∀ X Y : Matrix (Fin 3) (Fin 3) K,
      Am * (X * Y) * M = (Am * X * M) * (Am * Y * M) := by
    intro X Y
    calc Am * (X * Y) * M = Am * X * 1 * Y * M := by simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Am * X * (M * Am) * Y * M := by rw [hMA]
      _ = (Am * X * M) * (Am * Y * M) := by simp only [Matrix.mul_assoc]
  let v : K × K → SpecialLinearGroup (Fin 3) K := fun a => ⟨vMat N a, det_vMat h2 hN3 a⟩
  have hv : ∀ a, ((v a : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = vMat N a :=
    fun a => rfl
  have hv0 : v 0 = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hv, vMat_zero]; rfl
  have hvadd : ∀ a b, v (a + b) = v a * v b := by
    intro a b
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hv, Matrix.SpecialLinearGroup.coe_mul, hv, hv, vMat_add h2 hN3]
  refine ⟨v, hv0, hvadd, fun a => ?_, fun a ha => ?_⟩
  · have hinv : (v a)⁻¹ = v (-a) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← hvadd, add_neg_cancel, hv0]
    rw [hinv, Matrix.SpecialLinearGroup.coe_transpose, hv]
    have hA1 : Am * (1 : Matrix (Fin 3) (Fin 3) K) * M = 1 := by rw [Matrix.mul_one, hAM]
    have hA2 : ∀ b : K, Am * (b • Nᵀ) * M = b • N := by
      intro b; rw [Matrix.mul_smul, Matrix.smul_mul, hAN]
    have hA3 : ∀ b : K, Am * (b • (Nᵀ * Nᵀ)) * M = b • (N * N) := by
      intro b; rw [Matrix.mul_smul, Matrix.smul_mul, hconj, hAN]
    unfold vMat
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.transpose_mul]
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, hA1, hA2, hA3]
  · obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 ha
    rw [hv] at hr
    set x := a.1 with hx
    set c := a.2 + a.1 ^ 2 / 2 with hc
    have hN1 : N * (N * N) = 0 := by rw [← Matrix.mul_assoc]; exact hN3
    have hscal : Matrix.scalar (Fin 3) r = r • (1 : Matrix (Fin 3) (Fin 3) K) := by
      ext i j
      simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
    have hT : (r - 1) • (1 : Matrix (Fin 3) (Fin 3) K) = x • N + c • (N * N) := by
      have := hr
      rw [hscal] at this
      unfold vMat at this
      calc (r - 1) • (1 : Matrix (Fin 3) (Fin 3) K) = r • 1 - 1 := by rw [sub_smul, one_smul]
        _ = x • N + c • (N * N) := by
          rw [this]; abel
    have hr1 : r = 1 := by
      have h1 : ((r - 1) • (1 : Matrix (Fin 3) (Fin 3) K)) * (N * N) = 0 := by
        rw [hT]
        simp only [Matrix.add_mul, Matrix.smul_mul]
        rw [show N * (N * N) = 0 from hN1, show N * N * (N * N) = 0 by
          rw [Matrix.mul_assoc, hN1, Matrix.mul_zero]]
        simp
      rw [Matrix.smul_mul, Matrix.one_mul] at h1
      rcases smul_eq_zero.1 h1 with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h hN2
    have hT0 : x • N + c • (N * N) = 0 := by
      rw [← hT, hr1, sub_self, zero_smul]
    have hx0 : x = 0 := by
      have h1 : (x • N + c • (N * N)) * N = 0 := by rw [hT0, Matrix.zero_mul]
      rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hN3, smul_zero, add_zero] at h1
      rcases smul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hN2
    have hc0 : c = 0 := by
      rw [hx0, zero_smul, zero_add] at hT0
      rcases smul_eq_zero.1 hT0 with h | h
      · exact h
      · exact absurd h hN2
    refine Prod.ext hx0 ?_
    have : a.2 = c - a.1 ^ 2 / 2 := by rw [hc]; ring
    rw [this, hc0, ← hx, hx0]
    simp

end Inverted

end CFSG.QuasithinUnique.Setup.Family
