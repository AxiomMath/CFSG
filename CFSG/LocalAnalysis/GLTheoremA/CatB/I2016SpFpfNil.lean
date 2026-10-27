module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016Sp

open Polynomial

private theorem fpfSqEqZeroOfIsNilpotent {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (hdim : Module.finrank L V ≤ 2) (N : Module.End L V)
    (hN : IsNilpotent N) : N ^ 2 = 0 := by
  obtain ⟨n, hn⟩ := hN
  have h : N ^ Module.finrank L V = 0 := by
    have := Module.End.ker_pow_le_ker_pow_finrank N n
    rw [hn, LinearMap.ker_zero] at this
    exact LinearMap.ker_eq_top.mp (top_unique this)
  rw [show 2 = (2 - Module.finrank L V) + Module.finrank L V by omega, pow_add, h, mul_zero]

private theorem fpfCommuteAevalRight {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {a b : A} (h : Commute a b) (p : R[X]) : Commute a (aeval b p) := by
  refine Polynomial.induction_on p (fun c => ?_) (fun p q hp hq => ?_) (fun n c _ => ?_)
  · rw [aeval_C]
    exact (show Commute a (algebraMap R A c) from (Algebra.commutes c a).symm)
  · rw [map_add]
    exact hp.add_right hq
  · rw [map_mul, map_pow, aeval_C, aeval_X]
    exact (show Commute a (algebraMap R A c) from (Algebra.commutes c a).symm).mul_right
      (h.pow_right (n + 1))

theorem sq_eq_zero_of_commute_nilpotent {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hirr : ∀ a : K, a ^ 2 + a + 1 ≠ 0) (g : Module.End K V)
    (hg : g ^ 2 + g + 1 = 0) (hdim : Module.finrank K V ≤ 4) (N : Module.End K V)
    (hNg : Commute N g) (hN : IsNilpotent N) : N ^ 2 = 0 := by
  set f : K[X] := X ^ 2 + X + 1 with hf
  have hfdeg : f.natDegree = 2 := by
    rw [hf]
    compute_degree!
  have hfirr : Irreducible f := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hfdeg]; decide)
      fun a ha => hirr a ?_
    simpa [hf, IsRoot] using ha
  haveI : Fact (Irreducible f) := ⟨hfirr⟩
  have hgf : aeval g f = 0 := by
    rw [hf, map_add, map_add, map_pow, aeval_X, map_one]
    exact hg
  let ψ : AdjoinRoot f →+* Module.End K V :=
    Ideal.Quotient.lift (Ideal.span {f}) (aeval g : K[X] →ₐ[K] Module.End K V).toRingHom
      fun a ha => by
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp ha
        show aeval g (f * q) = 0
        rw [map_mul, hgf, zero_mul]
  have hψ : ∀ p : K[X], ψ (AdjoinRoot.mk f p) = aeval g p := fun _ => rfl
  letI : Module (AdjoinRoot f) V := Module.compHom V ψ
  have hsmul : ∀ (l : AdjoinRoot f) (v : V), l • v = ψ l v := fun _ _ => rfl
  haveI : IsScalarTower K (AdjoinRoot f) V := ⟨fun c l v => by
    rw [hsmul, hsmul, Algebra.smul_def, map_mul, Module.End.mul_apply, AdjoinRoot.algebraMap_eq,
      ← AdjoinRoot.mk_C, hψ, aeval_C, Module.algebraMap_end_apply]⟩
  have hL : Module.finrank K (AdjoinRoot f) = 2 := by
    rw [(AdjoinRoot.powerBasis hfirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hfdeg]
  haveI : Module.Finite (AdjoinRoot f) V :=
    Module.Finite.of_restrictScalars_finite K (AdjoinRoot f) V
  have htower := Module.finrank_mul_finrank K (AdjoinRoot f) V
  rw [hL] at htower
  have hdimL : Module.finrank (AdjoinRoot f) V ≤ 2 := by omega
  have hcomm : ∀ (l : AdjoinRoot f) (v : V), N (ψ l v) = ψ l (N v) := by
    intro l v
    induction l using AdjoinRoot.induction_on with
    | ih p =>
      rw [hψ]
      exact congrArg (fun φ : Module.End K V => φ v) (fpfCommuteAevalRight hNg p).eq
  let NL : V →ₗ[AdjoinRoot f] V :=
    { toFun := N
      map_add' := N.map_add
      map_smul' := fun l v => by
        rw [hsmul, hsmul]
        exact hcomm l v }
  have hpow : ∀ (k : ℕ) (v : V), (NL ^ k) v = (N ^ k) v := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl
  have hNL : IsNilpotent NL := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, LinearMap.ext fun v => by rw [hpow, hk]; rfl⟩
  have hsq := fpfSqEqZeroOfIsNilpotent hdimL NL hNL
  exact LinearMap.ext fun v => by rw [← hpow, hsq]; rfl

end CFSG.LocalAnalysis.GLTheoremA.I2016Sp

end
