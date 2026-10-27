module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7

open Polynomial

@[expose] noncomputable def quad (K : Type) [Field K] : K[X] := X ^ 2 + X + 1

theorem aeval_quad {K A : Type} [Field K] [CommRing A] [Algebra K A] (x : A) :
    Polynomial.aeval x (quad K) = x ^ 2 + x + 1 := by
  unfold quad
  simp

theorem eval₂_quad {K R : Type} [Field K] [CommRing R] (f : K →+* R) (x : R) :
    (quad K).eval₂ f x = x ^ 2 + x + 1 := by
  unfold quad
  simp

theorem quad_natDegree (K : Type) [Field K] : (quad K).natDegree = 2 := by
  unfold quad
  compute_degree!

theorem quad_irreducible {K : Type} [Field K] (hnr : ∀ x : K, x ^ 2 + x + 1 ≠ 0) :
    Irreducible (quad K) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [quad_natDegree]
    norm_num
  · intro x hx
    apply hnr x
    simpa [quad, Polynomial.IsRoot] using hx

section Quad

variable (K : Type) [Field K] [Fact (Irreducible (quad K))]

noncomputable abbrev zetaQ : AdjoinRoot (quad K) := AdjoinRoot.root (quad K)

theorem zetaQ_quad : zetaQ K ^ 2 + zetaQ K + 1 = 0 := by
  have h2 : Polynomial.aeval (zetaQ K) (quad K) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [aeval_quad] at h2
  exact h2

theorem zetaQ_cube : zetaQ K ^ 3 = 1 := by
  have h := zetaQ_quad K
  linear_combination (zetaQ K - 1) * h

end Quad

theorem three_ne_zero_quad {K : Type} [Field K] (hnr : ∀ x : K, x ^ 2 + x + 1 ≠ 0)
    [Fact (Irreducible (quad K))] : (3 : AdjoinRoot (quad K)) ≠ 0 := by
  intro h3
  apply hnr 1
  have h3K : (3 : K) = 0 := by
    apply (algebraMap K (AdjoinRoot (quad K))).injective
    rw [map_zero, map_ofNat]
    exact h3
  norm_num
  linear_combination h3K

theorem prim_root_quad {K : Type} [Field K] (hnr : ∀ x : K, x ^ 2 + x + 1 ≠ 0)
    [Fact (Irreducible (quad K))] : IsPrimitiveRoot (zetaQ K) 3 := by
  apply IsPrimitiveRoot.mk_of_lt (zetaQ K) (by norm_num) (zetaQ_cube K)
  intro l hl0 hl3
  interval_cases l
  ·
    intro h1
    have h := zetaQ_quad K
    rw [pow_one] at h1
    rw [h1] at h
    apply three_ne_zero_quad hnr
    linear_combination h
  ·
    intro h1
    have h := zetaQ_quad K
    apply three_ne_zero_quad hnr
    linear_combination h1 - (zetaQ K - 2) * (h - h1)

@[expose] noncomputable def sigmaQuad (K : Type) [Field K] [Fact (Irreducible (quad K))] :
    AdjoinRoot (quad K) →ₐ[K] AdjoinRoot (quad K) :=
  AdjoinRoot.liftAlgHom (quad K) (Algebra.ofId K (AdjoinRoot (quad K))) (zetaQ K ^ 2) (by
    have hz := zetaQ_cube K
    have hq := zetaQ_quad K
    rw [eval₂_quad]
    linear_combination (zetaQ K) * hz + hq)

theorem sigmaQuad_zeta (K : Type) [Field K] [Fact (Irreducible (quad K))] :
    sigmaQuad K (zetaQ K) = zetaQ K ^ 2 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem sigmaQuad_sigmaQuad (K : Type) [Field K] [Fact (Irreducible (quad K))]
    (u : AdjoinRoot (quad K)) : sigmaQuad K (sigmaQuad K u) = u := by
  have h : (sigmaQuad K).comp (sigmaQuad K) = AlgHom.id K (AdjoinRoot (quad K)) := by
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, sigmaQuad_zeta, AlgHom.id_apply]
    rw [map_pow, sigmaQuad_zeta]
    calc (zetaQ K ^ 2) ^ 2 = zetaQ K * zetaQ K ^ 3 := by ring
      _ = zetaQ K := by rw [zetaQ_cube, mul_one]
  exact congrArg (fun F => F u) h

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7

end
