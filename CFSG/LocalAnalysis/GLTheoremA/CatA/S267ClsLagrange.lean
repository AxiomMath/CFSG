module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsForm
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {V : Type*} [AddCommGroup V] [Module K V]

theorem prod_X_sub_C_eq : ∏ c : K, (X - C c) = (X ^ Fintype.card K - X : K[X]) := by
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  have hmon : (X ^ Fintype.card K - X : K[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  have hroots := FiniteField.roots_X_pow_card_sub_X K
  have hcard : Multiset.card (X ^ Fintype.card K - X : K[X]).roots =
      (X ^ Fintype.card K - X : K[X]).natDegree := by
    rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq K h1, Finset.card_val,
      Finset.card_univ]
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hcard
  rw [hroots] at h
  rw [← h]
  rfl

theorem aeval_prod_X_sub_C_eq_zero (g : Module.End K V) (hg : g ^ Fintype.card K = g) :
    aeval g (∏ c : K, (X - C c)) = 0 := by
  rw [prod_X_sub_C_eq, map_sub, map_pow, aeval_X, hg, sub_self]

theorem exists_eigenvector (g : Module.End K V) (hg : g ^ Fintype.card K = g) (W : Submodule K V)
    (hW : ∀ w ∈ W, g w ∈ W) (hW0 : W ≠ ⊥) : ∃ c : K, ∃ w ∈ W, w ≠ 0 ∧ g w = c • w := by
  by_contra hcon
  push Not at hcon
  have hinj : ∀ s : Finset K, ∀ w ∈ W, aeval g (∏ c ∈ s, (X - C c)) w = 0 → w = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro w _ hw; simpa using hw
    | insert c s hcs ih =>
      intro w hw h0
      rw [Finset.prod_insert hcs, map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C,
        LinearMap.sub_apply, sub_eq_zero] at h0
      have hmem : aeval g (∏ c ∈ s, (X - C c)) w ∈ W := by
        have : ∀ p : K[X], ∀ u ∈ W, aeval g p u ∈ W := by
          intro p
          induction p using Polynomial.induction_on with
          | C a => intro u hu; simpa using W.smul_mem a hu
          | add p₁ p₂ h₁ h₂ => intro u hu; simpa using W.add_mem (h₁ u hu) (h₂ u hu)
          | monomial n a ih =>
            intro u hu
            rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, aeval_X]
            exact ih _ (hW u hu)
        exact this _ w hw
      by_cases hne : aeval g (∏ c ∈ s, (X - C c)) w = 0
      · exact ih w hw hne
      · exact absurd (by
          rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply] at h0
          exact h0) (hcon c _ hmem hne)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  exact hw0 (hinj Finset.univ w hw (by rw [aeval_prod_X_sub_C_eq_zero g hg, LinearMap.zero_apply]))

@[expose] noncomputable def lagPoly (c : K) : K[X] := Lagrange.basis Finset.univ id c

@[expose] noncomputable def lagProj (g : Module.End K V) (c : K) : Module.End K V :=
  aeval g (lagPoly c)

theorem lagProj_apply_of_eigen (g : Module.End K V) {c : K} {v : V} (hv : g v = c • v) :
    lagProj g c v = v := by
  by_cases hv0 : v = 0
  · rw [hv0, map_zero]
  have hev : g.HasEigenvector c v :=
    ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩
  have h1 : (lagPoly c).eval c = 1 := by
    simpa [lagPoly] using Lagrange.eval_basis_self (v := (id : K → K)) (Set.injOn_id _)
      (Finset.mem_univ c)
  rw [lagProj, Module.End.aeval_apply_of_hasEigenvector hev, h1, one_smul]

private theorem X_sub_C_mul_lagPoly (c : K) :
    (X - C c) * lagPoly c =
      C (∏ c' ∈ Finset.univ.erase c, (c - c')⁻¹) * (X ^ Fintype.card K - X) := by
  rw [lagPoly, Lagrange.basis, ← prod_X_sub_C_eq, ← Finset.mul_prod_erase Finset.univ
    (fun c' => X - C c') (Finset.mem_univ c)]
  simp only [Lagrange.basisDivisor, id, Finset.prod_mul_distrib, map_prod]
  ring

theorem apply_lagProj (g : Module.End K V) (hg : g ^ Fintype.card K = g) (c : K) (v : V) :
    g (lagProj g c v) = c • lagProj g c v := by
  have h := congrArg (aeval g) (X_sub_C_mul_lagPoly (K := K) c)
  rw [map_mul, map_mul, map_sub, map_sub, map_pow, aeval_X, aeval_C, hg, sub_self, mul_zero]
    at h
  have h' := congrArg (fun f : Module.End K V => f v) h
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.zero_apply,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply] at h'
  rw [lagProj]
  exact sub_eq_zero.mp h'

theorem lagProj_comm (g T : Module.End K V) (h : Commute g T) (c : K) :
    Commute (lagProj g c) T := by
  have key : ∀ p : K[X], Commute (aeval g p) T := by
    intro p
    induction p using Polynomial.induction_on with
    | C a => simpa using Algebra.commute_algebraMap_left a T
    | add p₁ p₂ h₁ h₂ => simpa using h₁.add_left h₂
    | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      exact ih.mul_left h
  exact key _

theorem sum_lagProj (g : Module.End K V) : ∑ c : K, lagProj g c = 1 := by
  simp only [lagProj, lagPoly]
  rw [← map_sum, Lagrange.sum_basis (Set.injOn_id _) Finset.univ_nonempty, map_one]

theorem lagProj_left (β : LinearMap.BilinForm K V) (g g' : Module.End K V)
    (hgg : ∀ u v, β (g u) v = β u (g' v)) (c : K) (u v : V) :
    β (lagProj g c u) v = β u (lagProj g' c v) := by
  have key : ∀ p : K[X], ∀ u v, β (aeval g p u) v = β u (aeval g' p v) := by
    intro p
    induction p using Polynomial.induction_on with
    | C a => intro u v; simp [Algebra.algebraMap_eq_smul_one]
    | add p₁ p₂ h₁ h₂ => intro u v; simp [h₁, h₂]
    | monomial n a ih =>
      intro u v
      have e1 : (C a * X ^ (n + 1) : K[X]) = C a * X ^ n * X := by ring
      have e2 : (C a * X ^ (n + 1) : K[X]) = X * (C a * X ^ n) := by ring
      calc β (aeval g (C a * X ^ (n + 1)) u) v = β (aeval g (C a * X ^ n) (g u)) v := by
            rw [e1, map_mul (aeval g) (C a * X ^ n) X, Module.End.mul_apply, aeval_X]
        _ = β (g u) (aeval g' (C a * X ^ n) v) := ih _ _
        _ = β u (g' (aeval g' (C a * X ^ n) v)) := hgg _ _
        _ = β u (aeval g' (C a * X ^ (n + 1)) v) := by
            rw [e2, map_mul (aeval g') X (C a * X ^ n), Module.End.mul_apply, aeval_X]
  exact key _ u v

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
