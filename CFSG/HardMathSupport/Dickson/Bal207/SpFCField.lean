module

public import Mathlib.RingTheory.Trace.Basic

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open Polynomial

variable {F : Type} [Field F] (g : F[X])

@[expose] noncomputable def extAut (σ : F ≃+* F) (hσ : g.map (σ : F →+* F) = g) :
    AdjoinRoot g ≃+* AdjoinRoot g :=
  AdjoinRoot.mapRingEquiv σ g g (by rw [hσ])

variable {g}

theorem extAut_mk {σ : F ≃+* F} (hσ : g.map (σ : F →+* F) = g) (p : F[X]) :
    extAut g σ hσ (AdjoinRoot.mk g p) = AdjoinRoot.mk g (p.map (σ : F →+* F)) := by
  rw [extAut, AdjoinRoot.coe_mapRingEquiv, AdjoinRoot.map, AdjoinRoot.lift_mk,
    ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map, AdjoinRoot.algebraMap_eq]

theorem extAut_of {σ : F ≃+* F} (hσ : g.map (σ : F →+* F) = g) (c : F) :
    extAut g σ hσ (AdjoinRoot.of g c) = AdjoinRoot.of g (σ c) := by
  rw [← AdjoinRoot.mk_C, extAut_mk, Polynomial.map_C, AdjoinRoot.mk_C]
  rfl

theorem extAut_root {σ : F ≃+* F} (hσ : g.map (σ : F →+* F) = g) :
    extAut g σ hσ (AdjoinRoot.root g) = AdjoinRoot.root g := by
  rw [← AdjoinRoot.mk_X, extAut_mk, Polynomial.map_X]

theorem extAut_mul {σ σ' : F ≃+* F} (hσ : g.map (σ : F →+* F) = g)
    (hσ' : g.map (σ' : F →+* F) = g) (hσσ' : g.map ((σ * σ' : F ≃+* F) : F →+* F) = g) :
    extAut g (σ * σ') hσσ' = extAut g σ hσ * extAut g σ' hσ' := by
  refine RingEquiv.ext fun z => ?_
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  change extAut g (σ * σ') hσσ' (AdjoinRoot.mk g p) =
    extAut g σ hσ (extAut g σ' hσ' (AdjoinRoot.mk g p))
  rw [extAut_mk, extAut_mk, extAut_mk, Polynomial.map_map]
  rfl

theorem extAut_one (h1 : g.map ((1 : F ≃+* F) : F →+* F) = g) : extAut g 1 h1 = 1 := by
  refine RingEquiv.ext fun z => ?_
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [extAut_mk]
  change AdjoinRoot.mk g (p.map (RingHom.id F)) = AdjoinRoot.mk g p
  rw [Polynomial.map_id]

theorem extAut_eq_one_iff [Fact (Irreducible g)] {σ : F ≃+* F}
    (hσ : g.map (σ : F →+* F) = g) : extAut g σ hσ = 1 ↔ σ = 1 := by
  constructor
  · intro h
    ext c
    apply (AdjoinRoot.of g).injective
    have hc := extAut_of hσ c
    rw [h] at hc
    exact hc.symm
  · intro h
    subst σ
    exact extAut_one hσ

section Trace

variable [Fact (Irreducible g)]

theorem X_sq_add_X_add_one_ne_zero' : (X ^ 2 + X + 1 : F[X]) ≠ 0 := by
  intro h
  have := congrArg (fun p : F[X] => p.coeff 0) h
  simp at this

theorem root_sq_eq (hg : g = X ^ 2 + X + 1) :
    AdjoinRoot.root g ^ 2 = -AdjoinRoot.root g - 1 := by
  have h := AdjoinRoot.eval₂_root g
  rw [hg] at h
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h
  have h' : AdjoinRoot.root g ^ 2 + AdjoinRoot.root g + 1 = 0 := by
    subst hg
    exact h
  linear_combination h'

theorem root_pow_three (hg : g = X ^ 2 + X + 1) : AdjoinRoot.root g ^ 3 = 1 := by
  have h := root_sq_eq hg
  linear_combination (AdjoinRoot.root g - 1) * h

theorem finrank_adjoinRoot (hg : g = X ^ 2 + X + 1) :
    Module.finrank F (AdjoinRoot g) = 2 := by
  have hg0 : g ≠ 0 := hg ▸ X_sq_add_X_add_one_ne_zero'
  rw [(AdjoinRoot.powerBasis hg0).finrank, AdjoinRoot.powerBasis_dim, hg]
  compute_degree!

theorem trace_one_adjoinRoot (hg : g = X ^ 2 + X + 1) :
    Algebra.trace F (AdjoinRoot g) 1 = 2 := by
  rw [← map_one (algebraMap F (AdjoinRoot g)), Algebra.trace_algebraMap, finrank_adjoinRoot hg]
  norm_num

theorem trace_root_adjoinRoot (hg : g = X ^ 2 + X + 1) :
    Algebra.trace F (AdjoinRoot g) (AdjoinRoot.root g) = -1 := by
  have hg0 : g ≠ 0 := hg ▸ X_sq_add_X_add_one_ne_zero'
  have hmon : g.Monic := by
    rw [hg]
    monicity!
  have h := (AdjoinRoot.powerBasis hg0).trace_gen_eq_nextCoeff_minpoly
  rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic hmon, AdjoinRoot.powerBasis_gen] at h
  rw [h, hg]
  have hdeg : (X ^ 2 + X + 1 : F[X]).natDegree = 2 := by compute_degree!
  rw [nextCoeff, if_neg (by rw [hdeg]; norm_num), hdeg]
  simp [coeff_X, coeff_one]

theorem trace_root_pow (hg : g = X ^ 2 + X + 1) (n : ℕ) :
    ∃ m : ℤ, Algebra.trace F (AdjoinRoot g) (AdjoinRoot.root g ^ n) = m := by
  have hn : AdjoinRoot.root g ^ n = AdjoinRoot.root g ^ (n % 3) := by
    conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, root_pow_three hg, one_pow, mul_one]
  rw [hn]
  have h3 : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  interval_cases (n % 3)
  · exact ⟨2, by rw [pow_zero, trace_one_adjoinRoot hg]; norm_num⟩
  · exact ⟨-1, by rw [pow_one, trace_root_adjoinRoot hg]; norm_num⟩
  · refine ⟨-1, ?_⟩
    rw [root_sq_eq hg, map_sub, map_neg, trace_root_adjoinRoot hg, trace_one_adjoinRoot hg]
    norm_num

theorem trace_extAut (hg : g = X ^ 2 + X + 1) {σ : F ≃+* F} (hσ : g.map (σ : F →+* F) = g)
    (z : AdjoinRoot g) :
    Algebra.trace F (AdjoinRoot g) (extAut g σ hσ z) = σ (Algebra.trace F (AdjoinRoot g) z) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
    have h1 : AdjoinRoot.mk g (monomial n c) = AdjoinRoot.of g c * AdjoinRoot.root g ^ n := by
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    rw [h1, map_mul, map_pow, extAut_of, extAut_root, ← AdjoinRoot.algebraMap_eq,
      ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      map_mul]
    obtain ⟨m, hm⟩ := trace_root_pow hg n
    rw [hm, map_intCast]

theorem eq_of_forall_trace_mul_eq (hg : g = X ^ 2 + X + 1) {y y' : AdjoinRoot g}
    (h : ∀ c, Algebra.trace F (AdjoinRoot g) (c * y) = Algebra.trace F (AdjoinRoot g) (c * y')) :
    y = y' := by
  by_contra hne
  have hsub : y - y' ≠ 0 := sub_ne_zero.mpr hne
  have h1 := h (AdjoinRoot.root g * (y - y')⁻¹)
  rw [← sub_eq_zero, ← map_sub, ← mul_sub, mul_assoc, inv_mul_cancel₀ hsub, mul_one,
    trace_root_adjoinRoot hg] at h1
  exact one_ne_zero (neg_eq_zero.mp h1)

end Trace

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end
