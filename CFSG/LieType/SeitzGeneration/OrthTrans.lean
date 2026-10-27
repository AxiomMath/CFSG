module

public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts

public section

namespace CFSG.LieType.SeitzGeneration

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

section Submod

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem aeval_mem_of_stable {x : Module.End K V} {S : Submodule K V}
    (hS : ∀ s ∈ S, x s ∈ S) (f : K[X]) {s : V} (hs : s ∈ S) : aeval x f s ∈ S := by
  have hpow : ∀ n : ℕ, ((x ^ n) s) ∈ S := by
    intro n
    induction n with
    | zero => simpa using hs
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hS _ ih
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, LinearMap.add_apply]
    exact S.add_mem hf hg
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact S.smul_mem _ (hpow n)

@[expose] noncomputable def stableSubmodule (x : Module.End K V) (h : K[X]) (S : Submodule K V)
    (hS : ∀ s ∈ S, x s ∈ S) : Submodule (AdjoinRoot h) (primaryComponent x h) where
  carrier := {v | (v : V) ∈ S}
  add_mem' := fun {a b} ha hb => S.add_mem ha hb
  zero_mem' := S.zero_mem
  smul_mem' := fun e v hv => by
    induction e using AdjoinRoot.induction_on with
    | ih f =>
      change ((AdjoinRoot.mk h f • v : primaryComponent x h) : V) ∈ S
      rw [coe_mk_smul_primaryComponent]
      exact aeval_mem_of_stable hS f hv

end Submod

section Det

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M] [FiniteDimensional F M]

theorem det_one_add_of_sq_eq_zero (τ : M →ₗ[F] M) (hτ : τ ∘ₗ τ = 0) :
    LinearMap.det (1 + τ) = 1 := by
  have hnil : IsNilpotent τ := ⟨2, by rw [pow_two]; exact hτ⟩
  have h1 : (τ - (-1 : F) • (1 : M →ₗ[F] M)).charpoly = τ.charpoly.comp (X + C (-1)) :=
    LinearMap.charpoly_sub_smul τ (-1)
  have h2 : τ - (-1 : F) • (1 : M →ₗ[F] M) = 1 + τ := by
    rw [neg_smul, one_smul, sub_neg_eq_add, add_comm]
  rw [h2, hnil.charpoly_eq_X_pow_finrank] at h1
  rw [LinearMap.det_eq_sign_charpoly_coeff, h1]
  have h3 : ((X : F[X]) ^ finrank F M).comp (X + C (-1)) = (X - 1) ^ finrank F M := by
    rw [pow_comp, X_comp, map_neg, map_one, ← sub_eq_add_neg]
  rw [h3, coeff_zero_eq_eval_zero, eval_pow]
  simp [← mul_pow]

end Det

section Transvection

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem exists_paired_transvection (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp3 : 3 < p)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h)
    {S : Submodule K V} (hS : ∀ s ∈ S, x s ∈ S) {z w : V} (hz : z ∈ S)
    (hzh : z ∈ primaryComponent x.toLinearMap h) (hw : w ∈ primaryComponent x.toLinearMap h)
    (hwS : w ∉ S) :
    ∃ g : V ≃ₗ[K] V, g ∈ orthDerived Q ∧ g * x = x * g ∧
      (∀ u ∈ primaryComponent x.toLinearMap h, g u - u ∈ S) ∧
      (∀ u ∈ S, u ∈ primaryComponent x.toLinearMap h → g u = u) ∧ g w = w + z := by
  classical
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  let S' := stableSubmodule x.toLinearMap h S hS
  let w' : primaryComponent x.toLinearMap h := ⟨w, hw⟩
  let z' : primaryComponent x.toLinearMap h := ⟨z, hzh⟩
  have hw' : w' ∉ S' := hwS
  have hz' : z' ∈ S' := hz
  obtain ⟨φ, hφw, hφS⟩ := Submodule.exists_le_ker_of_notMem hw'
  let φ₁ : primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h := (φ w')⁻¹ • φ
  have hφ₁w : φ₁ w' = 1 := by
    change (φ w')⁻¹ • φ w' = 1
    rw [smul_eq_mul, inv_mul_cancel₀ hφw]
  have hφ₁S : ∀ v ∈ S', φ₁ v = 0 := fun v hv => by
    change (φ w')⁻¹ • φ v = 0
    rw [LinearMap.mem_ker.mp (hφS hv), smul_zero]
  let τ : primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] primaryComponent x.toLinearMap h :=
    φ₁.smulRight z'
  have hτ : τ ∘ₗ τ = 0 := by
    refine LinearMap.ext fun v => ?_
    change φ₁ (φ₁ v • z') • z' = 0
    rw [map_smul, hφ₁S z' hz', smul_zero, zero_smul]
  have hτv : ∀ v, τ v = φ₁ v • z' := fun v => rfl
  let γ : primaryComponent x.toLinearMap h ≃ₗ[AdjoinRoot h] primaryComponent x.toLinearMap h :=
    LinearEquiv.ofLinearMap (1 + τ) (1 - τ)
      (LinearMap.ext fun v => by
        have := LinearMap.congr_fun hτ v
        simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
        simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
          Module.End.one_apply, map_sub, this]
        abel)
      (LinearMap.ext fun v => by
        have := LinearMap.congr_fun hτ v
        simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
        simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
          Module.End.one_apply, map_add, this]
        abel)
  have hdet : γ.det = 1 := Units.ext (by
    rw [LinearEquiv.coe_det]
    exact det_one_add_of_sq_eq_zero τ hτ)
  obtain ⟨g, hg⟩ := hx.specialToSL_surjective_paired hh hne ⟨γ, hdet⟩
  have hgact : ∀ v : primaryComponent x.toLinearMap h,
      g.1 (v : V) = ((v + τ v : primaryComponent x.toLinearMap h) : V) := fun v => by
    have := (specialToSL_apply (Q := Q) (x := x) h g v).symm
    rw [hg] at this
    exact this
  have hgΩ : g.1 ∈ orthDerived Q := hx.specialBlock_le_orthDerived hp hp3 hh hne1 hm g.2
  have hgC : g.1 * x = x * g.1 := by
    have := (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (specialBlock_le_isometryCentralizer h g.2)).2) x (by simp)
    exact this.symm
  refine ⟨g.1, hgΩ, hgC, fun u hu => ?_, fun u hu huh => ?_, ?_⟩
  · have := hgact ⟨u, hu⟩
    change g.1 u - u ∈ S
    rw [this]
    rw [Submodule.coe_add, add_sub_cancel_left, hτv]
    exact S'.smul_mem _ hz'
  · have := hgact ⟨u, huh⟩
    rw [this, hτv, hφ₁S ⟨u, huh⟩ hu, zero_smul, add_zero]
  · have := hgact w'
    change g.1 w = w + z
    rw [this, hτv, hφ₁w, one_smul]
    rfl

end Transvection

end CFSG.LieType.SeitzGeneration
