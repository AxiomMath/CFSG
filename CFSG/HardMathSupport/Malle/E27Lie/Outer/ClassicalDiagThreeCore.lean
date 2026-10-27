module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

open Polynomial Module

namespace CFSG.HardMathSupport.Malle.E27Lie

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem commute_aeval_of_commute {f g : Module.End F V} (h : Commute g f) (p : F[X]) :
    Commute g (aeval f p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n a =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right a g).mul_right (h.pow_right n)

theorem scalar_of_commute_irreducible [FiniteDimensional F V] (hV : finrank F V = 3)
    (f g : Module.End F V) (c a : F) (hirr : Irreducible (X ^ 3 - C c : F[X]))
    (hf : aeval f (X ^ 3 - C c : F[X]) = 0) (hcomm : Commute g f)
    (hdet : LinearMap.det g = 1) (hg : g ^ 3 = algebraMap F (Module.End F V) a) :
    ∃ s : F, g = algebraMap F (Module.End F V) s := by
  classical
  set μ : F[X] := X ^ 3 - C c with hμ
  have : Fact (Irreducible μ) := ⟨hirr⟩
  have hμ0 : μ ≠ 0 := hirr.ne_zero
  have hμdeg : μ.natDegree = 3 := by rw [hμ, natDegree_X_pow_sub_C]
  have hVnt : Nontrivial V := by
    rw [← finrank_pos_iff (R := F)]; omega
  let E := AdjoinRoot μ
  have hEdim : finrank F E = 3 := by
    rw [(AdjoinRoot.powerBasis hμ0).finrank, AdjoinRoot.powerBasis_dim, hμdeg]
  have hEfin : FiniteDimensional F E := (AdjoinRoot.powerBasis hμ0).finite
  have hEint : Algebra.IsIntegral F E := Algebra.IsIntegral.of_finite F E
  have hker : ∀ b : F[X], b ∈ (Ideal.span {μ} : Ideal F[X]) → aeval f b = 0 := by
    intro b hb
    obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton.1 hb
    rw [map_mul, hf, zero_mul]
  let φ : E →ₐ[F] Module.End F V := Ideal.Quotient.liftₐ (Ideal.span {μ}) (aeval f) hker
  have hφinj : Function.Injective φ := (φ : E →+* Module.End F V).injective
  have hφmk : ∀ p : F[X], φ (AdjoinRoot.mk μ p) = aeval f p := fun p => by
    rfl
  have hcomφ : ∀ e : E, Commute g (φ e) := by
    intro e
    induction e using AdjoinRoot.induction_on with
    | ih p => rw [hφmk]; exact commute_aeval_of_commute hcomm p
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let ψ : E →ₗ[F] V :=
    { toFun := fun e => φ e v
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp }
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e he
    by_contra hne
    apply hv
    have h1 : φ e⁻¹ (φ e v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel₀ hne, map_one]; rfl
    rw [← h1]
    have : φ e v = 0 := he
    rw [this, map_zero]
  have hψsurj : Function.Surjective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hEdim, hV])).1 hψinj
  obtain ⟨e, he⟩ := hψsurj (g v)
  have hge : g = φ e := by
    refine LinearMap.ext fun w => ?_
    obtain ⟨e', rfl⟩ := hψsurj w
    show g (φ e' v) = φ e (φ e' v)
    have h1 : g (φ e' v) = φ e' (g v) := by
      have := (hcomφ e').eq
      exact (congrArg (fun m => m v) this)
    rw [h1, ← he]
    show φ e' (φ e v) = φ e (φ e' v)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  subst hge
  have he3 : e ^ 3 = algebraMap F E a := by
    apply hφinj
    rw [map_pow, hg, AlgHom.commutes]
  by_cases hmem : e ∈ (algebraMap F E).range
  · obtain ⟨s, rfl⟩ := hmem
    exact ⟨s, by rw [AlgHom.commutes]⟩
  · exfalso
    have hint : IsIntegral F e := Algebra.IsIntegral.isIntegral e
    have hdvd3 : (minpoly F e).natDegree ∣ 3 := hEdim ▸ minpoly.degree_dvd hint
    have hne1 : (minpoly F e).natDegree ≠ 1 := by
      rw [Ne, minpoly.natDegree_eq_one_iff]; exact hmem
    have hdeg3 : (minpoly F e).natDegree = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h | h
      · exact absurd h hne1
      · exact h
    have hmin : minpoly F e = X ^ 3 - C a := by
      have hd : minpoly F e ∣ (X ^ 3 - C a : F[X]) := by
        apply minpoly.dvd
        simp [he3]
      exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
        (monic_X_pow_sub_C _ (by norm_num)) hd (by rw [hdeg3, natDegree_X_pow_sub_C])).symm
    have hmin' : minpoly F (φ e) = X ^ 3 - C a := by
      rw [minpoly.algHom_eq φ hφinj, hmin]
    have hch : (φ e).charpoly = X ^ 3 - C a := by
      have hd : minpoly F (φ e) ∣ (φ e).charpoly := LinearMap.minpoly_dvd_charpoly _
      rw [hmin'] at hd
      have hmon : (φ e).charpoly.Monic := LinearMap.charpoly_monic _
      have hnd : (φ e).charpoly.natDegree = 3 := by
        rw [LinearMap.charpoly_natDegree, hV]
      exact eq_of_monic_of_dvd_of_natDegree_le (monic_X_pow_sub_C _ (by norm_num)) hmon hd
        (by rw [hnd, natDegree_X_pow_sub_C])
    have hdet' := LinearMap.det_eq_sign_charpoly_coeff (φ e)
    rw [hdet, hch, hV] at hdet'
    have ha : a = 1 := by
      simp [coeff_sub, coeff_X_pow, coeff_C] at hdet'
      linear_combination (-1 : F) * hdet'
    subst ha
    have hirr' : Irreducible (X ^ 3 - C (1 : F) : F[X]) := by
      rw [← hmin]; exact minpoly.irreducible hint
    have hroot : (X ^ 3 - C (1 : F) : F[X]).IsRoot 1 := by simp
    have := degree_eq_one_of_irreducible_of_root hirr' hroot
    rw [degree_X_pow_sub_C (by norm_num)] at this
    norm_num at this

end CFSG.HardMathSupport.Malle.E27Lie
