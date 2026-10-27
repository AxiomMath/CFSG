module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical
import CFSG.ClassicalInvolution.Phan.PhanS22Witt
import TauCeti.LinearAlgebra.QuadraticForm.Witt.Extension

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open QuadraticMap Module

namespace Witt

universe u

section Basic

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem exists_linearEquiv_range_of_ker_eq {M : Type*} [AddCommGroup M] [Module F M]
    (A B : M →ₗ[F] V) (h : LinearMap.ker A = LinearMap.ker B) :
    ∃ f : LinearMap.range A ≃ₗ[F] LinearMap.range B,
      ∀ m, (f ⟨A m, LinearMap.mem_range_self A m⟩ : V) = B m := by
  refine ⟨A.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ h).trans B.quotKerEquivRange), fun m => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivRange_symm_apply_image]
  simp [Submodule.quotEquivOfEq_mk]

theorem exists_radical_coeffs {ι : Type*} [Fintype ι] (v : ι → V)
    (hU : ¬ (Q.restrict (Submodule.span F (Set.range v))).Nondegenerate) :
    ∃ a : ι → F, ∑ i, a i • v i ≠ 0 ∧ ∀ j, polar Q (∑ i, a i • v i) (v j) = 0 := by
  by_contra h
  apply hU
  apply QuadraticMap.nondegenerate_of_ker_polarBilin_eq_bot
  rw [LinearMap.ker_eq_bot']
  intro r hr
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp r.2
  by_contra hr0
  refine h ⟨a, ?_, fun j => ?_⟩
  · rw [ha]
    exact fun h0 => hr0 (Subtype.ext h0)
  · have := congrArg (fun L => L ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩) hr
    rw [ha]
    simpa [LinearMap.domRestrict₁₂_apply, polarBilin_apply_apply] using this

variable [FiniteDimensional F V]

theorem finrank_span_lt {ι : Type*} [Fintype ι] (v : ι → V) {y : V}
    (hy : y ∉ Submodule.span F (Set.range v)) :
    finrank F (Submodule.span F (Set.range v)) <
      finrank F (Submodule.span F (Set.range (fun i : Option ι => i.elim y v))) := by
  apply Submodule.finrank_lt_finrank_of_lt
  rw [IsConcreteLE.lt_iff_le_and_exists]
  refine ⟨Submodule.span_mono ?_, y, Submodule.subset_span ⟨none, rfl⟩, hy⟩
  rintro _ ⟨i, rfl⟩
  exact ⟨some i, rfl⟩

end Basic

section Regular

variable {F : Type*} [Field F] [Invertible (2 : F)] {V : Type*} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem exists_isometryEquiv_of_regular_span {ι : Type*} [Fintype ι] (v w : ι → V)
    (hgram : ∀ i j, polar Q (v i) (v j) = polar Q (w i) (w j))
    (hrel : ∀ c : ι → F, ∑ i, c i • v i = 0 ↔ ∑ i, c i • w i = 0)
    (hreg : (Q.restrict (Submodule.span F (Set.range v))).Nondegenerate) :
    ∃ e : Q.IsometryEquiv Q, ∀ i, e (v i) = w i := by
  classical
  set A := Fintype.linearCombination F v with hA
  set B := Fintype.linearCombination F w with hB
  have hker : LinearMap.ker A = LinearMap.ker B := by
    ext c
    simpa only [LinearMap.mem_ker, hA, hB, Fintype.linearCombination_apply] using hrel c
  obtain ⟨f, hf⟩ := exists_linearEquiv_range_of_ker_eq A B hker
  have h2 : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero
  have hQAB : ∀ c, Q (A c) = Q (B c) := by
    intro c
    have h := polar_sum_smul (Q := Q) v c c
    have h' := polar_sum_smul (Q := Q) w c c
    simp only [hgram] at h
    have h3 : polar Q (A c) (A c) = polar Q (B c) (B c) := by
      simp only [hA, hB, Fintype.linearCombination_apply]
      rw [h, h']
    rw [polar_self, polar_self] at h3
    simpa [nsmul_eq_mul, h2] using h3
  let f' : (Q.restrict (LinearMap.range A)).IsometryEquiv (Q.restrict (LinearMap.range B)) :=
    { f with
      map_app' := by
        rintro ⟨x, c, rfl⟩
        change Q ((f ⟨A c, LinearMap.mem_range_self A c⟩ : LinearMap.range B) : V) = Q (A c)
        rw [hf c, hQAB c] }
  have hreg' : (Q.restrict (LinearMap.range A)).Nondegenerate := by
    rwa [hA, Fintype.range_linearCombination]
  obtain ⟨e, he⟩ := f'.exists_extension hreg'
  refine ⟨e, fun i => ?_⟩
  have h1 := he ⟨A (Pi.single i 1), LinearMap.mem_range_self A _⟩
  have h2 := hf (Pi.single i 1)
  simp only [hA, hB, Fintype.linearCombination_apply_single, one_smul] at h1 h2
  exact h1.trans h2

theorem exists_isometryEquiv_aux (hQ : Q.Nondegenerate) :
    ∀ (n : ℕ) {ι : Type u} [Fintype ι] (v w : ι → V),
      (∀ i j, polar Q (v i) (v j) = polar Q (w i) (w j)) →
      (∀ c : ι → F, ∑ i, c i • v i = 0 ↔ ∑ i, c i • w i = 0) →
      finrank F V - finrank F (Submodule.span F (Set.range v)) = n →
      ∃ e : Q.IsometryEquiv Q, ∀ i, e (v i) = w i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ v w hgram hrel hn
  by_cases hreg : (Q.restrict (Submodule.span F (Set.range v))).Nondegenerate
  · exact exists_isometryEquiv_of_regular_span v w hgram hrel hreg
  · obtain ⟨a, hr0, hrv⟩ := exists_radical_coeffs v hreg
    obtain ⟨y, y', hy1, hy0, hyy, hy1', hy0', hrw⟩ :=
      exists_extend_vectors hQ v w hgram hrel a rfl rfl hr0 hrv
    obtain ⟨hgram', hrel'⟩ := family_extend v w hgram hrel hy1 hy1' hy0 hy0' hrv hrw hyy
    have hlt := finrank_span_lt v (not_mem_span_of_polar v hy1 hrv)
    have hle := Submodule.finrank_le
      (Submodule.span F (Set.range (fun i : Option ι => i.elim y v)))
    obtain ⟨e, he⟩ := ih (finrank F V - finrank F
      (Submodule.span F (Set.range (fun i : Option ι => i.elim y v)))) (by omega)
      (fun i : Option ι => i.elim y v) (fun i : Option ι => i.elim y' w) hgram' hrel' rfl
    exact ⟨e, fun i => he (some i)⟩

end Regular

end Witt

section Main

variable {F : Type*} [Field F] [Invertible (2 : F)] {V : Type*} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem exists_isometryEquiv_of_family (hQ : Q.Nondegenerate)
    {ι : Type*} [Fintype ι] (v w : ι → V)
    (hgram : ∀ i j, QuadraticMap.polar Q (v i) (v j) = QuadraticMap.polar Q (w i) (w j))
    (hrel : ∀ c : ι → F, ∑ i, c i • v i = 0 ↔ ∑ i, c i • w i = 0) :
    ∃ e : Q.IsometryEquiv Q, ∀ i, e (v i) = w i :=
  Witt.exists_isometryEquiv_aux hQ _ v w hgram hrel rfl

end Main

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
