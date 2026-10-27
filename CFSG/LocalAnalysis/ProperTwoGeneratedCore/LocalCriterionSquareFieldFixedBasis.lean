module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u v

variable {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M]

theorem field_involution_apply (sigma : RingAut F) (hsigma : sigma ^ 2 = 1) (c : F) :
    sigma (sigma c) = c := by
  have h := DFunLike.congr_fun hsigma c
  simpa [pow_two] using h

theorem semilinear_trace_fixed (T : M ≃+ M) (hT : Function.Involutive T) (v : M) :
    T (v + T v) = v + T v := by
  rw [map_add, hT]
  exact add_comm _ _

theorem semilinear_weighted_trace_fixed
    (sigma : RingAut F) (hsigma : sigma ^ 2 = 1)
    (T : M ≃+ M) (hT : Function.Involutive T)
    (hsmul : ∀ (c : F) (v : M), T (c • v) = sigma c • T v) (c : F) (v : M) :
    T (sigma c • v + c • T v) = sigma c • v + c • T v := by
  rw [map_add, hsmul, hsmul, field_involution_apply sigma hsigma, hT]
  exact add_comm _ _

theorem semilinear_fixed_span_eq_top [CharP F 2]
    (sigma : RingAut F) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (T : M ≃+ M) (hT : Function.Involutive T)
    (hsmul : ∀ (c : F) (v : M), T (c • v) = sigma c • T v) :
    Submodule.span F {v : M | T v = v} = ⊤ := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : F, sigma c ≠ c := by
    by_contra h
    apply hne
    ext c
    exact not_not.mp (not_exists.mp h c)
  have hd : sigma c + c ≠ 0 := by
    intro hd
    exact hc (CharTwo.add_eq_zero.mp hd)
  apply top_unique
  intro v _hv
  let w : M := v + T v
  let u : M := sigma c • v + c • T v
  have hw : w ∈ Submodule.span F {v : M | T v = v} :=
    Submodule.subset_span (semilinear_trace_fixed T hT v)
  have hu : u ∈ Submodule.span F {v : M | T v = v} :=
    Submodule.subset_span (semilinear_weighted_trace_fixed sigma hsigma T hT hsmul c v)
  have hrecover : u + c • w = (sigma c + c) • v := by
    calc
      u + c • w = (sigma c + c) • v + (c + c) • T v := by
        dsimp [u, w]
        rw [smul_add, add_smul, add_smul]
        abel
      _ = (sigma c + c) • v := by rw [CharTwo.add_self_eq_zero, zero_smul, add_zero]
  have hmem := (Submodule.span F {v : M | T v = v}).add_mem hu
    ((Submodule.span F {v : M | T v = v}).smul_mem c hw)
  rw [hrecover] at hmem
  have hscaled := (Submodule.span F {v : M | T v = v}).smul_mem (sigma c + c)⁻¹ hmem
  simpa [smul_smul, hd] using hscaled

theorem exists_char_two_semilinear_fixed_basis [CharP F 2]
    (sigma : RingAut F) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (T : (Fin 2 → F) ≃+ (Fin 2 → F)) (hT : Function.Involutive T)
    (hsmul : ∀ (c : F) (v : Fin 2 → F), T (c • v) = sigma c • T v) :
    ∃ b : Module.Basis (Fin 2) F (Fin 2 → F), ∀ j, T (b j) = b j := by
  classical
  have hspan : ⊤ ≤ Submodule.span F {v : Fin 2 → F | T v = v} := by
    rw [semilinear_fixed_span_eq_top sigma hsigma hne T hT hsmul]
  let b := Module.Basis.ofSpan hspan
  let e := b.indexEquiv (Pi.basisFun F (Fin 2))
  refine ⟨b.reindex e, ?_⟩
  intro j
  have hj : b (e.symm j) ∈ {v : Fin 2 → F | T v = v} :=
    Module.Basis.ofSpan_subset hspan ⟨e.symm j, rfl⟩
  change T (b (e.symm j)) = b (e.symm j) at hj
  simpa only [Module.Basis.reindex_apply] using hj

end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
