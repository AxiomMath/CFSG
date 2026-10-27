module

public import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroupGL
public import CFSG.LieType.AlgebraicGroups.ReducedGroupSmooth
public import CFSG.LieType.AlgebraicGroups.RootWordRegular
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley AlgebraicGeometry WithConv TensorProduct

open scoped CFSG.ConvolutionPoints

section Smooth

variable {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [HopfAlgebra k A]
  [Algebra.FiniteType k A]

theorem IsConnectedAlgebraicSubgroup.smooth {H : Subgroup (WithConv (A →ₐ[k] k))}
    (h : IsConnectedAlgebraicSubgroup k H) :
    Algebra.Smooth k (A ⧸ subgroupIdeal H) ∧
      Smooth (Spec (CommRingCat.of (A ⧸ subgroupIdeal H)) ↘ Spec (CommRingCat.of k)) ∧
      IrreducibleSpace (PrimeSpectrum (A ⧸ subgroupIdeal H)) := by
  have := h.isReduced
  have := h.isDomain
  exact ⟨(smooth_of_hopfAlgebra_of_isReduced k _).1, (smooth_of_hopfAlgebra_of_isReduced k _).2,
    inferInstance⟩

end Smooth

section Adjoint

variable (τ : Tag) (k : Type) [Field k]

abbrev adjointPointSubgroup
    : Subgroup (WithConv (GLCoord k (Label τ) →ₐ[k] k)) :=
  (adjointGroup τ k).map (modGLPoint τ k).toMonoidHom

theorem transportPoints_modGLPoint :
    transportPoints (modGLPoint τ k) (adjointGroup τ k) =
      {y | (modGLPoint τ k).symm (toConv y) ∈ adjointGroup τ k} := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    rwa [Set.mem_ofPred_eq, toConv_ofConv, MulEquiv.symm_apply_apply]
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [MulEquiv.apply_symm_apply, ofConv_toConv]

variable {τ k}

theorem adjointGroup_realization [IsAlgClosed k]
    (hcons : IsPointConstructible k
      {y : GLCoord k (Label τ) →ₐ[k] k | (modGLPoint τ k).symm (toConv y) ∈ adjointGroup τ k})
    (hirr : IsPointIrreducible k
      {y : GLCoord k (Label τ) →ₐ[k] k | (modGLPoint τ k).symm (toConv y) ∈ adjointGroup τ k}) :
    IsPointClosed k
        {y : GLCoord k (Label τ) →ₐ[k] k | (modGLPoint τ k).symm (toConv y) ∈ adjointGroup τ k} ∧
      IsConnectedAlgebraicSubgroup k (adjointPointSubgroup τ k) ∧
      Algebra.Smooth k (GLCoord k (Label τ) ⧸ subgroupIdeal (adjointPointSubgroup τ k)) ∧
      IrreducibleSpace
        (PrimeSpectrum (GLCoord k (Label τ) ⧸ subgroupIdeal (adjointPointSubgroup τ k))) ∧
      ∃ e : WithConv ((GLCoord k (Label τ) ⧸ subgroupIdeal (adjointPointSubgroup τ k)) →ₐ[k] k) ≃*
          adjointGroup τ k, ∀ φ,
        ((e φ : adjointGroup τ k) : ModGL τ k) =
          (modGLPoint τ k).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _))) := by
  rw [← transportPoints_modGLPoint] at hcons hirr ⊢
  obtain ⟨hcl, h, he⟩ := isConnectedAlgebraicSubgroup_map (modGLPoint τ k) _ hcons hirr
  obtain ⟨hsm, -, hirrsp⟩ := h.smooth
  exact ⟨hcl, h, hsm, hirrsp, he⟩

end Adjoint

section Graph

variable {τ : Tag} {k : Type} [Field k] {M : ℕ}

@[expose] def graphSubgroup
    (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k) :
    Subgroup (ModGL τ k × Matrix.GeneralLinearGroup (Fin M) k) :=
  ((adjointGroup τ k).subtype.prod ψ).range

theorem mem_graphSubgroup
    {ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k}
    {p : ModGL τ k × Matrix.GeneralLinearGroup (Fin M) k} :
    p ∈ graphSubgroup ψ ↔ ∃ g : adjointGroup τ k, ((g : ModGL τ k), ψ g) = p :=
  MonoidHom.mem_range

variable (τ k M) in
@[expose] def modGLPairPoint :
    ModGL τ k × Matrix.GeneralLinearGroup (Fin M) k ≃*
      WithConv (GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) →ₐ[k] k) :=
  ((modGLEquivGL τ k).prodCongr (MulEquiv.refl _)).trans glPairPointEquiv

theorem modGLPairPoint_apply
    (p : ModGL τ k × Matrix.GeneralLinearGroup (Fin M) k) :
    (modGLPairPoint τ k M p).ofConv =
      tensorPointEquiv ((modGLPoint τ k p.1).ofConv, (glPointEquiv p.2).ofConv) :=
  rfl

abbrev graphPointSubgroup
    (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k) :
    Subgroup (WithConv (GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) →ₐ[k] k)) :=
  (graphSubgroup ψ).map (modGLPairPoint τ k M).toMonoidHom

theorem transportPoints_graphSubgroup
    (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k) :
    transportPoints (modGLPairPoint τ k M) (graphSubgroup ψ) = Set.range fun g : adjointGroup τ k =>
      tensorPointEquiv ((modGLPoint τ k g).ofConv, (glPointEquiv (ψ g)).ofConv) := by
  ext y
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, ⟨g, rfl⟩, rfl⟩

theorem graphSubgroup_realization [IsAlgClosed k]
    (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k)
    (hcons : IsPointConstructible k (Set.range fun g : adjointGroup τ k =>
      tensorPointEquiv ((modGLPoint τ k g).ofConv, (glPointEquiv (ψ g)).ofConv)))
    (hirr : IsPointIrreducible k (Set.range fun g : adjointGroup τ k =>
      tensorPointEquiv ((modGLPoint τ k g).ofConv, (glPointEquiv (ψ g)).ofConv))) :
    IsPointClosed k (Set.range fun g : adjointGroup τ k =>
        tensorPointEquiv ((modGLPoint τ k g).ofConv, (glPointEquiv (ψ g)).ofConv)) ∧
      IsConnectedAlgebraicSubgroup k (graphPointSubgroup ψ) ∧
      Algebra.Smooth k
        (GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) ⧸ subgroupIdeal (graphPointSubgroup ψ)) ∧
      IrreducibleSpace (PrimeSpectrum
        (GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) ⧸ subgroupIdeal (graphPointSubgroup ψ))) ∧
      ∃ e : WithConv ((GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) ⧸
          subgroupIdeal (graphPointSubgroup ψ)) →ₐ[k] k) ≃* graphSubgroup ψ, ∀ φ,
        ((e φ : graphSubgroup ψ) : ModGL τ k × Matrix.GeneralLinearGroup (Fin M) k) =
          (modGLPairPoint τ k M).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _))) := by
  rw [← transportPoints_graphSubgroup] at hcons hirr ⊢
  obtain ⟨hcl, h, he⟩ := isConnectedAlgebraicSubgroup_map (modGLPairPoint τ k M) _ hcons hirr
  obtain ⟨hsm, -, hirrsp⟩ := h.smooth
  exact ⟨hcl, h, hsm, hirrsp, he⟩

end Graph

end CFSG.LieType.AlgebraicGroups
