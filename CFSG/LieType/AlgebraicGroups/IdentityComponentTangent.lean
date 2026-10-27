module

public import CFSG.LieType.AlgebraicGroups.TangentSpace
public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang

import CFSG.LieType.AlgebraicGroups.AffinePointGeometry
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
import CFSG.LieType.AlgebraicGroups.ToralCentralizerComponent

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv

open scoped CFSG.ConvolutionPoints

section GeneralLinear

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem isPointConstructible_of_isPointClosed {A : Type} [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] {S : Set (A →ₐ[k] k)} (h : IsPointClosed k S) :
    IsPointConstructible k S := by
  obtain ⟨Zc, hZc, rfl⟩ := h
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine ⟨Zc, ?_, rfl⟩
  rw [← Topology.isConstructible_compl]
  exact (TopologicalSpace.NoetherianSpace.isCompact Zcᶜ).isConstructible hZc.isOpen_compl

theorem isConnectedAlgebraicSubgroup_closedIdentityComponent {Z : Subgroup (ModGL τ k)}
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k)))) :
    IsConnectedAlgebraicSubgroup k
      ((closedIdentityComponent Z).map (modGLPoint τ k).toMonoidHom) :=
  (isConnectedAlgebraicSubgroup_map (modGLPoint τ k) (closedIdentityComponent Z)
    (isPointConstructible_of_isPointClosed (isPointClosed_closedIdentityComponent hZ))
    (isPointIrreducible_closedIdentityComponent Z)).2.1

end GeneralLinear

end CFSG.LieType.AlgebraicGroups

end
