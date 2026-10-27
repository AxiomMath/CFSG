module

public import CFSG.LieType.AlgebraicGroups.FixedComponentNorm

public noncomputable section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem connectedSpace_of_componentPointsHom_eq_one
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (h : ∀ x : TauCeti.HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k),
      TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom H (CommAlgCat.of k k) x = 1) :
    ConnectedSpace (PrimeSpectrum H) := by
  let q := TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap H
  have hq : ∀ x, q x = 1 := fun x => (componentPointsHom_eq_one_iff H x).mp (h x)
  have hc : ∀ c : ConnectedComponents (PrimeSpectrum H), c = 1 := by
    intro c
    obtain ⟨x, rfl⟩ := TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap_surjective H c
    exact hq x
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨TauCeti.Bialgebra.augmentationPoint k H, ?_⟩
  apply Set.eq_univ_iff_forall.mpr
  intro x
  apply ConnectedComponents.coe_eq_coe'.mp
  exact (hc (ConnectedComponents.mk x)).trans
    (TauCeti.FiniteTypeCommHopfAlgCat.rationalKernelPoint_one_component H).symm

theorem componentPointsHom_comp_eq_one_of_connected
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    {A : Type u} [CommRing A] [Algebra k A]
    (f : H →ₐ[k] A) (hA : ConnectedSpace (PrimeSpectrum A))
    (p₀ : A →ₐ[k] k) (hp₀ : toConv (p₀.comp f) =
      (1 : TauCeti.HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)))
    (p : A →ₐ[k] k) :
    TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom H (CommAlgCat.of k k)
      (toConv (p.comp f)) = 1 := by
  let := hA
  apply (componentPointsHom_eq_one_iff H _).2
  rw [TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap_eq_one_iff,
    TauCeti.FiniteTypeCommHopfAlgCat.mem_identityComponentPointsSubgroup_iff]
  let z : PrimeSpectrum A := TauCeti.AlgHom.kernelPoint p
  let z₀ : PrimeSpectrum A := TauCeti.AlgHom.kernelPoint p₀
  have hp : z ∈ connectedComponent z₀ := by
    rw [PreconnectedSpace.connectedComponent_eq_univ (X := PrimeSpectrum A) z₀]
    exact Set.mem_univ _
  have h := (PrimeSpectrum.continuous_comap f.toRingHom).mapsTo_connectedComponent
    z₀ hp
  have hcomp (q : A →ₐ[k] k) :
      PrimeSpectrum.comap f.toRingHom (TauCeti.AlgHom.kernelPoint q) =
        (TauCeti.AlgHom.kernelPoint (q.comp f) : PrimeSpectrum H) :=
    TauCeti.AlgHom.comap_kernelPoint (f := q) f
  change PrimeSpectrum.comap f.toRingHom (TauCeti.AlgHom.kernelPoint p) ∈
    connectedComponent (PrimeSpectrum.comap f.toRingHom (TauCeti.AlgHom.kernelPoint p₀)) at h
  rw [hcomp p, hcomp p₀] at h
  have hbase : TauCeti.AlgHom.kernelPoint (p₀.comp f) =
      TauCeti.FiniteTypeCommHopfAlgCat.rationalKernelPoint H 1 := by
    exact congrArg (fun x : TauCeti.HopfAlgebra.points (R := k) (H := H)
      (CommAlgCat.of k k) => TauCeti.AlgHom.kernelPoint x.ofConv) hp₀
  rw [hbase] at h
  exact h

end CFSG.LieType.AlgebraicGroups
