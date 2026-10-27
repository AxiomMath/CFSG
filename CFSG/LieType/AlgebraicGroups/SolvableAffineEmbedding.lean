module

public import CFSG.LieType.AlgebraicGroups.EquivariantAffineEmbedding
public import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic

public section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem exists_upperTriangular_coordinateEmbedding_data
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
    [Group.IsSolvable (WithConv (H →ₐ[k] k))] :
    ∃ (D : TauCeti.Subcoalgebra k H) (n : ℕ)
      (b : Module.Basis (Fin n) k D.toRegularSubcomodule)
      (f : TauCeti.GeneralLinear.UpperTriangular.coordinateHopfAlgebra k n ⟶ H.obj),
      Module.Finite k D.toSubmodule ∧
      Algebra.adjoin k (D : Set H) = ⊤ ∧
      (TauCeti.Comodule.coefficientMatrix (C := H) b).IsUpperTriangular ∧
      (∀ i, IsGroupLikeElem k (TauCeti.Comodule.coefficientMatrix (C := H) b i i)) ∧
      Function.Surjective (TauCeti.Comodule.coordinateBialgHom (H := H) b) ∧
      f.hom.comp (TauCeti.GeneralLinear.UpperTriangular.coordinateMap k n).hom =
        TauCeti.Comodule.coordinateBialgHom (H := H) b ∧
      Function.Surjective f.hom := by
  classical
  obtain ⟨D, hD, _hσD, hgen⟩ :=
    exists_finite_invariant_generating_subcoalgebra_three H (BialgHom.id k H) (by rfl)
  let : Module.Finite k D.toSubmodule := hD
  let : Module.Finite k D.toRegularSubcomodule := D.toRegularSubcomodule_finite
  let : AddCommGroup D.toRegularSubcomodule := Module.addCommMonoidToAddCommGroup k
  obtain ⟨n, b, hb_upper, hb_diag⟩ :=
    TauCeti.Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_isSolvable
      (k := k) (H := (H : Type u)) (M := D.toRegularSubcomodule)
  let fA : TauCeti.GeneralLinear.coordinateHopfAlgebra k n →ₐc[k] H :=
    TauCeti.Comodule.coordinateBialgHom (H := H) b
  have hfA_surj : Function.Surjective fA :=
    coordinateBialgHom_surjective_of_generating_subcoalgebra D hgen b
  let F : TauCeti.GeneralLinear.coordinateHopfAlgebra k n ⟶ H.obj :=
    _root_.CommHopfAlgCat.ofHom fA
  have hF_surj : Function.Surjective F.hom := hfA_surj
  have hF_upper :
      ((TauCeti.GeneralLinear.pointToGeneralLinear n (toConv fA.toAlgHom) :
        Matrix.GeneralLinearGroup (Fin n) H) : Matrix (Fin n) (Fin n) H).IsUpperTriangular := by
    intro i j hji
    rw [TauCeti.GeneralLinear.pointToGeneralLinear_apply]
    simpa only [fA, BialgHom.coe_toAlgHom, TauCeti.Comodule.coordinateBialgHom_X,
      WithConv.ofConv_toConv] using hb_upper hji
  let I : TauCeti.HopfIdeal k (TauCeti.GeneralLinear.coordinateHopfAlgebra k n) :=
    TauCeti.GeneralLinear.UpperTriangular.definingHopfIdeal k n
  have hkill : I.toIdeal ≤ RingHom.ker F.hom.toAlgHom.toRingHom :=
    TauCeti.GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal_le_ker_of_isUpperTriangular
      k n F.hom.toAlgHom (by simpa [F, fA] using hF_upper)
  let f : TauCeti.GeneralLinear.UpperTriangular.coordinateHopfAlgebra k n ⟶ H.obj :=
    TauCeti.CommHopfAlgCat.liftQuotient I F hkill
  have hsquare : f.hom.comp
      (TauCeti.GeneralLinear.UpperTriangular.coordinateMap k n).hom = fA := by
    rw [TauCeti.GeneralLinear.UpperTriangular.coordinateMap_def]
    exact congrArg (fun g : TauCeti.GeneralLinear.coordinateHopfAlgebra k n ⟶ H.obj => g.hom)
      (TauCeti.CommHopfAlgCat.mkQuotient_comp_liftQuotient I F hkill)
  have hfs : Function.Surjective f.hom :=
    TauCeti.CommHopfAlgCat.liftQuotient_surjective_of_surjective I F hkill hF_surj
  exact ⟨D, n, b, f, hD, hgen, hb_upper, hb_diag, hfA_surj, hsquare, hfs⟩


theorem exists_upperTriangular_coordinateEmbedding
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
    [Group.IsSolvable (WithConv (H →ₐ[k] k))] :
    ∃ (n : ℕ)
      (f : TauCeti.GeneralLinear.UpperTriangular.coordinateHopfAlgebra k n ⟶ H.obj),
      Function.Surjective f.hom := by
  obtain ⟨D, n, b, f, hD, hgen, hupper, hdiag, hfaithful, hsquare, hf⟩ :=
    exists_upperTriangular_coordinateEmbedding_data H
  exact ⟨n, f, hf⟩

end CFSG.LieType.AlgebraicGroups
