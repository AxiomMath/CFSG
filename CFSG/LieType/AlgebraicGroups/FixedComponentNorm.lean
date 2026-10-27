module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Representable
public import Mathlib.RingTheory.HopkinsLevitzki
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Connected
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Equalizer

public noncomputable section

open CategoryTheory WithConv
namespace CFSG.LieType.AlgebraicGroups

universe u v
variable {k : Type u} [Field k]

section Components
variable [IsAlgClosed k]

theorem componentPointsHom_map_eq_one
    (M N : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (f : M.obj ⟶ N.obj) (hN : ConnectedSpace (PrimeSpectrum N))
    (x : TauCeti.HopfAlgebra.points (R := k) (H := N) (CommAlgCat.of k k)) :
    TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom M (CommAlgCat.of k k)
      (TauCeti.AlgHom.mapDomain f.hom x) = 1 := by
  rw [TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom_apply]
  exact TauCeti.ConstantGroup.point_comp_eq_one_of_connected
    (ConnectedComponents (PrimeSpectrum M)) hN
    (f.hom.comp (TauCeti.FiniteTypeCommHopfAlgCat.componentCoordinateHom M).hom) x.ofConv

theorem componentPointsHom_eq_one_iff
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (x : TauCeti.HopfAlgebra.points (R := k) (H := M) (CommAlgCat.of k k)) :
    TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom M (CommAlgCat.of k k) x = 1 ↔
      TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap M x = 1 := by
  rw [TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom_apply,
    TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff,
    TauCeti.FiniteTypeCommHopfAlgCat.kernelHopfIdeal_componentCoordinateHom,
    TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap_eq_one_iff]

end Components

variable (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [Coalgebra.IsCocomm k H]

variable {W : Type u} [Group W] [Fintype W]
variable {A : Type u} [CommRing A] [Algebra k A]

noncomputable def finiteNormBialgHom {ι : Type v} [Fintype ι] (ρ : ι → (H →ₐc[k] H)) : H →ₐc[k] H :=
  (∏ w : ι, toConv (ρ w)).ofConv
def normThreeBialgHom (σ : H →ₐc[k] H) : H →ₐc[k] H :=
  finiteNormBialgHom H ![BialgHom.id k H, σ, σ.comp σ]

theorem normThreeBialgHom_toAlgHom (σ : H →ₐc[k] H) :
    toConv (normThreeBialgHom H σ).toAlgHom =
      toConv (AlgHom.id k H) * toConv σ.toAlgHom * toConv (σ.comp σ).toAlgHom := by
  simp only [normThreeBialgHom, finiteNormBialgHom, Fin.prod_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    BialgHom.toAlgHom_convMul, BialgHom.id_toAlgHom]
  rfl

theorem normThreeBialgHom_comp (σ : H →ₐc[k] H)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k H) :
    (normThreeBialgHom H σ).comp σ = normThreeBialgHom H σ := by
  apply BialgHom.ext
  intro x
  have h := congrArg (TauCeti.AlgHom.mapDomain (A := H) σ)
    (normThreeBialgHom_toAlgHom H σ)
  simp only [map_mul, TauCeti.AlgHom.mapDomain_apply] at h
  have hid : (AlgHom.id k H).comp σ.toAlgHom = σ.toAlgHom := AlgHom.id_comp _
  have hs : σ.toAlgHom.comp σ.toAlgHom = (σ.comp σ).toAlgHom := rfl
  have hs2 : (σ.comp σ).toAlgHom.comp σ.toAlgHom = AlgHom.id k H := by
    exact congrArg BialgHom.toAlgHom hσ
  rw [hid, hs, hs2] at h
  have hrot : toConv σ.toAlgHom * toConv (σ.comp σ).toAlgHom * toConv (AlgHom.id k H) =
      toConv (AlgHom.id k H) * toConv σ.toAlgHom * toConv (σ.comp σ).toAlgHom := by
    ac_rfl
  rw [hrot, ← normThreeBialgHom_toAlgHom H σ] at h
  exact congrArg (fun p : WithConv (H →ₐ[k] H) => p.ofConv x) h

@[expose] def fixedHopfIdeal (σ : H →ₐc[k] H) : TauCeti.HopfIdeal k H :=
  TauCeti.HopfIdeal.equalizer σ (BialgHom.id k H)

abbrev fixedCoordinate (σ : H →ₐc[k] H) : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k :=
  TauCeti.FiniteTypeCommHopfAlgCat.quotient H (fixedHopfIdeal H σ)

omit [Coalgebra.IsCocomm k H] in
theorem fixedCoordinateHom_comp (σ : H →ₐc[k] H) :
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom.comp σ =
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom := by
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom
  have hI : TauCeti.CommHopfAlgCat.equalizerHopfIdeal
      (_root_.CommHopfAlgCat.ofHom σ) (𝟙 H.obj) = fixedHopfIdeal H σ := by
    rw [TauCeti.CommHopfAlgCat.equalizerHopfIdeal_def]
    rfl
  have h := TauCeti.CommHopfAlgCat.comp_mkQuotient_equalizerHopfIdeal
    (_root_.CommHopfAlgCat.ofHom σ) (𝟙 H.obj)
  rw [hI] at h
  have h' := congrArg (fun f => f.hom) h
  change q.comp σ = q.comp (BialgHom.id k H) at h'
  simpa only [BialgHom.comp_id] using h'

theorem normThreeBialgHom_on_points (σ : H →ₐc[k] H)
    (x : TauCeti.HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    TauCeti.AlgHom.mapDomain (normThreeBialgHom H σ) x =
      x * TauCeti.AlgHom.mapDomain σ x * TauCeti.AlgHom.mapDomain (σ.comp σ) x := by
  have h := congrArg (TauCeti.AlgHom.mapValue x.ofConv) (normThreeBialgHom_toAlgHom H σ)
  simpa only [map_mul, TauCeti.AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_id,
    TauCeti.AlgHom.mapDomain_apply] using h

omit [Coalgebra.IsCocomm k H] in
theorem fixedCoordinate_point_fixed (σ : H →ₐc[k] H)
    (x : TauCeti.HopfAlgebra.points (R := k) (H := fixedCoordinate H σ) (CommAlgCat.of k k)) :
    TauCeti.AlgHom.mapDomain σ
      (TauCeti.AlgHom.mapDomain
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom x) =
      TauCeti.AlgHom.mapDomain
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom x := by
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H (fixedHopfIdeal H σ)).hom.hom
  have he : q.comp σ = q := fixedCoordinateHom_comp H σ
  change (TauCeti.AlgHom.mapDomain σ) ((TauCeti.AlgHom.mapDomain q) x) =
    (TauCeti.AlgHom.mapDomain q) x
  rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, he]

variable [IsAlgClosed k]

end CFSG.LieType.AlgebraicGroups
