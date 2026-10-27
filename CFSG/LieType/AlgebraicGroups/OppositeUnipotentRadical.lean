module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
public import TauCeti.Algebra.AlgebraicGroup.Borel.Radical
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Semisimple
public import TauCeti.RingTheory.Smooth.GeometricallyReduced
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange

public noncomputable section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem unipotentRadicalDefiningIdeal_eq_augmentation_of_borels
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (Bpos Bneg : TauCeti.HopfIdeal k H)
    (hBpos : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H Bpos)
    (hBneg : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H Bneg)
    (hss : ∀ x : TauCeti.HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k),
      x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj Bpos (CommAlgCat.of k k) →
      x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj Bneg (CommAlgCat.of k k) →
      TauCeti.HopfAlgebra.IsSemisimplePoint x) :
    TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H =
      TauCeti.HopfIdeal.augmentation k H := by
  let I := TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H I
  have hU : TauCeti.smoothUnipotentCommHopfAlgProperty k Q :=
    (TauCeti.FiniteTypeCommHopfAlgCat.isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H).smoothUnipotent
  have hsm : Algebra.Smooth k Q := (TauCeti.smoothUnipotentCommHopfAlgProperty_iff k Q).mp hU |>.1
  let := hsm
  let : IsReduced Q := TauCeti.isReduced_of_smooth k Q
  apply le_antisymm
  · exact I.le_augmentation
  · apply TauCeti.HopfIdeal.le_of_quotientPointsSubgroup_le (K := k)
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    have hy : TauCeti.HopfAlgebra.IsUnipotentPoint y :=
      ((TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty_iff k Q.obj).mpr
        ((TauCeti.smoothUnipotentCommHopfAlgProperty_iff k Q).mp hU).2).forall_isUnipotentPoint y
    let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom
    have hxU : TauCeti.HopfAlgebra.IsUnipotentPoint (TauCeti.AlgHom.mapDomain q y) :=
      hy.mapDomain q
    have hxI : TauCeti.AlgHom.mapDomain q y ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) :=
      ⟨y, rfl⟩
    have hxpos := TauCeti.CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj
      hBpos.le_unipotentRadicalDefiningIdeal (CommAlgCat.of k k) hxI
    have hxneg := TauCeti.CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj
      hBneg.le_unipotentRadicalDefiningIdeal (CommAlgCat.of k k) hxI
    exact (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_augmentation_iff H.obj _ _).2
      ((hss _ hxpos hxneg).eq_one_of_isUnipotent hxU)

theorem reductive_of_unipotentRadical_eq_augmentation
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hsm : Algebra.Smooth k H) (hconn : ConnectedSpace (PrimeSpectrum H))
    (hrad : TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H =
      TauCeti.HopfIdeal.augmentation k H) :
    TauCeti.reductiveCommHopfAlgProperty k H := by
  let e : k ≃ₐ[k] AlgebraicClosure k :=
    AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  let : Algebra (AlgebraicClosure k) k := e.symm.toRingHom.toAlgebra
  let : IsScalarTower k (AlgebraicClosure k) k :=
    IsScalarTower.of_algebraMap_eq fun x => (e.symm.commutes x).symm
  let Hbar := TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
  let Hback := TauCeti.FiniteTypeCommHopfAlgCat.baseChange (K := k) Hbar
  let j : Hback ≅ H := ObjectProperty.isoMk _
    (TauCeti.CommHopfAlgCat.baseChangeTowerIso k k H.obj ≪≫
      _root_.CommHopfAlgCat.isoMk (_root_.Bialgebra.TensorProduct.lid k H.obj))
  have hback : TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal Hback =
      TauCeti.HopfIdeal.augmentation k Hback := by
    rw [← TauCeti.FiniteTypeCommHopfAlgCat.comapOfSurjective_unipotentRadicalDefiningIdeal j,
      hrad, TauCeti.HopfIdeal.comapOfSurjective_augmentation]
  have hbar : TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal Hbar =
      TauCeti.HopfIdeal.augmentation (AlgebraicClosure k) Hbar :=
    TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_of_baseChange_eq_augmentation
      (K := k) hback
  rw [TauCeti.reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation]
  exact ⟨hsm, (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k H.obj).mpr hconn,
    hbar⟩

theorem reductive_of_borels
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hsm : Algebra.Smooth k H) (hconn : ConnectedSpace (PrimeSpectrum H))
    (Bpos Bneg : TauCeti.HopfIdeal k H)
    (hBpos : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H Bpos)
    (hBneg : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H Bneg)
    (hss : ∀ x : TauCeti.HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k),
      x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj Bpos (CommAlgCat.of k k) →
      x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj Bneg (CommAlgCat.of k k) →
      TauCeti.HopfAlgebra.IsSemisimplePoint x) :
    TauCeti.reductiveCommHopfAlgProperty k H := by
  exact reductive_of_unipotentRadical_eq_augmentation H hsm hconn
    (unipotentRadicalDefiningIdeal_eq_augmentation_of_borels H Bpos Bneg hBpos hBneg hss)

end CFSG.LieType.AlgebraicGroups
