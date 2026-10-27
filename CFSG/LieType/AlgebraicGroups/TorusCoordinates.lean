module

public import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Semisimple

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CategoryTheory TauCeti

universe u

theorem exists_coordinateEquiv_of_torus
    {k : Type u} [Field k] [IsAlgClosed k]
    (T : FiniteTypeCommHopfAlgCat.{u,u} k) (hT : torusCommHopfAlgProperty k T) :
    ∃ r : ℕ, Nonempty (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ)) ≃ₐc[k] T) := by
  obtain ⟨r, ⟨i⟩⟩ := (splitTorusCommHopfAlgProperty_iff k T).mp (hT.split k T)
  let A := DiagonalizableGroup.coordinateRing k (SplitTorus.characterGroup (ULift.{u} (Fin r)))
  let e : A ≃ₐc[k] T := CommHopfAlgCat.ofIso
    ((forget₂ (FiniteTypeCommHopfAlgCat k) (CommHopfAlgCat k)).mapIso i)
  let eULift : Multiplicative (Fin r →₀ ℤ) ≃* Multiplicative (ULift.{u} (Fin r) →₀ ℤ) :=
    AddEquiv.toMultiplicative (Finsupp.domCongr Equiv.ulift.symm)
  exact ⟨r, ⟨(MonoidAlgebra.domCongrBialgEquiv k k eULift).trans e⟩⟩

theorem isSemisimplePoint_of_torus
    {k : Type u} [Field k] [IsAlgClosed k]
    (T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (hT : TauCeti.torusCommHopfAlgProperty k T)
    (t : WithConv (T →ₐ[k] k)) : TauCeti.HopfAlgebra.IsSemisimplePoint t := by
  obtain ⟨r, ⟨e⟩⟩ := exists_coordinateEquiv_of_torus T hT
  let E := AlgHom.mapDomainMulEquiv (A := k) e
  have hs := (TauCeti.DiagonalizableGroup.isSemisimplePoint (E t)).mapDomain e.symm.toBialgHom
  change TauCeti.HopfAlgebra.IsSemisimplePoint (E.symm (E t)) at hs
  rwa [MulEquiv.symm_apply_apply] at hs


end CFSG.LieType.AlgebraicGroups
