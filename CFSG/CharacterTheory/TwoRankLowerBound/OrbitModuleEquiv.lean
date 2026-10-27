module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuotientOrbitScalarTrace
public import CFSG.CharacterTheory.TwoRankLowerBound.OrbitCoefficientEquiv

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

noncomputable def orbitPermutationModuleEquiv {ring group points : Type*} [CommRing ring]
    [CommGroup group] [MulAction group points] [Fintype (MulAction.orbitRel.Quotient group points)] :
    letI : ∀ orbit : MulAction.orbitRel.Quotient group points,
        Module (MonoidAlgebra ring group) (MonoidAlgebra ring (group ⧸ MulAction.stabilizer group orbit.out)) :=
      fun orbit => Module.compHom (MonoidAlgebra ring (group ⧸ MulAction.stabilizer group orbit.out))
        (MonoidAlgebra.mapDomainRingHom ring (QuotientGroup.mk' (MulAction.stabilizer group orbit.out)))
    letI : ∀ orbit : MulAction.orbitRel.Quotient group points,
        IsScalarTower ring (MonoidAlgebra ring group)
          (MonoidAlgebra ring (group ⧸ MulAction.stabilizer group orbit.out)) :=
      fun orbit => groupAlgebra_quotient_scalarTower (QuotientGroup.mk' (MulAction.stabilizer group orbit.out))
    (Representation.ofMulAction ring group points).asModule ≃ₗ[MonoidAlgebra ring group]
      (∀ orbit : MulAction.orbitRel.Quotient group points,
        MonoidAlgebra ring (group ⧸ MulAction.stabilizer group orbit.out)) := by
  let : ∀ orbit : MulAction.orbitRel.Quotient group points,
      Module (MonoidAlgebra ring group) (MonoidAlgebra ring (group ⧸ MulAction.stabilizer group orbit.out)) :=
    fun orbit => Module.compHom (MonoidAlgebra ring (group ⧸ MulAction.stabilizer group orbit.out))
      (MonoidAlgebra.mapDomainRingHom ring (QuotientGroup.mk' (MulAction.stabilizer group orbit.out)))
  let : ∀ orbit : MulAction.orbitRel.Quotient group points,
      IsScalarTower ring (MonoidAlgebra ring group)
        (MonoidAlgebra ring (group ⧸ MulAction.stabilizer group orbit.out)) :=
    fun orbit => groupAlgebra_quotient_scalarTower (QuotientGroup.mk' (MulAction.stabilizer group orbit.out))
  let equivalence := (Representation.ofMulAction ring group points).asModuleEquiv.trans
    (orbitCoefficientEquiv (ring := ring) (group := group) (points := points))
  have hcommute : ∀ (element : group)
      (value : (Representation.ofMulAction ring group points).asModule),
      equivalence ((MonoidAlgebra.single element 1 : MonoidAlgebra ring group) • value) =
        (MonoidAlgebra.single element 1 : MonoidAlgebra ring group) • equivalence value := by
    intro element value
    funext orbit
    change orbitCoefficientEquiv
      ((Representation.ofMulAction ring group points).asModuleEquiv
        (MonoidAlgebra.single element 1 • value)) orbit = _
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one,
      orbitCoefficientEquiv_translation]
    change _ = MonoidAlgebra.mapDomainRingHom ring
      (QuotientGroup.mk' (MulAction.stabilizer group orbit.out))
      (MonoidAlgebra.single element 1) * _
    simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
    rfl
  exact LinearEquiv.ofBijective (MonoidAlgebra.equivariantOfLinearOfComm equivalence.toLinearMap hcommute)
    equivalence.bijective

end CFSG.TwoRankLowerBound.Helpers
