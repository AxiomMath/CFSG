module

public import CFSG.CharacterTheory.TwoRankLowerBound.OrbitCoordinates
public import Mathlib.RepresentationTheory.Basic

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

noncomputable def orbitCoefficientEquiv {ring group points : Type*} [CommRing ring]
    [Group group] [MulAction group points] [Fintype (MulAction.orbitRel.Quotient group points)] :
    MonoidAlgebra ring points ≃ₗ[ring]
      (∀ orbit : MulAction.orbitRel.Quotient group points,
        MonoidAlgebra ring (group ⧸ MulAction.stabilizer group orbit.out)) :=
  (MonoidAlgebra.coeffLinearEquiv ring).trans
    ((Finsupp.domLCongr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer group points)).trans
      ((Finsupp.sigmaFinsuppLEquivPiFinsupp ring).trans
        (LinearEquiv.piCongrRight (fun _ => (MonoidAlgebra.coeffLinearEquiv ring).symm))))

theorem orbitCoefficientEquiv_coeff {ring group points : Type*} [CommRing ring]
    [Group group] [MulAction group points] [Fintype (MulAction.orbitRel.Quotient group points)]
    (value : MonoidAlgebra ring points) (orbit : MulAction.orbitRel.Quotient group points)
    (coset : group ⧸ MulAction.stabilizer group orbit.out) :
    ((orbitCoefficientEquiv (group := group) value) orbit).coeff coset =
      value.coeff ((MulAction.selfEquivSigmaOrbitsQuotientStabilizer group points).symm ⟨orbit, coset⟩) := by
  rfl

theorem orbitCoefficientEquiv_translation {ring group points : Type*} [CommRing ring]
    [CommGroup group] [MulAction group points] [Fintype (MulAction.orbitRel.Quotient group points)]
    (value : MonoidAlgebra ring points) (element : group) (orbit : MulAction.orbitRel.Quotient group points) :
    orbitCoefficientEquiv ((Representation.ofMulAction ring group points element) value) orbit =
      MonoidAlgebra.single (QuotientGroup.mk' (MulAction.stabilizer group orbit.out) element) 1 *
        orbitCoefficientEquiv value orbit := by
  ext coset
  rw [orbitCoefficientEquiv_coeff, Representation.coeff_ofMulAction,
    MonoidAlgebra.coeff_single_mul_apply, one_mul, orbitCoefficientEquiv_coeff]
  congr 1
  rw [← map_inv]
  exact (orbitQuotientCoordinates_inverse_equivariant orbit element⁻¹ coset).symm

end CFSG.TwoRankLowerBound.Helpers
