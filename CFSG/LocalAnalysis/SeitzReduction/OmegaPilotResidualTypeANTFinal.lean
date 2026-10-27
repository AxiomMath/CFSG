module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeANTMain

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

theorem typeA_nSubTwo_input :
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
      (hn : 5 ≤ n), Even f →
      ∀ s : matrixIsometries (coordinateQuadPlus n K), s * s = 1 →
        (∀ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w = 0) →
        finrank K (LinearMap.range (sNil s.val)) + 2 = n →
        ∃ s₀ a : matrixIsometries (coordinateQuadPlus n K), s = a * s₀ * a⁻¹ ∧
          SpLeviData (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)
            (perfectCore (autFixSubgroup (isometryConjugationHom _ s₀))) :=
  fun _ _ _ _ _ _ hK hn hfe s hss hA hℓ =>
    exists_conj_spLeviData_typeA_nSubTwo _ hK hn (four_le_card_of_even hK hfe) s hss hA hℓ

end CFSG.SeitzReduction.OmegaPilot
