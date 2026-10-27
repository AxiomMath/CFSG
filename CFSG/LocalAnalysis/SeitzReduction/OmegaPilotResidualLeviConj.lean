module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualHigherSp

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem higherRankCoresRigid_of_spLeviData_conj (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    {fp : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)) →* (K ≃+* K)}
    (h : ∀ s : matrixIsometries (coordinateQuadPlus n K),
      orderOf (isometryConjugationHom _ s) = 2 →
      2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank →
      ∃ s₀ a : matrixIsometries (coordinateQuadPlus n K), s = a * s₀ * a⁻¹ ∧
        SpLeviData fp (perfectCore (autFixSubgroup (isometryConjugationHom _ s₀)))) :
    HigherRankCoresRigid n K fp :=
  higherRankCoresRigid_of_coreRead spRel_unique fun s h₁ hr => by
    obtain ⟨s₀, a, rfl, hs₀⟩ := h s h₁ hr
    exact coreRead_conj (spCoreRead_of_spLeviData fp hK hq hs₀) a

end CFSG.SeitzReduction.OmegaPilot
