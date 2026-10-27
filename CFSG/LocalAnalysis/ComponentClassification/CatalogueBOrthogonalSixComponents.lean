module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructureQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixSimilarity
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsDomain
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsImage

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open QuadraticMap

universe u v

variable {K : Type u} [Field K] [Finite K]

theorem six_full_isometry_pComponent_quasisimple (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (SixIsometries delta)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L :=
  CatalogueBFixedCentralQuotient.pComponent_quasisimple_of_normal_solvable_quotient
    p (sixSpecialImage delta h2)
    (fun J hJ => sixSpecialKappa_range_pComponent_quasisimple delta h2 p J hJ) L hL

variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem orthogonal_six_nonsplit_actual_p_component_verification
    (hodd : Odd (Nat.card K)) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 6)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 3 ∧ ∀ x ∈ S, Q x = 0)
    (p : ℕ) [Fact p.Prime]
    (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  obtain ⟨delta, hns, _, _, e, _, _, _⟩ :=
    CatalogueBOrthogonalSixSimilarity.exists_six_similarity_and_orthogonal_equiv
      hodd Q hQ hdim hno
  let : Fact (¬ IsSquare (delta : K)) := ⟨hns⟩
  have hmap := CatalogueBAlternating.pComponent_map_equiv p e L hL
  have hquasi := six_full_isometry_pComponent_quasisimple (delta : K)
    (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd) p (L.map e.toMonoidHom) hmap
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv (L.equivMapOfInjective e.toMonoidHom e.injective)
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
