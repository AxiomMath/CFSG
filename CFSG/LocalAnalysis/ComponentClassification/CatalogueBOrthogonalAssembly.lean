module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalAssemblyCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalAssembly

universe u v

variable {K : Type u} [Field K] [Finite K]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem orthogonal_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (_hdim : 3 ≤ Module.finrank K V) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  rcases pComponent_quasisimple_or_nonsplit_six hodd Q hQ p L hL with hquasi | ⟨hdim6, hno⟩
  · exact hquasi
  · exact CatalogueBOrthogonalSix.orthogonal_six_nonsplit_actual_p_component_verification
      hodd Q hQ hdim6 hno p L hL

theorem odd_orthogonal_p_components_assembly (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 3 ≤ Module.finrank K V) :
    ∀ p : ℕ, p.Prime → ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  intro p hp L hL
  let : Fact p.Prime := ⟨hp⟩
  exact orthogonal_pComponent_quasisimple hodd Q hQ hdim p L hL

end CFSG.ComponentClassification.CatalogueBOrthogonalAssembly

