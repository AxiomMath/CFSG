module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalThreeComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalNonsplitFourComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalAssembly

universe u v

variable {K : Type u} [Field K] [Finite K]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem orthogonal_four_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 4) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  by_cases hsplit : ∃ S : Submodule K V,
      Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
  · obtain ⟨S, hSdim, hS⟩ := hsplit
    exact CatalogueBOrthogonalFourSplitComponents.orthogonal_four_split_pComponent_quasisimple
      hodd Q hQ hdim S hSdim hS p L hL
  · exact CatalogueBOrthogonalNonsplitFourComponents.orthogonal_four_nonsplit_pComponent_quasisimple
      hodd Q hQ hdim hsplit p L hL

theorem orthogonal_small_solvable_no_pComponents (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V ≤ 2) :
    Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      ∀ (p : ℕ) (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)),
        ¬ CFSG.IsPComponent p L := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  exact ⟨CatalogueBOrthogonal.orthogonal_small_solvable Q h2 hQ hdim,
    CatalogueBOrthogonal.orthogonal_small_no_pComponent Q h2 hQ hdim⟩

theorem three_le_finrank_of_pComponent (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (p : ℕ) (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hL : CFSG.IsPComponent p L) : 3 ≤ Module.finrank K V := by
  by_contra hdim
  exact (orthogonal_small_solvable_no_pComponents hodd Q hQ (by omega)).2 p L hL

theorem orthogonal_le_five_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V ≤ 5) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have hthree := three_le_finrank_of_pComponent hodd Q hQ p L hL
  by_cases hdim3 : Module.finrank K V = 3
  · exact CatalogueBOrthogonal.orthogonal_three_pComponent_quasisimple
      hodd Q hQ hdim3 p L hL
  by_cases hdim4 : Module.finrank K V = 4
  · exact orthogonal_four_pComponent_quasisimple hodd Q hQ hdim4 p L hL
  exact CatalogueBOrthogonalFive.orthogonal_five_actual_p_component_verification
    hodd Q hQ (by omega) p L hL

theorem low_Witt_finrank_cases (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 3 ≤ Module.finrank K V)
    (hno : ¬ ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    Module.finrank K V = 3 ∨ Module.finrank K V = 4 ∨
      Module.finrank K V = 5 ∨ Module.finrank K V = 6 := by
  have hbound := CatalogueBOddQuadratic.finrank_le_six_of_no_totallySingular_three
    hodd Q hQ hno
  omega

theorem pComponent_quasisimple_or_nonsplit_six (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (p : ℕ) [Fact p.Prime] (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L ∨
      (Module.finrank K V = 6 ∧
        ¬ ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) := by
  by_cases hsingular : ∃ T : Submodule K V,
      Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  · obtain ⟨T, hTdim, hT⟩ := hsingular
    exact Or.inl ((CatalogueBOrthogonal.high_Witt_orthogonal_p_components Q
      (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd) hQ (by omega) hT).2
      p (Fact.out : p.Prime) L hL).2
  · by_cases hdim6 : Module.finrank K V = 6
    · exact Or.inr ⟨hdim6, hsingular⟩
    · have hbound := CatalogueBOddQuadratic.finrank_le_six_of_no_totallySingular_three
        hodd Q hQ hsingular
      exact Or.inl (orthogonal_le_five_pComponent_quasisimple hodd Q hQ (by omega) p L hL)

end CFSG.ComponentClassification.CatalogueBOrthogonalAssembly
