module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalThreeComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalNonsplitFourComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponents

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalLowDimensionFrontiers

universe u v

variable {K : Type u} [Field K] [Finite K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem orthogonal_three_p_components_frontier (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 3) :
    (∀ p : ℕ, p.Prime → ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
    (Nat.card K = 3 → Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      ∀ p : ℕ, p.Prime → ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
        ¬ CFSG.IsPComponent p L) := by
  obtain ⟨h1, h2⟩ :=
    CatalogueBOrthogonal.orthogonal_three_actual_p_component_verification hodd Q hQ hdim
  refine ⟨fun p hp L hL => ?_, fun hcard => ?_⟩
  · have : Fact p.Prime := ⟨hp⟩
    exact h1 p L hL
  · obtain ⟨hsol, hno⟩ := h2 hcard
    refine ⟨hsol, fun p hp L => ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    exact hno p L

theorem orthogonal_four_split_p_components_frontier (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 4)
    (hsplit : ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    (∀ p : ℕ, p.Prime → ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
    (Nat.card K = 3 → Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      ∀ p : ℕ, p.Prime → ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
        ¬ CFSG.IsPComponent p L) :=
  CatalogueBOrthogonalFourSplitComponents.orthogonal_four_split_actual_p_component_verification
    hodd Q hQ hdim hsplit

theorem orthogonal_four_nonsplit_p_components_frontier (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 4)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    ∀ p : ℕ, p.Prime → ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  open CatalogueBOrthogonalNonsplitFourComponents in
  exact orthogonal_four_nonsplit_actual_p_component_verification hodd Q hQ hdim hno

theorem orthogonal_five_p_components_frontier (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 5) :
    ∀ p : ℕ, p.Prime → ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  intro p hp L hL
  have : Fact p.Prime := ⟨hp⟩
  exact CatalogueBOrthogonalFive.orthogonal_five_actual_p_component_verification hodd Q hQ hdim
    p L hL

theorem orthogonal_six_nonsplit_p_components_frontier (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 6)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 3 ∧ ∀ x ∈ S, Q x = 0) :
    ∀ p : ℕ, p.Prime → ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  intro p hp L hL
  have : Fact p.Prime := ⟨hp⟩
  exact CatalogueBOrthogonalSix.orthogonal_six_nonsplit_actual_p_component_verification hodd Q
    hQ hdim hno p L hL

end CFSG.ComponentClassification.CatalogueBOrthogonalLowDimensionFrontiers
