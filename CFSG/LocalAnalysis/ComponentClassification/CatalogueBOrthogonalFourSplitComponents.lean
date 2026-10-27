module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitComponentsDeterminant

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourSplitComponents

open CatalogueBOrthogonalFourSplit

universe u v

variable {K : Type u} [Field K] [Finite K]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem splitFour_orthogonal_finite (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 4)
    (S : Submodule K V) (hSdim : Module.finrank K S = 2) (hS : ∀ x ∈ S, Q x = 0) :
    Finite (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  obtain ⟨_, e, _, _, _⟩ := split_four_determinant_form_isometry Q hQ hdim S hSdim hS
  exact Finite.of_injective e e.injective

theorem orthogonal_four_split_pComponent_quasisimple (_hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 4) (S : Submodule K V)
    (hSdim : Module.finrank K S = 2) (hS : ∀ x ∈ S, Q x = 0)
    (p : ℕ) [Fact p.Prime]
    (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  obtain ⟨_, e, _, _, _⟩ := split_four_determinant_form_isometry Q hQ hdim S hSdim hS
  have hmap := CatalogueBAlternating.pComponent_map_equiv p e L hL
  have hquasi := determinant_pComponent_quasisimple p (L.map e.toMonoidHom) hmap
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv (L.equivMapOfInjective e.toMonoidHom e.injective)
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))

theorem orthogonal_four_split_three_solvable (hcard : Nat.card K = 3)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 4) (S : Submodule K V)
    (hSdim : Module.finrank K S = 2) (hS : ∀ x ∈ S, Q x = 0) :
    Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  obtain ⟨_, e, _, _, _⟩ := split_four_determinant_form_isometry Q hQ hdim S hSdim hS
  let : Group.IsSolvable (DeterminantIsometries K) := determinant_three_solvable hcard
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem orthogonal_four_split_three_no_pComponent (hcard : Nat.card K = 3)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 4) (S : Submodule K V)
    (hSdim : Module.finrank K S = 2) (hS : ∀ x ∈ S, Q x = 0)
    (p : ℕ) (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    ¬ CFSG.IsPComponent p L := by
  let : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    orthogonal_four_split_three_solvable hcard Q hQ hdim S hSdim hS
  exact CatalogueBGeneralLinear.no_pComponent_of_solvable p L

theorem orthogonal_four_split_actual_p_component_verification (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 4)
    (hsplit : ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    (∀ (p : ℕ), p.Prime →
      ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
      (Nat.card K = 3 → Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) ∧
        ∀ (p : ℕ), p.Prime →
          ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q), ¬ CFSG.IsPComponent p L) := by
  obtain ⟨S, hSdim, hS⟩ := hsplit
  constructor
  · intro p hp L hL
    let : Fact p.Prime := ⟨hp⟩
    exact orthogonal_four_split_pComponent_quasisimple hodd Q hQ hdim S hSdim hS p L hL
  · intro hcard
    exact ⟨orthogonal_four_split_three_solvable hcard Q hQ hdim S hSdim hS,
      fun p _ L => orthogonal_four_split_three_no_pComponent hcard Q hQ hdim S hSdim hS p L⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalFourSplitComponents
