module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverage
public import CFSG.LocalAnalysis.ComponentInitial.QuadraticLowDimension
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitComponents
public import CFSG.GroupTheory.LocalCores.Layer

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ComponentClassification

theorem not_isComponent_of_isSolvable {G : Type*} [Group G] [Group.IsSolvable G]
    (L : Subgroup G) : ¬ CFSG.IsComponent L := by
  intro hL
  have := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  have := hL.1.1
  exact Group.IsPerfect.not_isSolvable L
    (Group.isSolvable_of_isSolvable_injective L.subtype_injective)

theorem isComponent_of_le_of_normal {G : Type*} [Group G] {L N : Subgroup G} [N.Normal]
    (hq : CFSG.IsQuasisimple L) (hLN : L ≤ N) (hn : (L.subgroupOf N).Normal) :
    CFSG.IsComponent L :=
  ⟨hq, Subgroup.IsSubnormal.step L N hLN (Subgroup.Normal.isSubnormal inferInstance) hn⟩

variable {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem odd_quadratic_isometry_empty_layer (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate)
    (hd : 4 ≤ Module.finrank K W) :
    (CFSG.layer (TauCeti.QuadraticMap.orthogonalGroup Q) = ⊥ ↔
      Module.finrank K W = 4 ∧ Nat.card K = 3 ∧
        ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) ∧
    ((Module.finrank K W = 4 ∧ Nat.card K = 3 ∧
        ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) →
      Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
    (¬ (Module.finrank K W = 4 ∧ Nat.card K = 3 ∧
        ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) →
      ∃ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q), CFSG.IsComponent L) := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hsolv : (Module.finrank K W = 4 ∧ Nat.card K = 3 ∧
      ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) →
      Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rintro ⟨hd4, hK, S, hSdim, hS⟩
    exact CatalogueBOrthogonalFourSplitComponents.orthogonal_four_split_three_solvable hK Q hQ
      hd4 S hSdim hS
  have hcomp : ¬ (Module.finrank K W = 4 ∧ Nat.card K = 3 ∧
      ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) →
      ∃ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q), CFSG.IsComponent L := by
    intro hne
    by_cases hT : ∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
    · obtain ⟨T, hTdim, hTQ⟩ := hT
      exact ⟨_, CatalogueBOrthogonal.derived_quasisimple Q h2 hQ hTdim.ge hTQ,
        (Subgroup.Normal.isSubnormal inferInstance)⟩
    · have h6 := (finite_odd_quadratic_low_Witt_dimension_bound hodd Q hQ).2.2 hT
      have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
      have hcase : (Odd (Nat.card K) ∧ (Module.finrank K W = 3 ∨ Module.finrank K W = 4 ∨
          Module.finrank K W = 5)) ∨
          (Odd (Nat.card K) ∧ Module.finrank K W = 6 ∧
            ¬ ∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) ∨
          (Module.finrank K W = 4 ∧
            ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) := by
        rcases (show Module.finrank K W = 4 ∨ Module.finrank K W = 5 ∨
            Module.finrank K W = 6 by omega) with h | h | h
        · exact Or.inl ⟨hodd, Or.inr (Or.inl h)⟩
        · exact Or.inl ⟨hodd, Or.inr (Or.inr h)⟩
        · exact Or.inr (Or.inl ⟨hodd, h, hT⟩)
      have hnexc : ¬ ((Module.finrank K W = 3 ∧ Nat.card K = 3) ∨
          ((Module.finrank K W = 4 ∧
            ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) ∧
            (Nat.card K = 2 ∨ Nat.card K = 3))) := by
        rintro (⟨h3, -⟩ | ⟨⟨hd4, hS⟩, hK | hK⟩)
        · omega
        · exact hK2 hK
        · exact hne ⟨hd4, hK, hS⟩
      obtain ⟨-, -, ⟨n, L, hn1, -, -, hL, -⟩, -⟩ :=
        (orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ hcase).2.1 hnexc
      obtain ⟨hq, hle, hnorm⟩ := hL ⟨0, by omega⟩
      exact ⟨L ⟨0, by omega⟩, isComponent_of_le_of_normal hq hle hnorm⟩
  refine ⟨⟨fun hE => ?_, fun hexc => ?_⟩, hsolv, hcomp⟩
  · by_contra hne
    obtain ⟨L, hL⟩ := hcomp hne
    have hle := CFSG.LocalCores.component_le_layer hL
    rw [hE, le_bot_iff] at hle
    exact (Subgroup.nontrivial_iff_ne_bot L).mp (CFSG.LocalCores.isQuasisimple_nontrivial hL.1)
      hle
  · have := hsolv hexc
    exact CFSG.LocalCores.layer_eq_bot_of_forall not_isComponent_of_isSolvable

end CFSG.LocalAnalysis.ComponentInitial
