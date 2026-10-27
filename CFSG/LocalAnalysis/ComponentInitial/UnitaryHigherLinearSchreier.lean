module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Assembly.LowTwoRank

theorem linear_higher_schreier {K : Type*} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) :
    derivedSeries (Outer (LinearFlag.projectiveSL n K)) 3 = ⊥ ∧
      Group.IsSolvable (Outer (LinearFlag.projectiveSL n K)) := by
  have hR := (LinearFlag.automorphism_generation (K := K) hn).1
  obtain ⟨-, -, -, -, -, -, -, -, -, h3⟩ := LinearFlag.standard_outer_quotients (n := n) (K := K)
  rw [hR] at h3
  have hD : derivedSeries (MulAut (LinearFlag.projectiveSL n K)) 3 ≤
      inner (LinearFlag.projectiveSL n K) := by
    simp only [derivedSeries_succ, derivedSeries_zero]
    exact h3
  have h2 : derivedSeries (Outer (LinearFlag.projectiveSL n K)) 3 = ⊥ := by
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (inner _)), eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x).mpr (hD hx)
  exact ⟨h2, (Group.isSolvable_def _).mpr ⟨3, h2⟩⟩

theorem linear_two_classical_model_schreier {S : Type} [Group S] {p f : ℕ}
    (hS : StatedClassicalModel S .PSL 2 p f) :
    derivedSeries (Outer S) 2 = ⊥ ∧ Group.IsSolvable (Outer S) := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hS
  obtain ⟨⟨E, -⟩, -⟩ := outer_isomorphism (e.trans
    ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.projectiveQuotientEquivPSL K).symm))
  have hP :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.projectiveOuter_secondDerived_eq_bot K
  have h2 : derivedSeries (Outer S) 2 = ⊥ := by
    rw [← map_derivedSeries_eq (f := E.symm.toMonoidHom) E.symm.surjective]
    exact (congrArg (Subgroup.map E.symm.toMonoidHom) hP).trans (Subgroup.map_bot _)
  exact ⟨h2, (Group.isSolvable_def _).mpr ⟨2, h2⟩⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
