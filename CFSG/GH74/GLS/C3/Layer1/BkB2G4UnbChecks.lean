module

public import CFSG.GH74.Filter.Statements
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUMathieuVanishing
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.SmallOddCore.HSMcL
public import CFSG.Sporadic.Schreier.LyOddCoreAll
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.SectionalRank
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk.B2G4

open CFSG CFSG.Blueprint CFSG.ComponentClassification CFSG.GH74 CFSG.GH74.Filter Subgroup
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible StatedClassicalModel StatedLieTag)

@[expose] def EvenExceptionalCheckG4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Gen4 X → IsSimpleGroup (GeneralizedFitting.subgroup X) →
    (∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) →
    ∀ (t : StatedLieTag) (f : ℕ), t ∈ chevalleyExceptionalTags →
    ChevalleyExceptionalModel (GeneralizedFitting.subgroup X) t 2 f →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    OutcomeLocal.UOutcome X

@[expose] def LargeReeTitsCheckG4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Gen4 X → IsSimpleGroup (GeneralizedFitting.subgroup X) →
    (∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) →
    ∀ (t : StatedLieTag) (f : ℕ), (t = .twistedF4 ∨ t = .Tits) →
    ReeTitsModel (GeneralizedFitting.subgroup X) t 2 f →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    OutcomeLocal.UOutcome X

@[expose] def SporadicNonJ1CheckG4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Gen4 X → IsSimpleGroup (GeneralizedFitting.subgroup X) →
    (∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) →
    NativeSporadic.SporadicRep (GeneralizedFitting.subgroup X) →
    ¬ Nonempty (GeneralizedFitting.subgroup X ≃* NativeSporadic.J1) →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    OutcomeLocal.UOutcome X

theorem evenExceptionalCheckG4_of_filter (hG2 : S_G2_even) (hF4 : S_F4_even) (hE6 : S_E6_even)
    (hE7 : S_E7_even) (hE8 : S_E8_even) (h2E6 : S_2E6_even) (h3D4 : S_3D4_even) :
    EvenExceptionalCheckG4 := by
  intro X _ _ hg _ _ t f ht hex _
  have hgF : Gen4 ↥(GeneralizedFitting.subgroup X) := Gen4.subgroup _ hg
  exfalso
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hG2 _ f hex hgF
  · exact hF4 _ f hex hgF
  · exact hE6 _ f hex hgF
  · exact hE7 _ f hex hgF
  · exact hE8 _ f hex hgF
  · exact h2E6 _ f hex hgF
  · exact h3D4 _ f hex hgF

theorem largeReeTitsCheckG4_of_filter (hF4 : S_twistedF4) (hTits : S_Tits) : LargeReeTitsCheckG4 := by
  intro X _ _ hg _ _ t f ht hm _
  have hgF : Gen4 ↥(GeneralizedFitting.subgroup X) := Gen4.subgroup _ hg
  exfalso
  rcases ht with rfl | rfl
  · exact hF4 _ f hm hgF
  · obtain ⟨-, -, -, hp2, hf1⟩ := hm.1
    subst hf1
    exact hTits _ hm hgF

theorem sporadicNonJ1CheckG4_of_out
    (hout : ∀ s ∈ sporadicOut, S_sporadic s) : SporadicNonJ1CheckG4 := by
  intro X _ _ hg hsimple hnonab hsp hJ1 hz
  obtain ⟨z, hz2, hcore⟩ := hz
  obtain ⟨s, ⟨e⟩⟩ := hsp
  have hF : CFSG.generalizedFitting X = GeneralizedFitting.subgroup X :=
    CFSG.generalizedFitting_eq_componentClassification X
  have hsimple' : IsSimpleGroup (CFSG.generalizedFitting X) := hF ▸ hsimple
  have hnonab' : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a := hF ▸ hnonab
  have hgF : Gen4 ↥(GeneralizedFitting.subgroup X) := Gen4.subgroup _ hg
  by_cases hs : s ∈ sporadicOut
  · exact absurd hgF (hout s hs _ hnonab ⟨e⟩)
  · refine absurd ?_ hcore
    have e' : CFSG.generalizedFitting X ≃* NativeSporadic.Carrier s :=
      (MulEquiv.subgroupCongr hF).trans e
    cases s
    case M11 =>
      exact CatalogueU.catalog_mathieu_almost_simple_odd_core_vanishing hsimple' hnonab'
        (.inl ⟨e'⟩) z hz2
    case M12 =>
      exact CatalogueU.catalog_mathieu_almost_simple_odd_core_vanishing hsimple' hnonab'
        (.inr (.inl ⟨e'⟩)) z hz2
    case M22 =>
      exact CatalogueU.catalog_mathieu_almost_simple_odd_core_vanishing hsimple' hnonab'
        (.inr (.inr (.inl ⟨e'⟩))) z hz2
    case M23 =>
      exact CatalogueU.catalog_mathieu_almost_simple_odd_core_vanishing hsimple' hnonab'
        (.inr (.inr (.inr (.inl ⟨e'⟩)))) z hz2
    case J1 => exact absurd ⟨e⟩ hJ1
    case J2 =>
      exact Sporadic.SmallOddCore.ctuc_j2_generalized_fitting_involution_centralizer_odd_core_trivial
        hsimple' ⟨e'⟩ z hz2
    case J3 =>
      exact Sporadic.SmallOddCore.ctuc_j3_generalized_fitting_involution_centralizer_odd_core_trivial
        hsimple' ⟨e'⟩ z hz2
    case McL =>
      exact Sporadic.SmallOddCore.ctu_catalog_hs_mcl_almost_simple_odd_core_vanishing hsimple'
        (.inr ⟨e'⟩) z hz2
    case Ly =>
      exact (Sporadic.LySchreier.full_group_all_involution_odd_core hsimple' hnonab' ⟨e'⟩).2 z hz2
    all_goals exact absurd (by decide) hs

end CFSG.GH74.GLS.C3.Layer1.Bk.B2G4
