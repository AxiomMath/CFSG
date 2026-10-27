module

public import CFSG.GH74.SectionalRank
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingInclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieFrontier
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced
public import CFSG.LocalAnalysis.ComponentClassification.ProperSectionBReduction

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk.B2G4

open CFSG CFSG.Blueprint CFSG.ComponentClassification CFSG.ComponentClassification.ProperSectionB
  CFSG.GH74 Subgroup
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def SchreierG4 : Prop :=
  SchreierFor (fun X : Type => Blueprint.Catalog X ∧ Gen4 X)

@[expose] def UnbalancedG4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Gen4 X → IsSimpleGroup (GeneralizedFitting.subgroup X) →
    (∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) →
    Blueprint.Catalog (GeneralizedFitting.subgroup X) →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    OutcomeLocal.UOutcome X

@[expose] def ExceptionalG4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Gen4 G → IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    (GeneralizedFitting.subgroup G).index ≤ 2 →
    (LieModel (GeneralizedFitting.subgroup G) .PSL 3 2 2 ∨
      Nonempty (GeneralizedFitting.subgroup G ≃* NativeSporadic.He)) →
    (∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) →
    CentralTwoBInclusion.Property G

theorem kGroup_B_inclusion_g4
    (hS : SchreierG4) (hU : UnbalancedG4) (hE : ExceptionalG4) :
    ∀ (Y : Type) [Group Y] [Finite Y], Gen4 Y → SectionRank.IsKGroupCat Y →
      CentralTwoBInclusion.Property Y := by
  have hC : ∀ {X Z : Type} [Group X] [Group Z], X ≃* Z → (Blueprint.Catalog Z ∧ Gen4 Z) →
      (Blueprint.Catalog X ∧ Gen4 X) := fun e h =>
    ⟨SectionRank.catalog_of_mulEquiv e h.1, Gen4.of_mulEquiv e.symm h.2⟩
  suffices h : ∀ n : ℕ, ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n → Gen4 Y →
      SectionRank.IsKGroupCat Y → CentralTwoBInclusion.Property Y from
    fun Y _ _ hg hY => h _ Y rfl hg hY
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y _ _ hn hg hY
    have hsub : ∀ X : Subgroup Y, X ≠ ⊤ → CentralTwoBInclusion.Property X := by
      intro X hX
      have hlt : Nat.card X < Nat.card Y := by
        simpa only [Subgroup.card_top] using Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hX)
      exact ih _ (hn ▸ hlt) X rfl (Gen4.subgroup X hg) (hY.subgroup X)
    have hquot : ∀ (N : Subgroup Y) (_ : N.Normal), N ≠ ⊥ →
        CentralTwoBInclusion.Property (Y ⧸ N) := by
      intro N _ hN
      exact ih _ (hn ▸ MinimalBCenter.quotient_card_lt N hN) (Y ⧸ N) rfl (Gen4.quotient N hg)
        (hY.quotient N)
    have hK : CFSG.Assembly.KProper (fun X : Type => Blueprint.Catalog X ∧ Gen4 X) Y := by
      intro K L _ _ _ hsimple _
      exact ⟨hY K (L.subgroupOf K) hsimple, Gen4.quotient _ (Gen4.subgroup K hg)⟩
    by_contra hfail
    obtain ⟨S, hS1, hS2, hSfail⟩ : ∃ S : Subgroup Y, S ≠ ⊥ ∧ IsPGroup 2 S ∧
        ¬ (TwoComponents.badSubgroup (normalizer (S : Set Y))).map
          (normalizer (S : Set Y)).subtype ≤ TwoComponents.badSubgroup Y := by
      by_contra hnone
      push Not at hnone
      exact hfail fun S hS1 hS2 => hnone S hS1 hS2
    obtain ⟨-, -, -, ⟨z, hz, hzS, hzc, -⟩, hlocal⟩ :=
      proper_section_B_failure_simple_unbalanced_reduction_of_schreier hC hS hK hsub hquot hS1 hS2
        hSfail
    obtain ⟨-, -, ⟨L, hL, hLq, hLB⟩, hall, hcore⟩ := hlocal z hz hzS hzc
    obtain ⟨-, -, hDF, hsimple, hnab, -, hindex⟩ := hall L hL hLq hLB _ rfl
    rw [CFSG.generalizedFitting_eq_componentClassification] at hDF
    rw [hDF] at hsimple hnab hindex
    have : IsSimpleGroup (GeneralizedFitting.subgroup Y) := hsimple
    have hcat : Blueprint.Catalog (GeneralizedFitting.subgroup Y) :=
      SectionRank.catalog_of_isKGroupCat_of_surjective hY _ (MonoidHom.id _)
        Function.surjective_id
    rcases hU Y hg hsimple hnab hcat ⟨z, hz, hcore⟩ with hlie | ⟨m, -, hm, ⟨θ⟩, -⟩ | ⟨hexc, -⟩
    · exact hfail
        (CatalogueBOddLie.odd_Lie_index_two_B_under_proper_subgroup_B hnab hindex hlie hsub)
    · exact hfail (CatalogueBAlternating.generalizedFitting_B_inclusion hnab (Or.inr hm) θ)
    · exact hfail (hE Y hg hsimple hnab hindex hexc hsub)

end CFSG.GH74.GLS.C3.Layer1.Bk.B2G4
