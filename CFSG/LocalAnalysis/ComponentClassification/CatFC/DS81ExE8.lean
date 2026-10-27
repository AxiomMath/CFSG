module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTransport

public section

namespace CFSG.ComponentClassification.CatFC.DS81.Ex

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.SeitzReduction
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.RankTwoExceptional.E8
  CFSG.ComponentClassification.RankTwoExceptional.Exc

set_option linter.unusedSectionVars false


theorem e8_exists_order_eightynine_commute {K : Type} [Field K] [Finite K] [CharP K 2]
    {ε : Kˣ} (hε : orderOf ε = 89) :
    ∀ y ∈ e8Reps K, ∃ z : adjointGroup .E8 K, orderOf z = 89 ∧ Commute z y := by
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  have h2 : ringChar K = 2 := ringChar.eq K 2
  have key : ∀ F : List (Fin Tag.E8.rank → ℤ),
      (∀ σ ∈ F, σ ∈ e8FrameX ++ e8FrameY ++ e8FrameZ ++ e8FrameU) →
        ∃ z : adjointGroup .E8 K, orderOf z = 89 ∧ Commute z (e8FramePt K F) := by
    intro F hF
    refine ⟨⟨rootDiagUnit .E8 fun i => ε ^ (Pi.single e8Top (1 : ℤ) : Fin Tag.E8.rank → ℤ) i,
      rootDiagUnit_mem_adjointGroup_of_charTwo (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) h2 _⟩,
      ?_, ?_⟩
    · rw [Subgroup.orderOf_mk]
      exact orderOf_rootDiagUnit_eq_prime hε (Pi.single e8Top (1 : ℤ)) e8Top (by norm_num)
    · have hroot : ∀ β ∈ F, IsRoot .E8 β := fun β hβ => (isRoot_of_mem_e8Frames β (hF β hβ)).1
      have h0 : ∀ β ∈ F, β e8Top = 0 := fun β hβ => (isRoot_of_mem_e8Frames β (hF β hβ)).2.1
      exact Subtype.ext (commute_rootDiagUnit_single_framePt e8Top F hroot h0 ε).eq
  intro y hy
  simp only [e8Reps, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact key e8FrameX fun σ hσ => by simp [hσ]
  · exact key e8FrameY fun σ hσ => by simp [hσ]
  · exact key e8FrameZ fun σ hσ => by simp [hσ]
  · exact key e8FrameU fun σ hσ => by simp [hσ]

theorem lie23To89At_E8 : Lie23To89At .E8 := by
  intro X _ _ n f hadm hM τ hτ h23
  have hn : n = 0 := hadm.2.2
  subst hn
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hM.chevalleyExceptionalModel (by decide)
  have hK2 : ringChar K = 2 :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_two hadm.2.1 hcard
  haveI : CharP K 2 := ringChar.of_eq hK2
  have h11 : 11 ∣ f := eleven_dvd_of_twentythree_dvd_card (by simp) hadm hM
    (dvd_trans h23 (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨ε, hε⟩ := exists_unit_orderOf_eightynine_of_card hcard h11
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  exact prime_dvd_card_centralizer_of_classesCover (e.trans (adjointQuotientEquiv .E8 K))
    classesCover_e8Reps (e8_exists_order_eightynine_commute hε) hτ

end CFSG.ComponentClassification.CatFC.DS81.Ex
