module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTransport

public section

namespace CFSG.ComponentClassification.CatFC.DS81.Ex

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.SeitzReduction
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
  CFSG.ComponentClassification.RankTwoExceptional.Exc

set_option linter.unusedSectionVars false


theorem e7_exists_order_eightynine_commute {K : Type} [Field K] [Finite K] [CharP K 2]
    {ε : Kˣ} (hε : orderOf ε = 89) :
    ∀ y ∈ e7Reps K, ∃ z : adjointGroup .E7 K, orderOf z = 89 ∧ Commute z y := by
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  have h2 : ringChar K = 2 := ringChar.eq K 2
  have key : ∀ F : List (Fin Tag.E7.rank → ℤ),
      (∀ σ ∈ F, σ ∈ e7FrameX ++ e7FrameY ++ e7FrameZ ++ e7FrameU ++ e7FrameV) →
        ∃ z : adjointGroup .E7 K, orderOf z = 89 ∧ Commute z (e7FramePt K F) := by
    intro F hF
    refine ⟨⟨rootDiagUnit .E7 fun i => ε ^ (Pi.single e7Top (1 : ℤ) : Fin Tag.E7.rank → ℤ) i,
      rootDiagUnit_mem_adjointGroup_of_charTwo (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h2 _⟩,
      ?_, ?_⟩
    · rw [Subgroup.orderOf_mk]
      exact orderOf_rootDiagUnit_eq_prime hε (Pi.single e7Top (1 : ℤ)) e7Top (by norm_num)
    · have hroot : ∀ β ∈ F, IsRoot .E7 β := fun β hβ => (isRoot_of_mem_e7Frames β (hF β hβ)).1
      have h0 : ∀ β ∈ F, β e7Top = 0 := fun β hβ => (isRoot_of_mem_e7Frames β (hF β hβ)).2.1
      exact Subtype.ext (commute_rootDiagUnit_single_framePt e7Top F hroot h0 ε).eq
  intro y hy
  simp only [e7Reps, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · exact key e7FrameX fun σ hσ => by simp [hσ]
  · exact key e7FrameY fun σ hσ => by simp [hσ]
  · exact key e7FrameZ fun σ hσ => by simp [hσ]
  · exact key e7FrameU fun σ hσ => by simp [hσ]
  · exact key e7FrameV fun σ hσ => by simp [hσ]

theorem lie23To89At_E7 : Lie23To89At .E7 := by
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
  exact prime_dvd_card_centralizer_of_classesCover (e.trans (adjointQuotientEquiv .E7 K))
    classesCover_e7Reps (e7_exists_order_eightynine_commute hε) hτ

end CFSG.ComponentClassification.CatFC.DS81.Ex
