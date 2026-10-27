module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.SetupData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.CaseShapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.CaseCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.FixOuter

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.CSide
open scoped commutatorElement

theorem cSideFacts_five_local :
    ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    AschbacherHyp C Q → ∀ ρ : C, orderOf ρ = 5 →
        (IsShapeZpTimesA5 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q))) ∧
            Q ⊓ Subgroup.centralizer ({ρ} : Set C) = centerOf Q) ∨
        (IsShapeZpTimesZp 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q))) ∧
            IsMinusExtraspecial 2 (Q ⊓ Subgroup.centralizer ({ρ} : Set C))) ∨
        (IsShapeZpWrTwo 5 ↥(Subgroup.centralizer ({(ρ : C ⧸ Q)} : Set (C ⧸ Q))) ∧
            Q ⊓ Subgroup.centralizer ({ρ} : Set C) = centerOf Q) := by
  classical
  intro C _ Q _ hC ρ hρ
  have hW : WeakHyp C Q := WeakHyp.of_aschbacherHyp hC
  haveI : Finite Q := hW.finite_Q
  haveI : Finite C := hW.finite
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hW.isExtraspecialPGroup
  obtain ⟨S⟩ := hW.nonempty_setup
  obtain ⟨hρL, hg⟩ := CSideSetup.odd_data hW S (p := 5) (Or.inr rfl) hρ
  obtain ⟨t, htL, ht2, _⟩ := hC.exists_isOuterInvolution
  have htq : t ^ 2 ∈ Q := by rw [ht2]; exact one_mem Q
  have ht2bar : (t : C ⧸ Q) ^ 2 = 1 := by
    have h := congrArg (fun x : C => (x : C ⧸ Q)) ht2
    simpa using h
  have hcard : Nat.card {q : C // q ∈ Q ∧ ⁅q, t⁆ ∈ centerOf Q} ≤ 2 ^ 5 := by
    rw [cSide_card_comm_eq hW.isExtraspecialPGroup t, cSide_card_fix_outer hC htL htq]
    norm_num
  by_cases htriv : (S.θ ⟨ρ, hρL⟩).1 = 1 ∨ (S.θ ⟨ρ, hρL⟩).2 = 1
  · exact Or.inl ⟨S.shape_one_coord (p := 5) (Or.inr rfl) hρL hg htriv,
      CSideSetup.cent_eq_of_one_coord hW S (p := 5) (Or.inr rfl) hρL hρ hg htriv⟩
  · have h1 : (S.θ ⟨ρ, hρL⟩).1 ≠ 1 := fun h => htriv (Or.inl h)
    have h2 : (S.θ ⟨ρ, hρL⟩).2 ≠ 1 := fun h => htriv (Or.inr h)
    have hboth := CSideSetup.cent_of_five_both hW S htL ht2bar hcard hρL hρ hg h1 h2
    by_cases hc : IsConj (S.θ ⟨ρ, hρL⟩).1 (S.θ ⟨ρ, hρL⟩).2
    · exact Or.inr (Or.inr ⟨S.shape_conj (p := 5) (Or.inr rfl) hρL hg hc, hboth.1 hc⟩)
    · exact Or.inr (Or.inl ⟨S.shape_nonconj hρL hg h1 h2 hc, hboth.2 hc⟩)

end CFSG.EvenSporadicStandard.HNRecog.Section3
