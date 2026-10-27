module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.SolKAb.Residue
public import CFSG.CGT.PushingUpLit.SolKAb.Setup
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (MTOutcome STSetting sylowImg)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedClassicalModel)

@[expose] def PosModel (t : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Blueprint.LieModel X t n 3 1 →
    ∀ Q : Subgroup X, IsQuaternionTwoGroup Q → Nonempty (↥Q ≃* QuaternionGroup 2)

@[expose] def NegModel (t : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Blueprint.LieModel X t n 3 1 →
    ∀ (K : Subgroup X), STSetting X K → ∀ R : Sylow 2 K, ¬ IsQuaternionTwoGroup (sylowImg R)

@[expose] def Pos3Table : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n : ℕ),
    ((t = .PSL ∧ n = 3) ∨ (t = .PSU ∧ n = 3) ∨ (t = .G2 ∧ n = 0)) →
    CFSG.Blueprint.LieModel X t n 3 1 →
    ∀ Q : Subgroup X, IsQuaternionTwoGroup Q → Nonempty (↥Q ≃* QuaternionGroup 2)

@[expose] def Neg3Table : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n : ℕ),
    ((t = .PSL ∧ (n = 4 ∨ n = 5)) ∨ (t = .PSU ∧ n = 4) ∨ (t = .PSp ∧ n = 2) ∨
      (t = .trialityD4 ∧ n = 0)) →
    CFSG.Blueprint.LieModel X t n 3 1 →
    ∀ (K : Subgroup X), STSetting X K → ∀ R : Sylow 2 K, ¬ IsQuaternionTwoGroup (sylowImg R)

@[expose] def Small3Table : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n : ℕ),
    ((t = .PSL ∧ (n = 3 ∨ n = 4 ∨ n = 5)) ∨ (t = .PSU ∧ (n = 3 ∨ n = 4)) ∨ (t = .PSp ∧ n = 2) ∨
      ((t = .G2 ∨ t = .trialityD4) ∧ n = 0)) →
    CFSG.Blueprint.LieModel X t n 3 1 →
    ∀ (K : Subgroup X), STSetting X K → ∀ R : Sylow 2 K, IsQuaternionTwoGroup (sylowImg R) →
      MTOutcome X K R

theorem statedClassical_of_lieModel_ne_zero {X : Type} [Group X] {t : StatedLieTag} {n : ℕ}
    (hn : n ≠ 0) (h : CFSG.Blueprint.LieModel X t n 3 1) : StatedClassicalModel X t n 3 1 :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem small3Table_of_pos_neg (hP : Pos3Table) (hN : Neg3Table) : Small3Table := by
  intro X _ _ t n hcases hm K hK R hq
  by_cases hpos : (t = .PSL ∧ n = 3) ∨ (t = .PSU ∧ n = 3) ∨ (t = .G2 ∧ n = 0)
  · have hQ8 : Nonempty (↥(sylowImg R) ≃* QuaternionGroup 2) := hP X t n hpos hm _ hq
    rcases hpos with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hQ8, Or.inl
        (statedClassical_of_lieModel_ne_zero (by norm_num) hm)⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hQ8, Or.inr (Or.inl
        (statedClassical_of_lieModel_ne_zero (by norm_num) hm))⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hQ8, Or.inr (Or.inr (Or.inl hm))⟩))
  · have hneg : ((t = .PSL ∧ (n = 4 ∨ n = 5)) ∨ (t = .PSU ∧ n = 4) ∨ (t = .PSp ∧ n = 2) ∨
        (t = .trialityD4 ∧ n = 0)) := by
      rcases hcases with ⟨h1, h2 | h2 | h2⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2⟩ | ⟨h1 | h1, h2⟩
      · exact absurd (Or.inl ⟨h1, h2⟩) hpos
      · exact Or.inl ⟨h1, Or.inl h2⟩
      · exact Or.inl ⟨h1, Or.inr h2⟩
      · exact absurd (Or.inr (Or.inl ⟨h1, h2⟩)) hpos
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
      · exact absurd (Or.inr (Or.inr ⟨h1, h2⟩)) hpos
      · exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))
    exact (hN X t n hneg hm K hK R hq).elim

theorem neg3Table_of_five (h1 : NegModel .PSL 4) (h2 : NegModel .PSL 5) (h3 : NegModel .PSU 4)
    (h4 : NegModel .PSp 2) (h5 : NegModel .trialityD4 0) : Neg3Table := by
  intro X _ _ t n hc hm K hK R
  rcases hc with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h1 X hm K hK R
  · exact h2 X hm K hK R
  · exact h3 X hm K hK R
  · exact h4 X hm K hK R
  · exact h5 X hm K hK R

theorem pos3Table_of_three (h1 : PosModel .PSL 3) (h2 : PosModel .PSU 3) (h3 : PosModel .G2 0) :
    Pos3Table := by
  intro X _ _ t n hc hm Q hQ
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h1 X hm Q hQ
  · exact h2 X hm Q hQ
  · exact h3 X hm Q hQ

end CFSG.CGT.PushingUpLit.SolKNA
