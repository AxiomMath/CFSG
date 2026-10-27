module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDetExc
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSL
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenLinearSource
import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

theorem exists_projectiveSL_equiv_of_lieModel_PSL {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .PSL n p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (X ≃* projectiveSL n K) :=
  CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel h

theorem not_lieModel_PSL_three_four {X : Type} [Group X] (h3 : LieModel X .PSL 3 2 2)
    (h4 : LieModel X .PSL 4 2 1) : False := by
  obtain ⟨K₄, _, _, hK₄, ⟨e₄⟩⟩ := exists_projectiveSL_equiv_of_lieModel_PSL h3
  obtain ⟨K₂, _, _, hK₂, ⟨e₂⟩⟩ := exists_projectiveSL_equiv_of_lieModel_PSL h4
  exact (ComponentClassification.SymmetricLocal.projectiveSL_three_four_not_equiv
    (by rw [hK₄]; norm_num) (by rw [hK₂]; norm_num)).false (e₄.symm.trans e₂)

theorem lieModel_PSL_two_unique_classicalOrSuzuki_of_card_eq
    {X Y : Type} [Group X] [Group Y] {m f : ℕ} (hm : 3 ≤ m) (hX : LieModel X .PSL m 2 f)
    {t : StatedLieTag} {n f' : ℕ} (ht : t ∈ classicalTags ∨ t = .twistedB2)
    (h : LieModel Y t n 2 f') (hcard : Nat.card Y = Nat.card X) :
    t = .PSL ∧ ((n = m ∧ f' = f) ∨ (n = 4 ∧ f' = 1 ∧ m = 3 ∧ f = 2) ∨
      (n = 3 ∧ f' = 2 ∧ m = 4 ∧ f = 1)) := by
  have he := F4Pilot.card_eq_evenLieOrder_of_classicalOrSuzuki ht h
  rw [hcard, F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hX] at he
  obtain ⟨rfl, h1⟩ := evenLieOrder_eq_ordA (r := m - 1) (F4Pilot.statedLieAdmissible_of_lieModel h)
    (by omega) (F4Pilot.statedLieAdmissible_of_lieModel hX).2.1 he.symm
  refine ⟨rfl, ?_⟩
  rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨by omega, h2⟩
  · exact Or.inr (Or.inl ⟨h1, h2, by omega, h4⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, by omega, h4⟩)

theorem lieModel_PSL_two_unique_classicalOrSuzuki {X : Type}
    [Group X] {m f : ℕ} (hm : 3 ≤ m) (hX : LieModel X .PSL m 2 f) {t : StatedLieTag} {n f' : ℕ}
    (ht : t ∈ classicalTags ∨ t = .twistedB2) (h : LieModel X t n 2 f') :
    t = .PSL ∧ n = m ∧ f' = f := by
  obtain ⟨rfl, h1 | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩⟩ :=
    lieModel_PSL_two_unique_classicalOrSuzuki_of_card_eq hm hX ht h rfl
  · exact ⟨rfl, h1⟩
  · exact (not_lieModel_PSL_three_four hX h).elim
  · exact (not_lieModel_PSL_three_four h hX).elim

section Orders


theorem lieModel_PSL_two_unique_of_card_eq {X Y : Type} [Group X] [Group Y] {m f : ℕ}
    (hm : 3 ≤ m) (hX : LieModel X .PSL m 2 f) {t : StatedLieTag} {n f' : ℕ}
    (h : LieModel Y t n 2 f') (hcard : Nat.card Y = Nat.card X) :
    t = .PSL ∧ ((n = m ∧ f' = f) ∨ (n = 4 ∧ f' = 1 ∧ m = 3 ∧ f = 2) ∨
      (n = 3 ∧ f' = 2 ∧ m = 4 ∧ f = 1)) := by
  have he := F4Pilot.card_eq_evenLieOrder h
  rw [hcard, F4Pilot.card_eq_evenLieOrder hX] at he
  obtain ⟨rfl, h1⟩ := evenLieOrder_eq_ordA (r := m - 1) (F4Pilot.statedLieAdmissible_of_lieModel h)
    (by omega) (F4Pilot.statedLieAdmissible_of_lieModel hX).2.1 he.symm
  refine ⟨rfl, ?_⟩
  rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨by omega, h2⟩
  · exact Or.inr (Or.inl ⟨h1, h2, by omega, h4⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, by omega, h4⟩)

theorem lieModel_PSL_two_unique {X : Type} [Group X] {m f : ℕ} (hm : 3 ≤ m)
    (hX : LieModel X .PSL m 2 f) {t : StatedLieTag} {n f' : ℕ} (h : LieModel X t n 2 f') :
    t = .PSL ∧ n = m ∧ f' = f := by
  obtain ⟨rfl, h1 | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩⟩ :=
    lieModel_PSL_two_unique_of_card_eq hm hX h rfl
  · exact ⟨rfl, h1⟩
  · exact (not_lieModel_PSL_three_four hX h).elim
  · exact (not_lieModel_PSL_three_four h hX).elim

theorem slmEvenTypeDetAt {m : ℕ} (hm : 3 ≤ m) : SLmEvenTypeDetAt m :=
  fun _ _ _ _ _ _ hX _ h => lieModel_PSL_two_unique hm hX h

theorem slmEvenTypeDet : SLmEvenTypeDet := fun _ hm => slmEvenTypeDetAt hm

end Orders

end CFSG.SeitzReduction.LinearPilot
