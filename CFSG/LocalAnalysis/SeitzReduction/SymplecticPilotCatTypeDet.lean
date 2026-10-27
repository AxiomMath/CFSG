module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDetExc

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def Sp2mEvenTypeDet (m : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ) (t : StatedLieTag) (n f' : ℕ),
    LieModel X .PSp m 2 f → StatedLieAdmissible t n 2 f' → LieModel X t n 2 f' →
      t = .PSp ∧ n = m ∧ f' = f

@[expose] def Sp2mEvenTypeDetClassical (m : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ) (t : StatedLieTag) (n f' : ℕ),
    (t ∈ classicalTags ∨ t = .twistedB2) → LieModel X .PSp m 2 f → StatedLieAdmissible t n 2 f' →
      LieModel X t n 2 f' → t = .PSp ∧ n = m ∧ f' = f

theorem sp2mEvenTypeDetClassical_of_sp2mEvenTypeDet {m : ℕ} (h : Sp2mEvenTypeDet m) :
    Sp2mEvenTypeDetClassical m :=
  fun X _ f t n f' _ h1 h2 h3 => h X f t n f' h1 h2 h3

theorem admissible_of_lieModel_PSp {X : Type} [Group X] {m f : ℕ} (h : LieModel X .PSp m 2 f) :
    1 ≤ f ∧ 2 ≤ m ∧ (m, 2 ^ f) ≠ (2, 2) := by
  obtain ⟨-, hf, hm, h22⟩ := F4Pilot.statedLieAdmissible_of_lieModel h
  exact ⟨hf, hm, h22⟩

theorem not_lieModel_PSp_two_two_one {X : Type} [Group X] : ¬ LieModel X .PSp 2 2 1 :=
  fun h => (admissible_of_lieModel_PSp h).2.2 rfl

theorem lieModel_PSp_two_unique_classicalOrSuzuki_of_card_eq
    {X Y : Type} [Group X] [Group Y] {m f : ℕ} (hX : LieModel X .PSp m 2 f) {t : StatedLieTag}
    {n f' : ℕ} (ht : t ∈ classicalTags ∨ t = .twistedB2) (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : t = .PSp ∧ n = m ∧ f' = f := by
  obtain ⟨hf, hm, -⟩ := admissible_of_lieModel_PSp hX
  refine evenLieOrder_eq_ordBC (F4Pilot.statedLieAdmissible_of_lieModel h) hm hf ?_
  rw [← F4Pilot.card_eq_evenLieOrder_of_classicalOrSuzuki ht h, hcard,
    F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hX]
  rfl

theorem lieModel_PSp_two_unique_classicalOrSuzuki {X : Type}
    [Group X] {m f : ℕ} (hX : LieModel X .PSp m 2 f) {t : StatedLieTag} {n f' : ℕ}
    (ht : t ∈ classicalTags ∨ t = .twistedB2) (h : LieModel X t n 2 f') :
    t = .PSp ∧ n = m ∧ f' = f :=
  lieModel_PSp_two_unique_classicalOrSuzuki_of_card_eq hX ht h rfl

theorem sp2mEvenTypeDetClassical (m : ℕ) :
    Sp2mEvenTypeDetClassical m :=
  fun _ _ _ _ _ _ ht hX _ h => lieModel_PSp_two_unique_classicalOrSuzuki hX ht h

section Orders


theorem lieModel_PSp_two_unique_of_card_eq {X Y : Type} [Group X] [Group Y] {m f : ℕ}
    (hX : LieModel X .PSp m 2 f) {t : StatedLieTag} {n f' : ℕ} (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : t = .PSp ∧ n = m ∧ f' = f := by
  obtain ⟨hf, hm, -⟩ := admissible_of_lieModel_PSp hX
  refine evenLieOrder_eq_ordBC (F4Pilot.statedLieAdmissible_of_lieModel h) hm hf ?_
  rw [← F4Pilot.card_eq_evenLieOrder h, hcard, F4Pilot.card_eq_evenLieOrder hX]
  rfl

theorem lieModel_PSp_two_unique {X : Type} [Group X] {m f : ℕ} (hX : LieModel X .PSp m 2 f)
    {t : StatedLieTag} {n f' : ℕ} (h : LieModel X t n 2 f') : t = .PSp ∧ n = m ∧ f' = f :=
  lieModel_PSp_two_unique_of_card_eq hX h rfl

theorem sp2mEvenTypeDet (m : ℕ) : Sp2mEvenTypeDet m :=
  fun _ _ _ _ _ _ hX _ h => lieModel_PSp_two_unique hX h

end Orders

end CFSG.SeitzReduction.SymplecticPilot
