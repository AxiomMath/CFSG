module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDetExcMinus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatAlt
public import CFSG.RankThree.PartOne.S12K.OrdRigidL
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDetExc

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem evenLieOrder_eq_ordD {t : StatedLieTag} {n g m f : ℕ}
    (hadm : StatedLieAdmissible t n 2 g) (hm : 4 ≤ m) (hf : 1 ≤ f)
    (h : F4Pilot.evenLieOrder t n g = ordD m (2 ^ f)) :
    t = .POmegaPlus ∧ n = m ∧ g = f := by
  have hG2 : t = .G2 → 2 ≤ g := fun ht => F4Pilot.two_le_of_admissible_G2 (ht ▸ hadm)
  obtain ⟨-, hg, ht⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hn, -⟩ := ht
    rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
    · exact absurd h.symm (RankThree.PartOne.S12K.ordD_ne_ordA_one hm hf hg)
    · exact absurd h.symm (LinearPilot.ordD_ne_ordA hm hf (by omega) hg)
  case PSU =>
    exact absurd h.symm (ordD_ne_ordTwistedA hm hf (by obtain ⟨hn, -⟩ := ht; omega) hg)
  case PSp =>
    obtain ⟨hn, -⟩ := ht
    rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | hn4
    · exact absurd h.symm (ordD_ne_ordBC_two hm hf hg)
    · exact absurd h.symm (F4Pilot.ordD_ne_ordBC_three hm hf hg)
    · exact absurd h (ordBC_ne_ordD hn4 hg hm hf)
  case POmegaOdd => exact absurd rfl ht.2
  case POmegaPlus =>
    obtain ⟨rfl, rfl⟩ := ordD_eq_ordD ht hg hm hf h
    exact ⟨rfl, rfl, rfl⟩
  case POmegaMinus => exact absurd h (ordTwistedD_ne_ordD ht hg hm hf)
  case G2 => exact absurd h (ordG2_ne_ordD (hG2 rfl) hm hf)
  case F4 => exact absurd h (ordF4_ne_ordD hg hm hf)
  case E6 => exact absurd h (ordE6_ne_ordD hg hm hf)
  case E7 => exact absurd h.symm (E8Pilot.ordD_ne_ordE7 hm hf hg)
  case E8 => exact absurd h (ordE8_ne_ordD hg hm hf)
  case twistedE6 => exact absurd h (ordTwistedE6_ne_ordD hg hm hf)
  case trialityD4 => exact absurd h (ordTrialityD4_ne_ordD hg hm hf)
  case twistedB2 => exact absurd h (ordSuzuki_ne_ordD (by obtain ⟨-, -, -, h3⟩ := ht; omega) hm hf)
  case twistedG2 => exact absurd ht.2.1 (by norm_num)
  case twistedF4 => exact absurd h (ordTwistedF4_ne_ordD hg hm hf)
  case Tits => exact absurd h (ordTits_ne_ordD hm hf)

theorem evenLieOrder_eq_ordTwistedD {t : StatedLieTag} {n g m f : ℕ}
    (hadm : StatedLieAdmissible t n 2 g) (hm : 4 ≤ m) (hf : 1 ≤ f)
    (h : F4Pilot.evenLieOrder t n g = ordTwistedD m (2 ^ f)) :
    t = .POmegaMinus ∧ n = m ∧ g = f := by
  obtain ⟨-, hg, ht⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hn, -⟩ := ht
    rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
    · exact absurd h.symm (RankThree.PartOne.S12K.ordTwistedD_ne_ordA_one hm hf hg)
    · exact absurd h.symm (LinearPilot.ordTwistedD_ne_ordA hm hf (by omega) hg)
  case PSU =>
    exact absurd h.symm (ordTwistedD_ne_ordTwistedA hm hf (by obtain ⟨hn, -⟩ := ht; omega) hg)
  case PSp =>
    obtain ⟨hn, -⟩ := ht
    rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | hn4
    · exact absurd h.symm (ordTwistedD_ne_ordBC_two hm hf hg)
    · exact absurd h.symm (F4Pilot.ordTwistedD_ne_ordBC_three hm hf hg)
    · exact absurd h (ordBC_ne_ordTwistedD hn4 hg hm hf)
  case POmegaOdd => exact absurd rfl ht.2
  case POmegaPlus => exact absurd h.symm (ordTwistedD_ne_ordD hm hf ht hg)
  case POmegaMinus =>
    obtain ⟨rfl, rfl⟩ := ordTwistedD_eq_ordTwistedD ht hg hm hf h
    exact ⟨rfl, rfl, rfl⟩
  case G2 => exact absurd h (ordG2_ne_ordTwistedD hg hm hf)
  case F4 => exact absurd h (ordF4_ne_ordTwistedD hg hm hf)
  case E6 => exact absurd h (ordE6_ne_ordTwistedD hg hm hf)
  case E7 => exact absurd h.symm (E8Pilot.ordTwistedD_ne_ordE7 hm hf hg)
  case E8 => exact absurd h (ordE8_ne_ordTwistedD hg hm hf)
  case twistedE6 => exact absurd h (ordTwistedE6_ne_ordTwistedD hg hm hf)
  case trialityD4 => exact absurd h (ordTrialityD4_ne_ordTwistedD hg hm hf)
  case twistedB2 => exact absurd h (ordSuzuki_ne_ordTwistedD hg hm hf)
  case twistedG2 => exact absurd ht.2.1 (by norm_num)
  case twistedF4 => exact absurd h (ordTwistedF4_ne_ordTwistedD hg hm hf)
  case Tits => exact absurd h (ordTits_ne_ordTwistedD hm hf)

theorem evenLieOrder_eq_POmega {s t : StatedLieTag} (hs : s = .POmegaPlus ∨ s = .POmegaMinus)
    {n g m f : ℕ} (hadm : StatedLieAdmissible t n 2 g) (hm : 4 ≤ m) (hf : 1 ≤ f)
    (h : F4Pilot.evenLieOrder t n g = F4Pilot.evenLieOrder s m f) :
    t = s ∧ n = m ∧ g = f := by
  rcases hs with rfl | rfl
  · exact evenLieOrder_eq_ordD hadm hm hf h
  · exact evenLieOrder_eq_ordTwistedD hadm hm hf h

@[expose] def OmegaEvenTypeDetAt (m : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (s : StatedLieTag) (f : ℕ) (t : StatedLieTag) (n f' : ℕ),
    (s = .POmegaPlus ∨ s = .POmegaMinus) → LieModel X s m 2 f →
      StatedLieAdmissible t n 2 f' → LieModel X t n 2 f' → t = s ∧ n = m ∧ f' = f

theorem lieModel_POmega_two_unique_classicalOrSuzuki_of_card_eq
    {X Y : Type} [Group X] [Group Y] {s : StatedLieTag} {m f : ℕ}
    (hs : s = .POmegaPlus ∨ s = .POmegaMinus) (hX : LieModel X s m 2 f) {t : StatedLieTag}
    {n f' : ℕ} (ht : t ∈ classicalTags ∨ t = .twistedB2) (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : t = s ∧ n = m ∧ f' = f := by
  refine evenLieOrder_eq_POmega hs (F4Pilot.statedLieAdmissible_of_lieModel h)
    (four_le_of_lieModel_POmega hs hX) (one_le_of_lieModel_POmega hs hX) ?_
  rw [← F4Pilot.card_eq_evenLieOrder_of_classicalOrSuzuki ht h, hcard,
    card_of_lieModel_POmega_two hs hX]

section Orders


theorem lieModel_POmega_two_unique_of_card_eq {X Y : Type} [Group X] [Group Y]
    {s : StatedLieTag} {m f : ℕ} (hs : s = .POmegaPlus ∨ s = .POmegaMinus)
    (hX : LieModel X s m 2 f) {t : StatedLieTag} {n f' : ℕ} (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : t = s ∧ n = m ∧ f' = f := by
  refine evenLieOrder_eq_POmega hs (F4Pilot.statedLieAdmissible_of_lieModel h)
    (four_le_of_lieModel_POmega hs hX) (one_le_of_lieModel_POmega hs hX) ?_
  rw [← F4Pilot.card_eq_evenLieOrder h, hcard, card_of_lieModel_POmega_two hs hX]

theorem lieModel_POmega_two_unique {X : Type} [Group X] {s : StatedLieTag} {m f : ℕ}
    (hs : s = .POmegaPlus ∨ s = .POmegaMinus) (hX : LieModel X s m 2 f) {t : StatedLieTag}
    {n f' : ℕ} (h : LieModel X t n 2 f') : t = s ∧ n = m ∧ f' = f :=
  lieModel_POmega_two_unique_of_card_eq hs hX h rfl

theorem omegaEvenTypeDetAt (m : ℕ) : OmegaEvenTypeDetAt m :=
  fun _ _ _ _ _ _ _ hs hX _ h => lieModel_POmega_two_unique hs hX h

end Orders

end CFSG.SeitzReduction.OmegaPilot
