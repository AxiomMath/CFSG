module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreExcB

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld.Orders
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.SeitzReduction.F4Pilot (evenLieOrder)

theorem ordG2_two_pow_injective {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f)
    (h : ordG2 (2 ^ g) = ordG2 (2 ^ f)) : g = f := by
  have h1 := CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordG2' hg
  rw [h] at h1
  have hN := (h1.transfer (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordG2' hf)).1
  omega

theorem ordG2_ne_ordSuzuki_two_pow {g f : ℕ} (hg : 2 ≤ g) (hf : 1 ≤ f) :
    ordG2 (2 ^ g) ≠ ordSuzuki (2 ^ f) := by
  intro h
  have h1 := CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordG2' (by omega : 1 ≤ g)
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordSuzuki' hf)
  have hk := (hZ (g * 6) (by omega) (by omega)).mp (Or.inl dvd_rfl)
  rcases hk with ⟨-, h3⟩ | h2
  · exact (h3 (by rw [← hN])).elim
  · have := Nat.le_of_dvd (by omega) h2
    omega

theorem ordG2_ne_ordTits_two_pow {g : ℕ} (hg : 1 ≤ g) : ordG2 (2 ^ g) ≠ ordTits := by
  have h := (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordG2' hg).ne_of_ne
    (show Odd (3 ^ 3 * 5 ^ 2 * 13) by decide) (show g * 6 ≠ 11 by omega)
  intro he
  apply h
  rw [he]
  norm_num [ordTits]

theorem evenLieOrder_eq_ordG2 {t : StatedLieTag} {m g f : ℕ}
    (hadm : StatedLieAdmissible t m 2 g) (hf : 2 ≤ f)
    (h : evenLieOrder t m g = ordG2 (2 ^ f)) : t = .G2 ∧ g = f := by
  have hG2 : t = .G2 → 2 ≤ g := fun ht =>
    CFSG.SeitzReduction.F4Pilot.two_le_of_admissible_G2 (ht ▸ hadm)
  obtain ⟨-, hg, ht⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hm, -⟩ := ht
    rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
    · exact absurd h.symm (RankThree.PartOne.S12K.ordG2_ne_ordA_one (by omega) hg)
    · exact absurd h.symm
        (SeitzReduction.LinearPilot.ordG2_ne_ordA (by omega) (by omega : 2 ≤ m - 1) hg)
  case PSU =>
    obtain ⟨hm, -⟩ := ht
    exact absurd h.symm (ordG2_ne_ordTwistedA hf (by omega : 2 ≤ m - 1) hg)
  case PSp => exact absurd h.symm (SeitzReduction.SymplecticPilot.ordG2_ne_ordBC hf ht.1 hg)
  case POmegaOdd => exact absurd rfl ht.2
  case POmegaPlus => exact absurd h.symm (SeitzReduction.OmegaPilot.ordG2_ne_ordD hf ht hg)
  case POmegaMinus =>
    exact absurd h.symm (SeitzReduction.OmegaPilot.ordG2_ne_ordTwistedD (by omega) ht hg)
  case G2 => exact ⟨rfl, ordG2_two_pow_injective (by omega) (by omega) h⟩
  case F4 => exact absurd h.symm (StandardType.NbrInnerMore.ordG2_ne_ordF4 (by omega) hg)
  case E6 => exact absurd h.symm (StandardType.NbrInnerMore.ordG2_ne_ordE6 (by omega) hg)
  case E7 => exact absurd h.symm (SeitzReduction.E8Pilot.ordG2_ne_ordE7 (by omega) hg)
  case E8 => exact absurd h.symm (StandardType.NbrInnerMore.ordG2_ne_ordE8 (by omega) hg)
  case twistedE6 =>
    exact absurd h.symm (StandardType.NbrInnerMore.ordG2_ne_ordTwistedE6 (by omega) hg)
  case trialityD4 =>
    exact absurd h.symm (StandardType.NbrInnerMore.ordG2_ne_ordTrialityD4 (by omega) hg)
  case twistedB2 => exact absurd h.symm (ordG2_ne_ordSuzuki_two_pow hf hg)
  case twistedG2 => exact absurd ht.2.1 (by norm_num)
  case twistedF4 =>
    exact absurd h.symm (StandardType.NbrInnerMore.ordG2_ne_ordTwistedF4 (by omega) hg
      (by obtain ⟨-, -, -, h3⟩ := ht; omega))
  case Tits => exact absurd h.symm (ordG2_ne_ordTits_two_pow (by omega))

theorem two_pow_twelve_dvd_ordG2 {n : ℕ} (hn : 2 ≤ n) : 2 ^ 12 ∣ ordG2 (2 ^ n) := by
  have h : 2 ^ (6 * n) = (2 ^ n) ^ 6 := by rw [← pow_mul, mul_comm]
  refine (Nat.pow_dvd_pow 2 (by omega : 12 ≤ 6 * n)).trans ?_
  rw [h]
  exact ((Dvd.intro _ rfl : (2 ^ n) ^ 6 ∣ (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1))).mul_right _

section Orders


theorem lieModel_G2_two_unique {X : Type} [Group X] {n : ℕ} (hG : LieModel X .G2 0 2 n)
    {t : StatedLieTag} {m g : ℕ} (h : LieModel X t m 2 g) : t = .G2 ∧ g = n := by
  refine evenLieOrder_eq_ordG2 (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel h)
    (CFSG.SeitzReduction.F4Pilot.two_le_of_admissible_G2
      (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hG)) ?_
  rw [← CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder h,
    CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hG]
  rfl

theorem false_of_lieModel_G2_of_ne {X : Type} [Group X] {n : ℕ} (hG : LieModel X .G2 0 2 n)
    {t : StatedLieTag} {m g : ℕ} (ht : t ≠ .G2) (h : LieModel X t m 2 g) : False :=
  ht (lieModel_G2_two_unique hG h).1

theorem two_pow_twelve_dvd_card_of_lieModel_G2 {X : Type} [Group X] {n : ℕ}
    (hG : LieModel X .G2 0 2 n) : 2 ^ 12 ∣ Nat.card X := by
  rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hG]
  exact two_pow_twelve_dvd_ordG2 (CFSG.SeitzReduction.F4Pilot.two_le_of_admissible_G2
    (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hG))

end Orders

end CFSG.EvenSporadicStandard.Induction
