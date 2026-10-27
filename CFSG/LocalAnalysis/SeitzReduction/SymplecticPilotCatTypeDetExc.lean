module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDetOrders
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.SeitzReduction.F4Pilot (idxBC profile_idxBC)
open CFSG.SeitzReduction.F4Pilot.EvenExc (profile_ordG2' profile_ordF4' profile_ordE6'
  profile_ordTwistedE6' profile_ordE7' profile_ordE8' profile_ordTrialityD4' profile_ordSuzuki'
  profile_ordTwistedF4')

theorem exc_vs_ordBC {M a b e m f : ℕ} {Z : ℕ → Prop} (hm : 4 ≤ m) (hf : 1 ≤ f) (he : 1 ≤ e)
    (h : Profile M (e * a) Z) (hw : Z (e * b)) (hle : ∀ k, Z k → k ≤ e * b)
    (hM : M = ordBC m (2 ^ f)) :
    2 * a = b * m ∧ e * b = f * (2 * m) ∧ ∀ k, 2 ≤ k → k ≠ 6 → (Z k ↔ idxBC m f k) :=
  vsBC_rank (by omega) hf he h hw hle (Or.inr (by nlinarith)) hM

theorem ordG2_ne_ordBC_of_four_le {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordG2 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  intro h
  have := (exc_vs_ordBC (a := 6) (b := 6) hm hf he (profile_ordG2' he) (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega)) h).1
  omega

theorem ordTrialityD4_ne_ordBC_of_four_le {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordTrialityD4 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  intro h
  have := (exc_vs_ordBC (a := 12) (b := 12) hm hf he (profile_ordTrialityD4' he)
    (Or.inl ⟨dvd_rfl, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    h).1
  omega

theorem ordTwistedF4_ne_ordBC_of_four_le {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordTwistedF4 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  intro h
  have := (exc_vs_ordBC (a := 12) (b := 12) hm hf he (profile_ordTwistedF4' he)
    (Or.inl ⟨⟨1, by ring⟩, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h | ⟨h, -⟩ | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    h).1
  omega

theorem ordSuzuki_ne_ordBC_of_four_le {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordSuzuki (2 ^ e) ≠ ordBC m (2 ^ f) := by
  intro h
  have := (exc_vs_ordBC (a := 2) (b := 4) hm hf he (profile_ordSuzuki' he)
    (Or.inl ⟨⟨1, by ring⟩, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    h).1
  omega

theorem ordF4_ne_ordBC_of_four_le {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordF4 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := exc_vs_ordBC (a := 24) (b := 12) hm hf he (profile_ordF4' he)
    (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega)) h
  obtain rfl : m = 4 := by omega
  have hrel : 2 * f = 3 * e := by omega
  obtain ⟨i, hi, hd⟩ := (hZ (e * 8) (by omega) (by omega)).mp (Or.inr (Or.inl dvd_rfl))
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
  have := dvd_of_rel (by omega) hrel hd
  interval_cases i <;> omega

theorem ordE6_ne_ordBC_of_four_le {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordE6 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := exc_vs_ordBC (a := 36) (b := 12) hm hf he (profile_ordE6' he)
    (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega)) h
  obtain rfl : m = 6 := by omega
  have hrel : 1 * f = 1 * e := by omega
  obtain ⟨i, hi, hd⟩ := (hZ (e * 9) (by omega) (by omega)).mp (Or.inr (Or.inl dvd_rfl))
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
  have := dvd_of_rel (by omega) hrel hd
  interval_cases i <;> omega

theorem ordTwistedE6_ne_ordBC_of_four_le {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordTwistedE6 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := exc_vs_ordBC (a := 36) (b := 18) hm hf he (profile_ordTwistedE6' he)
    (Or.inr (Or.inl ⟨⟨1, by ring⟩, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩))
    (fun k hk => by
      rcases hk with h | ⟨h, -⟩ | h | h | ⟨h, -⟩ | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega)) h
  obtain rfl : m = 4 := by omega
  have hrel : 4 * f = 9 * e := by omega
  obtain ⟨i, hi, hd⟩ := (hZ (e * 8) (by omega) (by omega)).mp
    (Or.inr (Or.inr (Or.inl dvd_rfl)))
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
  have := dvd_of_rel (by omega) hrel hd
  interval_cases i <;> omega

theorem ordE7_ne_ordBC_of_four_le {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordE7 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := exc_vs_ordBC (a := 63) (b := 18) hm hf he (profile_ordE7' he)
    (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega)) h
  obtain rfl : m = 7 := by omega
  have hrel : 7 * f = 9 * e := by omega
  obtain ⟨i, hi, hd⟩ := (hZ (e * 14) (by omega) (by omega)).mp (Or.inr (Or.inl dvd_rfl))
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
  have := dvd_of_rel (by omega) hrel hd
  interval_cases i <;> omega

theorem ordE8_ne_ordBC_of_four_le {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordE8 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := exc_vs_ordBC (a := 120) (b := 30) hm hf he (profile_ordE8' he)
    (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h | h | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega)) h
  obtain rfl : m = 8 := by omega
  have hrel : 8 * f = 15 * e := by omega
  obtain ⟨i, hi, hd⟩ := (hZ (e * 14) (by omega) (by omega)).mp
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl dvd_rfl)))))
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
  have := dvd_of_rel (by omega) hrel hd
  interval_cases i <;> omega

theorem ordG2_ne_ordBC {e m f : ℕ} (he : 2 ≤ e) (hm : 2 ≤ m) (hf : 1 ≤ f) :
    ordG2 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
  · exact ordG2_ne_ordBC_two he hf
  · exact F4Pilot.EvenExc.ordG2_ne_ordBC_three he hf
  · exact ordG2_ne_ordBC_of_four_le (by omega) hm4 hf

theorem ordTrialityD4_ne_ordBC {e m f : ℕ} (he : 1 ≤ e) (hm : 2 ≤ m) (hf : 1 ≤ f) :
    ordTrialityD4 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
  · exact ordTrialityD4_ne_ordBC_two he hf
  · exact F4Pilot.EvenExc.ordTrialityD4_ne_ordBC_three he hf
  · exact ordTrialityD4_ne_ordBC_of_four_le he hm4 hf

theorem ordTwistedF4_ne_ordBC {e m f : ℕ} (he : 3 ≤ e) (hm : 2 ≤ m) (hf : 1 ≤ f) :
    ordTwistedF4 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
  · exact ordTwistedF4_ne_ordBC_two he hf
  · exact F4Pilot.EvenExc.ordTwistedF4_ne_ordBC_three (by omega) hf
  · exact ordTwistedF4_ne_ordBC_of_four_le (by omega) hm4 hf

theorem ordSuzuki_ne_ordBC {e m f : ℕ} (he : Odd e) (hm : 2 ≤ m) (hf : 1 ≤ f) :
    ordSuzuki (2 ^ e) ≠ ordBC m (2 ^ f) := by
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
  · exact ordSuzuki_ne_ordBC_two he hf
  · exact F4Pilot.EvenExc.ordSuzuki_ne_ordBC_three he.pos hf
  · exact ordSuzuki_ne_ordBC_of_four_le he.pos hm4 hf

theorem ordF4_ne_ordBC {e m f : ℕ} (he : 1 ≤ e) (hm : 2 ≤ m) (hf : 1 ≤ f) :
    ordF4 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
  · exact ordF4_ne_ordBC_two he hf
  · exact F4Pilot.EvenExc.ordF4_ne_ordBC_three he hf
  · exact ordF4_ne_ordBC_of_four_le he hm4 hf

theorem ordE6_ne_ordBC {e m f : ℕ} (he : 1 ≤ e) (hm : 2 ≤ m) (hf : 1 ≤ f) :
    ordE6 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
  · exact ordE6_ne_ordBC_two he hf
  · exact F4Pilot.EvenExc.ordE6_ne_ordBC_three he hf
  · exact ordE6_ne_ordBC_of_four_le he hm4 hf

theorem ordTwistedE6_ne_ordBC {e m f : ℕ} (he : 1 ≤ e) (hm : 2 ≤ m) (hf : 1 ≤ f) :
    ordTwistedE6 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
  · exact ordTwistedE6_ne_ordBC_two he hf
  · exact F4Pilot.EvenExc.ordTwistedE6_ne_ordBC_three he hf
  · exact ordTwistedE6_ne_ordBC_of_four_le he hm4 hf

theorem ordE7_ne_ordBC {e m f : ℕ} (he : 1 ≤ e) (hm : 2 ≤ m) (hf : 1 ≤ f) :
    ordE7 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
  · exact ordE7_ne_ordBC_two he hf
  · exact F4Pilot.EvenExc.ordE7_ne_ordBC_three he hf
  · exact ordE7_ne_ordBC_of_four_le he hm4 hf

theorem ordE8_ne_ordBC {e m f : ℕ} (he : 1 ≤ e) (hm : 2 ≤ m) (hf : 1 ≤ f) :
    ordE8 (2 ^ e) ≠ ordBC m (2 ^ f) := by
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
  · exact ordE8_ne_ordBC_two he hf
  · exact F4Pilot.EvenExc.ordE8_ne_ordBC_three he hf
  · exact ordE8_ne_ordBC_of_four_le he hm4 hf

theorem ordTits_ne_ordBC {m f : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f) : ordTits ≠ ordBC m (2 ^ f) := by
  rw [ordTits_eq]
  refine fun h => (profile_idxBC (n := m) hf).ne_of_ne (by decide) ?_ h.symm
  rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
  · omega
  · omega
  · have : 4 * 4 ≤ m * m := Nat.mul_le_mul hm4 hm4
    have : m * m ≤ f * (m * m) := Nat.le_mul_of_pos_left _ hf
    omega

theorem evenLieOrder_eq_ordBC {t : StatedLieTag} {n g m f : ℕ}
    (hadm : StatedLieAdmissible t n 2 g) (hm : 2 ≤ m) (hf : 1 ≤ f)
    (h : F4Pilot.evenLieOrder t n g = ordBC m (2 ^ f)) : t = .PSp ∧ n = m ∧ g = f := by
  have hG2 : t = .G2 → 2 ≤ g := fun ht => F4Pilot.two_le_of_admissible_G2 (ht ▸ hadm)
  obtain ⟨-, hg, ht⟩ := hadm
  cases t
  case PSL => exact absurd h (ordA_ne_ordBC (by obtain ⟨hn, -⟩ := ht; omega) hg hm hf)
  case PSU => exact absurd h (ordTwistedA_ne_ordBC (by obtain ⟨hn, -⟩ := ht; omega) hg hm hf)
  case PSp =>
    obtain ⟨hn, -⟩ := ht
    obtain ⟨rfl, rfl⟩ := ordBC_eq_ordBC hn hg hm hf h
    exact ⟨rfl, rfl, rfl⟩
  case POmegaOdd => exact absurd rfl ht.2
  case POmegaPlus => exact absurd h (ordD_ne_ordBC ht hg hm hf)
  case POmegaMinus => exact absurd h (ordTwistedD_ne_ordBC ht hg hm hf)
  case G2 => exact absurd h (ordG2_ne_ordBC (hG2 rfl) hm hf)
  case F4 => exact absurd h (ordF4_ne_ordBC hg hm hf)
  case E6 => exact absurd h (ordE6_ne_ordBC hg hm hf)
  case E7 => exact absurd h (ordE7_ne_ordBC hg hm hf)
  case E8 => exact absurd h (ordE8_ne_ordBC hg hm hf)
  case twistedE6 => exact absurd h (ordTwistedE6_ne_ordBC hg hm hf)
  case trialityD4 => exact absurd h (ordTrialityD4_ne_ordBC hg hm hf)
  case twistedB2 => exact absurd h (ordSuzuki_ne_ordBC ht.2.2.1 hm hf)
  case twistedG2 => exact absurd ht.2.1 (by norm_num)
  case twistedF4 => exact absurd h (ordTwistedF4_ne_ordBC ht.2.2.2 hm hf)
  case Tits => exact absurd h (ordTits_ne_ordBC hm hf)

end CFSG.SeitzReduction.SymplecticPilot
