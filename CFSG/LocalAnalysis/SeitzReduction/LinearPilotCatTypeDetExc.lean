module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDetOrders
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.SeitzReduction.F4Pilot (profile_idxA)
open CFSG.SeitzReduction.F4Pilot.EvenExc (profile_ordG2' profile_ordF4' profile_ordE6'
  profile_ordTwistedE6' profile_ordE7' profile_ordE8' profile_ordTrialityD4' profile_ordSuzuki'
  profile_ordTwistedF4')

theorem dvd_of_rel_top {e b c f r : ℕ} (hf : 1 ≤ f) (hrel : e * b = f * (r + 1))
    (h : f * r ∣ e * c) : r * b ∣ (r + 1) * c := by
  have h1 := mul_dvd_mul_right h b
  have e1 : e * c * b = f * ((r + 1) * c) := by
    calc e * c * b = (e * b) * c := by ring
      _ = f * ((r + 1) * c) := by rw [hrel]; ring
  rw [e1, show f * r * b = f * (r * b) by ring] at h1
  exact Nat.dvd_of_mul_dvd_mul_left (by omega) h1

theorem exc_vs_ordA {M a b e r f : ℕ} {Z : ℕ → Prop} (hr : 2 ≤ r) (hf : 1 ≤ f) (he : 1 ≤ e)
    (h : Profile M (e * a) Z) (hw : Z (e * b)) (hle : ∀ k, Z k → k ≤ e * b) (h6 : 6 < e * b)
    (hM : M = ordA r (2 ^ f)) :
    2 * a = b * r ∧ e * b = f * (r + 1) ∧ (f * r ≠ 6 → Z (f * r)) := by
  obtain ⟨h1, h2, hZ⟩ := vsA_rank (by omega) hf he h hw hle (Or.inl h6) hM
  exact ⟨h1, h2, fun h6' => (hZ _ (by nlinarith) h6').mpr (idxA_sub_top hr)⟩

theorem three_le_tri {r : ℕ} (hr : 2 ≤ r) : 3 ≤ r * (r + 1) / 2 := by
  have : 2 * 3 ≤ r * (r + 1) := Nat.mul_le_mul hr (by omega)
  omega

theorem ordG2_ne_ordA {e r f : ℕ} (he : 1 ≤ e) (hr : 2 ≤ r) (hf : 1 ≤ f) :
    ordG2 (2 ^ e) ≠ ordA r (2 ^ f) := by
  intro h
  have hX := profile_ordG2' he
  have hw : (fun k => k ∣ e * 6 ∨ k ∣ e * 2) (e * 6) := Or.inl dvd_rfl
  have hle : ∀ k, (fun k => k ∣ e * 6 ∨ k ∣ e * 2) k → k ≤ e * 6 := fun k hk => by
    rcases hk with h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega)
  rcases Nat.lt_or_ge 6 (e * 6) with h6 | h6
  · obtain ⟨h1, h2, hZ⟩ := exc_vs_ordA (a := 6) hr hf he hX hw hle h6 h
    obtain rfl : r = 2 := by omega
    rcases hZ (by omega) with h' | h' <;>
    · have := dvd_of_rel_top hf h2 h'
      norm_num at this
  · obtain rfl : e = 1 := by omega
    by_cases h6' : 6 < f * (r + 1)
    · have := (vsA_rank (a := 6) (b := 6) (by omega) hf le_rfl hX hw hle (Or.inr h6') h).2.1
      omega
    · have hN := vsA_two (by omega) hf hX h
      obtain ⟨hr5, hf2⟩ := small_of_le_six hr hf (by omega)
      interval_cases r <;> interval_cases f <;> first | omega | (revert h; decide)

theorem ordTrialityD4_ne_ordA {e r f : ℕ} (he : 1 ≤ e) (hr : 2 ≤ r) (hf : 1 ≤ f) :
    ordTrialityD4 (2 ^ e) ≠ ordA r (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := exc_vs_ordA (a := 12) (b := 12) hr hf he (profile_ordTrialityD4' he)
    (Or.inl ⟨dvd_rfl, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (by omega) h
  obtain rfl : r = 2 := by omega
  rcases hZ (by omega) with ⟨h', -⟩ | h' | h' <;>
  · have := dvd_of_rel_top hf h2 h'
    norm_num at this

theorem ordTwistedF4_ne_ordA {e r f : ℕ} (he : 1 ≤ e) (hr : 2 ≤ r) (hf : 1 ≤ f) :
    ordTwistedF4 (2 ^ e) ≠ ordA r (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := exc_vs_ordA (a := 12) (b := 12) hr hf he (profile_ordTwistedF4' he)
    (Or.inl ⟨⟨1, by ring⟩, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h | ⟨h, -⟩ | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (by omega) h
  obtain rfl : r = 2 := by omega
  rcases hZ (by omega) with ⟨h', -⟩ | h' | ⟨h', -⟩ | h'
  · rw [show 2 * (e * 6) = e * 12 by ring] at h'
    have := dvd_of_rel_top hf h2 h'
    norm_num at this
  · have := dvd_of_rel_top hf h2 h'
    norm_num at this
  · rw [show 2 * (e * 3) = e * 6 by ring] at h'
    have := dvd_of_rel_top hf h2 h'
    norm_num at this
  · rw [← mul_one e] at h'
    have := dvd_of_rel_top hf h2 h'
    norm_num at this

theorem ordF4_ne_ordA {e r f : ℕ} (he : 1 ≤ e) (hr : 2 ≤ r) (hf : 1 ≤ f) :
    ordF4 (2 ^ e) ≠ ordA r (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := exc_vs_ordA (a := 24) (b := 12) hr hf he (profile_ordF4' he)
    (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (by omega) h
  obtain rfl : r = 4 := by omega
  rcases hZ (by omega) with h' | h' | h' | h' <;>
  · have := dvd_of_rel_top hf h2 h'
    norm_num at this

theorem ordE6_ne_ordA {e r f : ℕ} (he : 1 ≤ e) (hr : 2 ≤ r) (hf : 1 ≤ f) :
    ordE6 (2 ^ e) ≠ ordA r (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := exc_vs_ordA (a := 36) (b := 12) hr hf he (profile_ordE6' he)
    (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (by omega) h
  obtain rfl : r = 6 := by omega
  rcases hZ (by omega) with h' | h' | h' | h' | h' | h' <;>
  · have := dvd_of_rel_top hf h2 h'
    norm_num at this

theorem ordTwistedE6_ne_ordA {e r f : ℕ} (he : 1 ≤ e) (hr : 2 ≤ r) (hf : 1 ≤ f) :
    ordTwistedE6 (2 ^ e) ≠ ordA r (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := exc_vs_ordA (a := 36) (b := 18) hr hf he (profile_ordTwistedE6' he)
    (Or.inr (Or.inl ⟨⟨1, by ring⟩, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩))
    (fun k hk => by
      rcases hk with h | ⟨h, -⟩ | h | h | ⟨h, -⟩ | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (by omega) h
  obtain rfl : r = 4 := by omega
  rcases hZ (by omega) with h' | ⟨h', -⟩ | h' | h' | ⟨h', -⟩ | h'
  · have := dvd_of_rel_top hf h2 h'
    norm_num at this
  · rw [show 2 * (e * 9) = e * 18 by ring] at h'
    have := dvd_of_rel_top hf h2 h'
    norm_num at this
  · have := dvd_of_rel_top hf h2 h'
    norm_num at this
  · have := dvd_of_rel_top hf h2 h'
    norm_num at this
  · rw [show 2 * (e * 5) = e * 10 by ring] at h'
    have := dvd_of_rel_top hf h2 h'
    norm_num at this
  · have := dvd_of_rel_top hf h2 h'
    norm_num at this

theorem ordE7_ne_ordA {e r f : ℕ} (he : 1 ≤ e) (hr : 2 ≤ r) (hf : 1 ≤ f) :
    ordE7 (2 ^ e) ≠ ordA r (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := exc_vs_ordA (a := 63) (b := 18) hr hf he (profile_ordE7' he)
    (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (by omega) h
  obtain rfl : r = 7 := by omega
  rcases hZ (by omega) with h' | h' | h' | h' | h' | h' | h' <;>
  · have := dvd_of_rel_top hf h2 h'
    norm_num at this

theorem ordE8_ne_ordA {e r f : ℕ} (he : 1 ≤ e) (hr : 2 ≤ r) (hf : 1 ≤ f) :
    ordE8 (2 ^ e) ≠ ordA r (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := exc_vs_ordA (a := 120) (b := 30) hr hf he (profile_ordE8' he)
    (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h | h | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    (by omega) h
  obtain rfl : r = 8 := by omega
  rcases hZ (by omega) with h' | h' | h' | h' | h' | h' | h' | h' <;>
  · have := dvd_of_rel_top hf h2 h'
    norm_num at this

theorem ordSuzuki_ne_ordA {e r f : ℕ} (he : 1 ≤ e) (hr : 2 ≤ r) (hf : 1 ≤ f) :
    ordSuzuki (2 ^ e) ≠ ordA r (2 ^ f) := by
  intro h
  have hX := profile_ordSuzuki' he
  rcases Nat.lt_or_ge 1 e with he2 | he1
  · have := (exc_vs_ordA (a := 2) (b := 4) hr hf he hX
      (Or.inl ⟨⟨1, by ring⟩, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩)
      (fun k hk => by
        rcases hk with ⟨h, -⟩ | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega))
      (by omega) h).1
    omega
  · have hN := vsA_two (by omega) hf hX h
    have h3 := three_le_tri hr
    have : r * (r + 1) / 2 ≤ f * (r * (r + 1) / 2) := Nat.le_mul_of_pos_left _ hf
    omega

theorem ordTits_ne_ordA {r f : ℕ} (hr : 2 ≤ r) (hf : 1 ≤ f) : ordTits ≠ ordA r (2 ^ f) := by
  rw [ordTits_eq]
  refine fun h => (profile_idxA (by omega : 1 ≤ r) hf).ne_of_ne (by decide) ?_ h.symm
  rcases Nat.lt_or_ge r 5 with hr5 | hr5
  · interval_cases r <;> omega
  · have : 5 * 6 ≤ r * (r + 1) := Nat.mul_le_mul hr5 (by omega)
    have : r * (r + 1) / 2 ≤ f * (r * (r + 1) / 2) := Nat.le_mul_of_pos_left _ hf
    omega

theorem evenLieOrder_eq_ordA {t : StatedLieTag} {n g r f : ℕ}
    (hadm : StatedLieAdmissible t n 2 g) (hr : 2 ≤ r) (hf : 1 ≤ f)
    (h : F4Pilot.evenLieOrder t n g = ordA r (2 ^ f)) :
    t = .PSL ∧ ((n = r + 1 ∧ g = f) ∨ (n = 4 ∧ g = 1 ∧ r = 2 ∧ f = 2) ∨
      (n = 3 ∧ g = 2 ∧ r = 3 ∧ f = 1)) := by
  obtain ⟨-, hg, ht⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hn, -⟩ := ht
    refine ⟨rfl, ?_⟩
    rcases ordA_eq_ordA (s := n - 1) (by omega) hg hr hf h with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ |
      ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨by omega, h2⟩
    · exact Or.inr (Or.inl ⟨by omega, h2, h3, h4⟩)
    · exact Or.inr (Or.inr ⟨by omega, h2, h3, h4⟩)
  case PSU =>
    exact absurd h.symm (ordA_ne_ordTwistedA (by omega) hf (by obtain ⟨hn, -⟩ := ht; omega) hg)
  case PSp => exact absurd h (ordBC_ne_ordA ht.1 hg hr hf)
  case POmegaOdd => exact absurd rfl ht.2
  case POmegaPlus => exact absurd h (ordD_ne_ordA ht hg hr hf)
  case POmegaMinus => exact absurd h (ordTwistedD_ne_ordA ht hg hr hf)
  case G2 => exact absurd h (ordG2_ne_ordA hg hr hf)
  case F4 => exact absurd h (ordF4_ne_ordA hg hr hf)
  case E6 => exact absurd h (ordE6_ne_ordA hg hr hf)
  case E7 => exact absurd h (ordE7_ne_ordA hg hr hf)
  case E8 => exact absurd h (ordE8_ne_ordA hg hr hf)
  case twistedE6 => exact absurd h (ordTwistedE6_ne_ordA hg hr hf)
  case trialityD4 => exact absurd h (ordTrialityD4_ne_ordA hg hr hf)
  case twistedB2 => exact absurd h (ordSuzuki_ne_ordA hg hr hf)
  case twistedG2 => exact absurd ht.2.1 (by norm_num)
  case twistedF4 => exact absurd h (ordTwistedF4_ne_ordA hg hr hf)
  case Tits => exact absurd h (ordTits_ne_ordA hr hf)

end CFSG.SeitzReduction.LinearPilot
