module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcOrders
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDetOrders

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.SeitzReduction.F4Pilot (idxD idx2D profile_idxD profile_idx2D)
open CFSG.SeitzReduction.F4Pilot.EvenExc (profile_ordG2' profile_ordF4' profile_ordE6'
  profile_ordTwistedE6' profile_ordE8' profile_ordTrialityD4' profile_ordSuzuki'
  profile_ordTwistedF4')

theorem ordG2_ne_ordTwistedD {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordG2 (2 ^ e) ≠ ordTwistedD m (2 ^ f) := by
  intro h
  obtain ⟨h1, -, -⟩ := vs2D_rank (a := 6) (b := 6) hm hf he (profile_ordG2' he) (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega)) h
  omega

theorem ordF4_ne_ordTwistedD {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordF4 (2 ^ e) ≠ ordTwistedD m (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := vs2D_rank (a := 24) (b := 12) hm hf he (profile_ordF4' he)
    (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega)) h
  obtain rfl : m = 5 := by omega
  have hrel : 6 * e = 5 * f := by omega
  have hk : idx2D 5 f (f * 8) := Or.inr ⟨4, by decide, by norm_num⟩
  rcases (hZ (f * 8) (by omega) (by omega)).mpr hk with h' | h' | h' | h' <;>
  · have := dvd_of_rel (by omega : 0 < f) hrel h'
    norm_num at this

theorem ordE6_ne_ordTwistedD {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordE6 (2 ^ e) ≠ ordTwistedD m (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := vs2D_rank (a := 36) (b := 12) hm hf he (profile_ordE6' he)
    (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega)) h
  obtain rfl : m = 7 := by omega
  have hrel : 6 * e = 7 * f := by omega
  have hk : idx2D 7 f (f * 12) := Or.inr ⟨6, by decide, by norm_num⟩
  rcases (hZ (f * 12) (by omega) (by omega)).mpr hk with h' | h' | h' | h' | h' | h' <;>
  · have := dvd_of_rel (by omega : 0 < f) hrel h'
    norm_num at this

theorem ordTwistedE6_ne_ordTwistedD {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordTwistedE6 (2 ^ e) ≠ ordTwistedD m (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := vs2D_rank (a := 36) (b := 18) hm hf he (profile_ordTwistedE6' he)
    (Or.inr (Or.inl ⟨⟨1, by ring⟩, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩))
    (fun k hk => by
      rcases hk with h | ⟨h, -⟩ | h | h | ⟨h, -⟩ | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega)) h
  obtain rfl : m = 5 := by omega
  have hrel : 9 * e = 5 * f := by omega
  have hk : idx2D 5 f (f * 8) := Or.inr ⟨4, by decide, by norm_num⟩
  rcases (hZ (f * 8) (by omega) (by omega)).mpr hk with
    h' | ⟨h', -⟩ | h' | h' | ⟨h', -⟩ | h'
  · have := dvd_of_rel (by omega : 0 < f) hrel h'
    norm_num at this
  · rw [show 2 * (e * 9) = e * 18 by ring] at h'
    have := dvd_of_rel (by omega : 0 < f) hrel h'
    norm_num at this
  · have := dvd_of_rel (by omega : 0 < f) hrel h'
    norm_num at this
  · have := dvd_of_rel (by omega : 0 < f) hrel h'
    norm_num at this
  · rw [show 2 * (e * 5) = e * 10 by ring] at h'
    have := dvd_of_rel (by omega : 0 < f) hrel h'
    norm_num at this
  · have := dvd_of_rel (by omega : 0 < f) hrel h'
    norm_num at this

theorem ordE8_ne_ordTwistedD {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordE8 (2 ^ e) ≠ ordTwistedD m (2 ^ f) := by
  intro h
  obtain ⟨h1, h2, hZ⟩ := vs2D_rank (a := 120) (b := 30) hm hf he (profile_ordE8' he)
    (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h | h | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega)) h
  obtain rfl : m = 9 := by omega
  have hrel : 5 * e = 3 * f := by omega
  have hk : idx2D 9 f (f * 16) := Or.inr ⟨8, by decide, by norm_num⟩
  rcases (hZ (f * 16) (by omega) (by omega)).mpr hk with
    h' | h' | h' | h' | h' | h' | h' | h' <;>
  · have := dvd_of_rel (by omega : 0 < f) hrel h'
    norm_num at this

theorem ordTrialityD4_ne_ordTwistedD {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordTrialityD4 (2 ^ e) ≠ ordTwistedD m (2 ^ f) := by
  intro h
  obtain ⟨h1, -, -⟩ := vs2D_rank (a := 12) (b := 12) hm hf he (profile_ordTrialityD4' he)
    (Or.inl ⟨dvd_rfl, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega)) h
  omega

theorem ordSuzuki_ne_ordTwistedD {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordSuzuki (2 ^ e) ≠ ordTwistedD m (2 ^ f) := by
  intro h
  obtain ⟨h1, -, -⟩ := vs2D_rank (a := 2) (b := 4) hm hf he (profile_ordSuzuki' he)
    (Or.inl ⟨⟨1, by ring⟩, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega)) h
  omega

theorem ordTwistedF4_ne_ordTwistedD {e m f : ℕ} (he : 1 ≤ e) (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordTwistedF4 (2 ^ e) ≠ ordTwistedD m (2 ^ f) := by
  intro h
  obtain ⟨h1, -, -⟩ := vs2D_rank (a := 12) (b := 12) hm hf he (profile_ordTwistedF4' he)
    (Or.inl ⟨⟨1, by ring⟩, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h | ⟨h, -⟩ | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega)) h
  omega

theorem ordTits_ne_ordTwistedD {m f : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f) :
    ordTits ≠ ordTwistedD m (2 ^ f) := by
  rw [ordTits_eq]
  refine fun h => (profile_idx2D (by omega : 1 ≤ m) hf).ne_of_ne (by decide) ?_ h.symm
  have := (twelve_le_mul_rank hm hf).1
  omega

end CFSG.SeitzReduction.OmegaPilot
