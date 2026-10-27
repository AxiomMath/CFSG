module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamTools
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

private theorem not_dvd_orderTits {r : ℕ} (hr : Odd r) (hr1 : 1 < r) :
    ¬ (2 ^ r * ((2 ^ r) ^ 2 - 1) ∣ orderTits) := by
  intro h
  have h2 : 2 ^ r ∣ orderTits := (dvd_mul_right _ _).trans h
  have hr11 : r ≤ 11 := by
    by_contra hlt
    have h12 : 2 ^ 12 ∣ orderTits := (pow_dvd_pow 2 (by omega : 12 ≤ r)).trans h2
    revert h12
    unfold orderTits
    decide
  obtain ⟨k, rfl⟩ := hr
  have hk1 : 1 ≤ k := by omega
  have hk5 : k ≤ 5 := by omega
  revert h
  unfold orderTits
  interval_cases k <;> decide

section Certified

set_option linter.unusedSectionVars false


theorem censusBodyTits : CensusBodyTits := by
  intro hv η _ _ _ r hr hr1 J₁ J₂ J₃ _ _ _ _ _ _ hL1 _ _
  exfalso
  haveI := (CFSG.Assembly.lie_finite_simple ⟨TauCeti.LieTypeIndex.tits, hv⟩).1
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hr) even_two
  obtain ⟨-, hcard⟩ := card_of_catalogIs_isL2n_of_ne_two hr2 hL1
  have hS : Nat.card (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.tits, hv⟩).Group = orderTits :=
    CatDistinct.ctx_holds.bridge ⟨.tits, hv⟩ _ ⟨MulEquiv.refl _⟩
  have hdvd := card_quot_center_dvd_card J₁
  rw [hcard, hS] at hdvd
  exact not_dvd_orderTits hr hr1 hdvd

end Certified

end CFSG.LocalAnalysis.GLTheoremA.T1428
