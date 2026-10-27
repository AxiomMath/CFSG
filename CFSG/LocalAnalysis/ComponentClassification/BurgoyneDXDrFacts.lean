module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrSpin
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCenter

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Dr

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LieType.Steinberg.CentralExt

variable {F : Type} [Field F] [Finite F]

theorem isPGroup_two_of_card_dvd_four {G : Type*} [Group G] {H : Subgroup G}
    (h : Nat.card H ∣ 4) : IsPGroup 2 H := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (by simpa using h : Nat.card H ∣ 2 ^ 2)
  exact IsPGroup.of_card hk

section Plus

variable {n : ℕ}

omit [Finite F] in
theorem center_quadPlus (hn : 3 ≤ n) :
    center (spinGroup (quadPlus n F)) = SpinPlusClosed.scalarSpin n F :=
  (spinToStatedProj_quadPlus hn).2.2.symm.trans (spinToStatedProj_quadPlus hn).2.1

omit [Finite F] in
theorem isCyclic_center_quadPlus (hF : ringChar F ≠ 2) (hn : 3 ≤ n) (ho : Odd n) :
    IsCyclic (center (spinGroup (quadPlus n F))) ∧
      Nat.card (center (spinGroup (quadPlus n F))) ∣ 4 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rw [center_quadPlus hn]
  by_cases hsq : IsSquare (-1 : F)
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      exact one_ne_zero (neg_eq_zero.1 hr)
    have hι : Units.mk0 r hr0 ^ 2 = -1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, pow_two, ← hr, Units.val_neg, Units.val_one])
    obtain ⟨hc4, hcy⟩ := SpinPlusClosed.card_scalarSpin_of_isSquare hn h2 ho hι
    exact ⟨hcy, by rw [hc4]⟩
  · have hc2 := SpinPlusClosed.card_scalarSpin_of_not_isSquare hn h2 ho hsq
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact ⟨isCyclic_of_prime_card hc2, by rw [hc2]; norm_num⟩

omit [Finite F] in
theorem card_center_quadPlus_dvd (hF : ringChar F ≠ 2) (hn : 3 ≤ n) :
    Nat.card (center (spinGroup (quadPlus n F))) ∣ 4 := by
  rcases Nat.even_or_odd n with he | ho
  · rw [center_quadPlus hn,
      (SpinPlusClosed.isKleinFour_scalarSpin hn (Ring.two_ne_zero hF) he).card_four]
  · exact (isCyclic_center_quadPlus hF hn ho).2

theorem spinFacts_quadPlus (hF : ringChar F ≠ 2) (hn : 3 ≤ n) :
    SpinFacts (quadPlus n F) (StatedQuadPlus n F) := by
  have : NeZero n := ⟨by omega⟩
  exact
  { coe := coe_quadPlus n F
    range := range_spinMatrix_quadPlus hn
    ne_zero := (nondegenerate_quadPlus n F).ne_zero
    ker := mem_ker_spinMatrix_quadPlus_iff
    nondeg := nondegenerate_quadPlus n F
    rad := fun v hv => (nondegenerate_polarBilin_quadPlus n F).1 v fun w => by simpa using hv w
    finite := CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (coe_ker_spinMatrix_quadPlus (n := n))
    perfect := isPerfect_spinGroup_quadPlus hn
    surj := (spinToStatedProj_quadPlus hn).1
    kerP := (spinToStatedProj_quadPlus hn).2.2
    split := fun E _ _ π hπ hker2 h2' => by
      obtain ⟨s, hs, -⟩ :=
        CFSG.LieType.Steinberg.spinPlus_central_two_extension_splitting hn hF hπ hker2 h2'
      exact ⟨s, hs⟩
    center2 := isPGroup_two_of_card_dvd_four (card_center_quadPlus_dvd hF hn) }

end Plus

section Minus

variable {n : ℕ} {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem center_quadMinus (hn : 4 ≤ n) :
    center (spinGroup (quadMinus n F b c)) = SpinMinusClosed.scalarSpinM n F b c :=
  (spinToStatedProj_quadMinus hn hirr).2.2.symm.trans (spinToStatedProj_quadMinus hn hirr).2.1

include hirr in
theorem isCyclic_center_quadMinus (hn : 4 ≤ n) {p f : ℕ} (hK : Nat.card F = p ^ f) :
    IsCyclic (center (spinGroup (quadMinus n F b c))) ∧
      Nat.card (center (spinGroup (quadMinus n F b c))) ∣ 4 := by
  rw [center_quadMinus hirr hn]
  obtain ⟨hcard, hcy⟩ := SpinMinusClosed.card_scalarSpinM hirr hn hK
  exact ⟨hcy, by rw [hcard]; exact Nat.gcd_dvd_left _ _⟩

include hirr in
theorem spinFacts_quadMinus (hF : ringChar F ≠ 2) (hn : 4 ≤ n) {p f : ℕ}
    (hK : Nat.card F = p ^ f) : SpinFacts (quadMinus n F b c) (StatedQuadMinus n F b c) where
  coe := coe_quadMinus n F b c
  range := range_spinMatrix_quadMinus hn hirr
  ne_zero := (nondegenerate_quadMinus_of_finite n F hirr).ne_zero
  ker := mem_ker_spinMatrix_quadMinus_iff hirr
  nondeg := nondegenerate_quadMinus_of_finite n F hirr
  rad := fun v hv => (nondegenerate_polarBilin_quadMinus_of_finite n F hirr).1 v fun w => by
    simpa using hv w
  finite := CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
    (coe_ker_spinMatrix_quadMinus (n := n) hirr)
  perfect := isPerfect_spinGroup_quadMinus hn hirr
  surj := (spinToStatedProj_quadMinus hn hirr).1
  kerP := (spinToStatedProj_quadMinus hn hirr).2.2
  split := fun E _ _ π hπ hker2 h2' => by
    obtain ⟨s, hs, -⟩ :=
      CFSG.LieType.Steinberg.spinMinus_central_two_extension_splitting hn hF hirr hπ hker2 h2'
    exact ⟨s, hs⟩
  center2 := isPGroup_two_of_card_dvd_four (isCyclic_center_quadMinus hirr hn hK).2

end Minus

end CFSG.ComponentClassification.Burgoyne.DX.Dr
