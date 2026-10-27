module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXKlSpin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrLift
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBDInputs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrFacts

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Kl

open CFSG Subgroup CFSG.LieType.Universal.Spin CFSG.ComponentClassification.Burgoyne
open CFSG.ComponentClassification.Burgoyne.DX.Dr
open CFSG.LieType.Steinberg.CentralExt

theorem burgoynePropBSpinPlusKleinInput_holds : BurgoynePropBSpinPlusKleinInput := by
  intro F _ _ hF n hn _ L _ _ α hα c hII
  have hS := spinFacts_quadPlus hF (by omega : 3 ≤ n)
  have : Finite (spinGroup (quadPlus n F)) := hS.finite
  have : Group.IsPerfect (spinGroup (quadPlus n F)) := hS.perfect
  have hq := isQuasisimple_spinGroup_quadPlus (K := F) (by omega : 3 ≤ n)
  obtain ⟨s, hs2, Q, hQs, hQc, ⟨p₁, n₁, _, hp₁, hn₁, ⟨e⟩⟩, hcZ, hcQ, hc2⟩ := id hII
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hnt : ∃ k, α k ≠ 1 := by
    obtain ⟨k, hk⟩ := hα c
    exact ⟨k, by rw [hk]; exact hc1⟩
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hnt
  have hker2 : IsPGroup 2 α.ker := hS.center2.to_le hker
  have hF₁ : ringChar (GaloisField p₁ n₁) ≠ 2 := by
    rw [ringChar.eq (GaloisField p₁ n₁) p₁]
    exact hp₁
  have hQQ : ⁅Q, Q⁆ = Q := C.commutator_eq_of_isPComponent hQs hQc
  obtain ⟨hTQ, -, hinj⟩ := perfectLift_spec α hα hker hker2 hQQ hF₁ e
  obtain ⟨x₀, hx₀T, hαx₀, hx₀Z, hx₀2⟩ := exists_central_lift α hker hTQ hinj hcZ hcQ hc2
  by_cases hx₀n : x₀ = negOneR hS
  · rw [← hαx₀, hx₀n]
  · exact (false_of_propBHypII_spin hF (by omega) hS hx₀Z hx₀2 hx₀n
      (propBHypII_lift hS.split α hα hker hker2 hs2 hQs hQc hp₁ hn₁ e hx₀T hx₀Z hx₀2)).elim

end CFSG.ComponentClassification.Burgoyne.DX.Kl
