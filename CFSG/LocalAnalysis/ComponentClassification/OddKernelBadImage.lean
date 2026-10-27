module

public import CFSG.LocalAnalysis.ComponentClassification.OddKernelTwoComponents

public section

open CFSG.Open

namespace CFSG.ComponentClassification.OddKernelBadImage

theorem lower_image {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) :
    TwoComponents.badSubgroup H ≤ (TwoComponents.badSubgroup G).map quotient := by
  apply sSup_le
  intro component hbad
  obtain ⟨lift, hlift, hmap⟩ := OddKernelTwoComponents.exists_lift quotient hsurjective
    hoddKernel component hbad.1
  have hnotQuasisimple : ¬ IsQuasisimple lift := by
    intro hquasisimple
    have hnotKilled : ¬ lift ≤ quotient.ker := by
      intro hcontained
      have hbot : lift.map quotient = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hcontained
      rw [hmap] at hbot
      let : Nontrivial component := TwoComponents.nontrivial hbad.1
      exact (component.nontrivial_iff_ne_bot.mp inferInstance) hbot
    have himage := LocalComponents.image ⟨le_top, hlift.1, hquasisimple⟩
      quotient hsurjective hnotKilled
    rw [hmap] at himage
    exact hbad.2 himage.2.2
  rw [← hmap]
  exact Subgroup.map_mono (le_sSup ⟨hlift, hnotQuasisimple⟩)

end CFSG.ComponentClassification.OddKernelBadImage
