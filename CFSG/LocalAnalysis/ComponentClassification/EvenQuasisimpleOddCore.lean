module

public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

open CFSG.Open

namespace CFSG.ComponentClassification.EvenQuasisimpleOddCore

theorem le_center {G : Type*} [Group G] [Finite G] (hquasisimple : IsQuasisimple G)
    (heven : Even (Nat.card G)) : componentClassificationOddCore G ≤ Subgroup.center G := by
  let : (componentClassificationOddCore G).Characteristic := OddCore.characteristic G
  apply Quasisimple.normal_le_center_of_ne_top hquasisimple
  intro htop
  have hodd := OddCore.odd_card G
  rw [htop, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) heven

end CFSG.ComponentClassification.EvenQuasisimpleOddCore
