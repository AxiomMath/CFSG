module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.YExists
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.YElem
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.WeakData
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.MFusionLemma
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.EgawaApply

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup

theorem false_of_localData {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hA : M24Std.Ega81HypAZ2A8K) (hE : Ega81M24Section)
    (hKS : M24Std.KLocalSections G) {L U T0 : Subgroup G} {z p q u0 : G} (hS : Setting L z)
    (hD : LocalData L U T0) (hD11 : LocalData11 L U p q u0) (hM : ModData L U) : False := by
  have htrans := trans_of_simple hnonab hS hD
  have hW23 := card_Csub hnonab hS hD hD11
  obtain ⟨Y, hY, hYab⟩ := exists_Y hnonab hS hD hD11 hM
  have hYsq := Y_sq hnonab hS hD hD11 hM hY hYab
  have hR := rankData_of hS hD
  have hW := weakData_of hS hD hY hR hYsq hYab hW23
  have hF := fusionData_of hS hD htrans hY hR hW
  exact false_of_fusionData hnonab hA hE hKS hS hD hM hY hW hF

end CFSG.EvenSporadicStandard.J4Std
