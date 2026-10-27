module

public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Section

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

variable {G : Type} [Group G]

theorem oddCore_eq_pPrimeCore_two (Y : Type*) [Group Y] :
    CFSG.oddCore Y = CFSG.pPrimeCore 2 Y := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem outerSection_oddCore_eq_bot [Finite G] {v : G} (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hH : CFSG.oddCore ↥(centralizer ({v} : Set G)) = ⊥) :
    CFSG.oddCore (OuterSection v) = ⊥ := by
  have hp : IsPGroup 2 (vSub v) := IsPGroup.of_card (n := 1) (by rw [card_vSub hv2 hv1]; simp)
  rw [oddCore_eq_pPrimeCore_two, CFSG.central_p_subgroup_prime_core_quotient (vSub v)
    (vSub_le_center v) hp, ← oddCore_eq_pPrimeCore_two, hH, Subgroup.map_bot]

end CFSG.EvenSporadicStandard.HSStd
