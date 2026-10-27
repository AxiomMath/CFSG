module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GDefs
public import CFSG.Goldschmidt.OddCore
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

theorem sec5g8_normalClosure_bar {X : Type} [Group X] [Finite X] (P : Sylow 2 X) {Tb : Subgroup X}
    (hle : Tb ≤ (P : Subgroup X)) (hSC : fusionStronglyClosed (Tb : Set X) (P : Subgroup X)) :
    normalClosure ((Sec5GImg Tb : Subgroup (Sec5GBar Tb)) : Set (Sec5GBar Tb)) = ⊤ := by
  have htop := CFSG.Goldschmidt.normalClosure_subgroupOf_eq_top (A := Tb) P hle hSC
    (M := Subgroup.normalClosure (Tb : Set X)) rfl
  have hmap := CFSG.Goldschmidt.normalClosure_map_eq_top htop (sec5g_pi Tb)
    (QuotientGroup.mk'_surjective (N := goldschmidtOddCore ↥(normalClosure (Tb : Set X))))
  simpa only [Sec5GImg] using hmap

theorem sec5g8_oddCore_bar {X : Type} [Group X] [Finite X] (Tb : Subgroup X) :
    CFSG.oddCore (Sec5GBar Tb) = ⊥ := by
  have h : CFSG.oddCore (Sec5GBar Tb) = goldschmidtOddCore (Sec5GBar Tb) := rfl
  rw [h]
  exact CFSG.Goldschmidt.goldschmidtOddCore_quotient_eq_bot ↥(normalClosure (Tb : Set X))

end CFSG.OddStandard.SmallF3.Omega
