module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5G8HN
public import CFSG.ClassicalInvolution.AschTight.MuZ2Final

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open CFSG.ClassicalInvolution.Disconnected.AschTight

theorem sec5g8_isSylowIn (hB3 : GoldschmidtB3Tmp) {X : Type} [Group X] [Finite X] (P : Sylow 2 X)
    {Tb : Subgroup X} (hle : Tb ≤ (P : Subgroup X)) (hD : Nonempty (↥Tb ≃* DihedralGroup 4))
    (hSC : fusionStronglyClosed (Tb : Set X) (P : Subgroup X)) :
    fusionIsSylowIn 2 Tb (normalClosure (Tb : Set X)) := by
  exact hB3 X P Tb hle hSC (sec5g8_hN hD)

theorem sec5g8_exists_sylow (hB3 : GoldschmidtB3Tmp) {X : Type} [Group X] [Finite X]
    (P : Sylow 2 X) {Tb : Subgroup X} (hle : Tb ≤ (P : Subgroup X))
    (hD : Nonempty (↥Tb ≃* DihedralGroup 4))
    (hSC : fusionStronglyClosed (Tb : Set X) (P : Subgroup X)) :
    ∃ Pm : Sylow 2 ↥(normalClosure (Tb : Set X)),
      (Pm : Subgroup ↥(normalClosure (Tb : Set X))) =
        Tb.subgroupOf (normalClosure (Tb : Set X)) := by
  classical
  let M := normalClosure (Tb : Set X)
  have hsyl : fusionIsSylowIn 2 Tb M := sec5g8_isSylowIn hB3 P hle hD hSC
  obtain ⟨hTbM, hTb2, hmax⟩ := hsyl
  have hT2 : IsPGroup 2 (Tb.subgroupOf M) := hTb2.comap_subtype
  obtain ⟨Pm, hTPm⟩ := hT2.exists_le_sylow
  refine ⟨Pm, ?_⟩
  have hmapM : (Pm : Subgroup ↥M).map M.subtype ≤ M := Subgroup.map_subtype_le _
  have hpgM : IsPGroup 2 ((Pm : Subgroup ↥M).map M.subtype) := Pm.isPGroup'.map M.subtype
  have hTbmap : Tb ≤ (Pm : Subgroup ↥M).map M.subtype := by
    intro t ht
    exact Subgroup.mem_map.mpr ⟨⟨t, hTbM ht⟩, hTPm ht, rfl⟩
  have hmapEq : (Pm : Subgroup ↥M).map M.subtype = Tb := hmax _ hmapM hpgM hTbmap
  have hTmap : (Tb.subgroupOf M).map M.subtype = Tb := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTbM]
  exact Subgroup.map_injective Subtype.coe_injective (by rw [hmapEq, hTmap])

end CFSG.OddStandard.SmallF3.Omega
