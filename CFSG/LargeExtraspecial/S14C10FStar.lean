module

public import CFSG.LargeExtraspecial.BridgeSetting
import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open

theorem fstar_eq_subgroupOf {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    {H : Subgroup K} [H.Normal] (hp : IsPGroup p (timmesfeldFStar K))
    (hle : timmesfeldFStar K ≤ H) :
    timmesfeldFStar H = (timmesfeldFStar K).subgroupOf H := by
  have hNn : (timmesfeldFStar K).Normal := timmesfeldFStar_normal K
  have hN'n : ((timmesfeldFStar K).subgroupOf H).Normal := hNn.subgroupOf H
  have hN'p : IsPGroup p ((timmesfeldFStar K).subgroupOf H) :=
    hp.of_equiv (subgroupOfEquivOfLe hle).symm
  have hN'le : (timmesfeldFStar K).subgroupOf H ≤ CFSG.pCore p H := le_sSup ⟨hN'n, hN'p⟩
  have hcent : centralizer (timmesfeldFStar K : Set K) ≤ timmesfeldFStar K :=
    CFSG.Adapters.centralizer_timmesfeldFStar_le K
  have hchar : CFSG.IsCharacteristicP p H := by
    intro x hx
    refine hN'le (mem_subgroupOf.mpr (hcent (mem_centralizer_iff.mpr fun n hn => ?_)))
    have h1 := mem_centralizer_iff.mp hx ⟨n, hle hn⟩ (hN'le (mem_subgroupOf.mpr hn))
    exact congrArg Subtype.val h1
  have hF : timmesfeldFStar H = CFSG.pCore p H := by
    rw [← Bridge.generalizedFitting_eq_timmesfeldFStar]
    exact (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore H p).mp hchar
  rw [hF]
  refine le_antisymm (fun x hx => ?_) hN'le
  have hmapn : ((CFSG.pCore p H).map H.subtype).Normal := inferInstance
  have hmapp : IsPGroup p ((CFSG.pCore p H).map H.subtype) :=
    CFSG.pCore_isPGroup.map H.subtype
  have hnil : Group.IsNilpotent ((CFSG.pCore p H).map H.subtype) := hmapp.isNilpotent
  have hle' : (CFSG.pCore p H).map H.subtype ≤ timmesfeldFStar K :=
    (le_sSup ⟨hmapn, hnil⟩ : _ ≤ timmesfeldFitting K).trans le_sup_left
  exact mem_subgroupOf.mpr (hle' ⟨x, hx, rfl⟩)

theorem map_fstar_eq_of_le {Y : Type} [Group Y] {K H : Subgroup Y} [Finite K] {p : ℕ}
    [Fact p.Prime] (hHK : H ≤ K) (hnorm : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H)
    (hp : IsPGroup p (timmesfeldFStar K)) (hle : (timmesfeldFStar K).map K.subtype ≤ H) :
    (timmesfeldFStar H).map H.subtype = (timmesfeldFStar K).map K.subtype := by
  have hn : (H.subgroupOf K).Normal := ⟨fun h hh k => by
    rw [mem_subgroupOf] at hh ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hnorm k k.2 h hh⟩
  have hle' : timmesfeldFStar K ≤ H.subgroupOf K := fun x hx =>
    mem_subgroupOf.mpr (hle ⟨x, hx, rfl⟩)
  have h1 := fstar_eq_subgroupOf hp hle'
  set e := subgroupOfEquivOfLe hHK
  have h2 := Bridge.timmesfeldFStar_map e
  have h3 : H.subtype.comp e.toMonoidHom = K.subtype.comp (H.subgroupOf K).subtype := rfl
  rw [← h2, h1, map_map, h3, ← map_map, subgroupOf_map_subtype, inf_eq_left.mpr hle']

end CFSG.LargeExtraspecial.S14
