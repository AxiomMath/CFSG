module

public import CFSG.Dihedral.BlueprintDefs
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public noncomputable section

namespace CFSG.DihedralBlueprint

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddCoreOf_le (H : Subgroup G) : oddCoreOf H ≤ H :=
  Subgroup.map_subtype_le _

theorem oddCoreOf_odd (H : Subgroup G) : Odd (Nat.card (oddCoreOf H)) := by
  rw [oddCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
  exact DisconnectedInvolutionGraph.Helpers.oddCore_odd

omit [Finite G] in
theorem oddCoreOf_normal (H : Subgroup G) : ((oddCoreOf H).subgroupOf H).Normal := by
  have heq : (oddCoreOf H).subgroupOf H = Assembly.oddCore H := by
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [heq]
  infer_instance

omit [Finite G] in
theorem oddCoreOf_normalized (H : Subgroup G) : NormalizedBy (oddCoreOf H) H := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (oddCoreOf_le H)).mp
    (oddCoreOf_normal H)

omit [Finite G] in
theorem normal_odd_le_oddCoreOf (R H : Subgroup G) (hRH : R ≤ H)
    (hR : (R.subgroupOf H).Normal) (hodd : Odd (Nat.card R)) : R ≤ oddCoreOf H := by
  have hodd' : Odd (Nat.card (R.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv]
  have hle : R.subgroupOf H ≤ Assembly.oddCore H := le_sSup ⟨hR, hodd'⟩
  have hm := Subgroup.map_mono (f := H.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hRH] at hm

omit [Finite G] in
theorem odd_le_normal_of_two_quotient (W H : Subgroup G) (hWH : W ≤ H)
    (J : Subgroup H) [J.Normal] (hodd : Odd (Nat.card W))
    (hquot : IsPGroup 2 (H ⧸ J)) : W ≤ J.map H.subtype := by
  let f := QuotientGroup.mk' J
  let U := (W.subgroupOf H).map f
  have hUodd : Odd (Nat.card U) := by
    have hodd' : Odd (Nat.card (W.subgroupOf H)) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv]
    exact hodd'.of_dvd_nat ((W.subgroupOf H).card_map_dvd f)
  have hUp : IsPGroup 2 U := hquot.to_subgroup U
  have hUcard : Nat.card U = 1 := by
    rcases hUp.card_eq_or_dvd with hone | htwo
    · exact hone
    · exact (hUodd.not_two_dvd_nat htwo).elim
  have hUbot : U = ⊥ := (Subgroup.eq_bot_iff_card U).mpr hUcard
  intro x hx
  have hfx : f (⟨x, hWH hx⟩ : H) = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hUbot]
    exact Subgroup.mem_map_of_mem f hx
  have hJ : (⟨x, hWH hx⟩ : H) ∈ J := by
    exact (QuotientGroup.eq_one_iff _).mp hfx
  exact Subgroup.mem_map.mpr ⟨⟨x, hWH hx⟩, hJ, rfl⟩

end CFSG.DihedralBlueprint
