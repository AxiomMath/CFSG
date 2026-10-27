module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMK1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMK3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G}

theorem OuterS16Hyp.card_cent_zbar
    (h : OuterS16Hyp G L z t T E Q x B β) :
    Nat.card ↥(centralizer ({(QuotientGroup.mk (⟨z, h.z_mem_cent_beta⟩ :
      ↥(centralizer ({β} : Set G))) : ↥(centralizer ({β} : Set G)) ⧸
        fusionOddCore ↥(centralizer ({β} : Set G)))} : Set (↥(centralizer ({β} : Set G)) ⧸
          fusionOddCore ↥(centralizer ({β} : Set G))))) = 1440 :=
  h.m10Config.card_centralizer_bar

theorem OuterS16Hyp.Dbar_le_cent_zbar
    (h : OuterS16Hyp G L z t T E Q x B β) :
    ((L ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G))).map
      (QuotientGroup.mk' (fusionOddCore ↥(centralizer ({β} : Set G)))) ≤
    centralizer ({(QuotientGroup.mk (⟨z, h.z_mem_cent_beta⟩ :
      ↥(centralizer ({β} : Set G))) : ↥(centralizer ({β} : Set G)) ⧸
        fusionOddCore ↥(centralizer ({β} : Set G)))} : Set (↥(centralizer ({β} : Set G)) ⧸
          fusionOddCore ↥(centralizer ({β} : Set G)))) :=
  h.m10Config.map_D_le

theorem OuterS16Hyp.Dbar_iso
    (h : OuterS16Hyp G L z t T E Q x B β) :
    Nonempty (↥(((L ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G))).map
      (QuotientGroup.mk' (fusionOddCore ↥(centralizer ({β} : Set G))))) ≃*
        alternatingGroup (Fin 6)) :=
  h.m10Config.map_D_iso

theorem OuterS16Hyp.Fbar
    (h : OuterS16Hyp G L z t T E Q x B β) :
    ((E ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G))) ≤
        (L ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G)) ∧
      Nat.card ↥(((E ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G))).map
        (QuotientGroup.mk' (fusionOddCore ↥(centralizer ({β} : Set G))))) = 8 ∧
      ((E ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G))).map
        (QuotientGroup.mk' (fusionOddCore ↥(centralizer ({β} : Set G)))) ≤
      ((L ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G))).map
        (QuotientGroup.mk' (fusionOddCore ↥(centralizer ({β} : Set G)))) ∧
      Nat.card ↥(((L ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G))).map
        (QuotientGroup.mk' (fusionOddCore ↥(centralizer ({β} : Set G))))) = 360 := by
  have hM := h.m10Config
  have hFD : ((E ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G))) ≤
      (L ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G)) := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact ⟨h.outerE.E_le_L hk.1, hk.2⟩
  have hF8 : Nat.card ↥((E ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G))) =
      8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      E ⊓ centralizer ({β} : Set G) ≤ centralizer ({β} : Set G))).toEquiv]
    exact h.cardEβ
  have hF2 : IsPGroup 2 ↥((E ⊓ centralizer ({β} : Set G)).subgroupOf
      (centralizer ({β} : Set G))) := IsPGroup.of_card (n := 3) (by rw [hF8]; norm_num)
  refine ⟨hFD, ?_, Subgroup.map_mono hFD, ?_⟩
  · rw [hM.card_map_two hFD hF2, hF8]
  · obtain ⟨e⟩ := hM.map_D_iso
    rw [Nat.card_congr e.toEquiv]
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide

end CFSG.EvenSporadicStandard.Fin76b
