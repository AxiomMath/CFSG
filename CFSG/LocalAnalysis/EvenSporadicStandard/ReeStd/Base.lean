module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Base
import CFSG.Walter.J1Props.Elt
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Local

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.J1Std CFSG.EvenSporadicStandard.J1Std.WalterArith

theorem seven_dvd_card {G : Type} [Group G] [Finite G] (L : LocalSetting (G := G)) :
    7 ∣ Nat.card G := by
  have h7range : 7 ∣ Nat.card L.actB.range := by
    rw [L.card_range_B]
    norm_num
  exact (h7range.trans (Subgroup.card_range_dvd L.actB)).trans
    (Subgroup.card_subgroup_dvd_card L.B)

theorem base_not_sylow_local {G : Type} [Group G] [Finite G] (hW : WalterAbelian)
    (H : LocalSetting G) : 2 ∣ H.V.index := by
  by_contra hidx
  haveI : IsSimpleGroup G := H.simple
  have hVp : IsPGroup 2 H.V := H.pgroup_V
  have hcomm : IsMulCommutative (hVp.toSylow hidx : Subgroup G) :=
    ⟨⟨fun a b => Subtype.ext (H.V_comm a.2 b.2)⟩⟩
  have hcard : Nat.card G = 16 * H.V.index := by
    rw [← Subgroup.card_mul_index H.V, H.card_V]
  have h7 : 7 ∣ Nat.card G := seven_dvd_card H
  rcases hW G H.nonabelian (hVp.toSylow hidx) hcomm with ⟨f, hf, ⟨e⟩⟩ |
      ⟨p, f, hp, hpodd, hf0, -, hmod, ⟨e⟩⟩ | ⟨m, -, hree⟩ | hJ
  · refine false_of_card_psl2_two_pow hf (by omega) (hcard ▸ h7) ?_
    rw [← hcard, Nat.card_congr e.toEquiv, card_psl2_two_pow (by omega)]
  · obtain ⟨r, hr, hqr⟩ := exists_eight_mul_odd hmod
    have h := card_psl2_odd_mul_two hpodd (by omega : f ≠ 0)
    rw [← Nat.card_congr e.toEquiv, hcard, hqr] at h
    obtain ⟨j, rfl⟩ := hr
    omega
  · exact not_sixteen_dvd_ordRee m ⟨H.V.index, hree.symm.trans hcard⟩
  · obtain ⟨e⟩ := hJ
    have : Nat.card G = 175560 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Walter.J1Props.card_walterJ1
    omega

end CFSG.EvenSporadicStandard.ReeStd
