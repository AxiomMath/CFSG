module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.Basic
public import CFSG.LargeExtraspecial.S7Seven
public import CFSG.Adapters.WholeGroupLayer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.TriPlus

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S5 CFSG.LargeExtraspecial.S7

variable {G : Type*} [Group G] [Finite G]

theorem centralizer_oddCore_le (S : Setting G) (hE : timmesfeldLayer S.Mbar = ⊥)
    (h27 : Nat.card (timmesfeldOddCore S.Mbar) = 3 ^ 3) :
    centralizer (timmesfeldOddCore S.Mbar : Set S.Mbar) ≤ timmesfeldOddCore S.Mbar := by
  have hge : timmesfeldOddCore S.Mbar ≤ timmesfeldFitting S.Mbar := by
    refine le_sSup ⟨timmesfeldOddCore_normal S.Mbar, ?_⟩
    exact (IsPGroup.of_card (n := 3) h27).isNilpotent
  have hF : timmesfeldFStar S.Mbar = timmesfeldOddCore S.Mbar := by
    rw [timmesfeldFStar, hE, sup_bot_eq]
    exact le_antisymm (fitting_le_oddCore S) hge
  intro x hx
  rw [← hF] at hx ⊢
  exact CFSG.Adapters.centralizer_timmesfeldFStar_le (G := S.Mbar) hx

theorem mem_Obar_of_commute {S : Setting G} (hE : timmesfeldLayer S.Mbar = ⊥)
    (h27 : Nat.card (timmesfeldOddCore S.Mbar) = 3 ^ 3) {x : S.O} (hx : x ∈ S.Mbar)
    (hc : ∀ y ∈ S7.Obar S, x * y = y * x) : x ∈ S7.Obar S := by
  have hx' : (⟨x, hx⟩ : S.Mbar) ∈
      centralizer (timmesfeldOddCore S.Mbar : Set S.Mbar) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (hc (y : S.O) ⟨y, hy, rfl⟩).symm
  have h := centralizer_oddCore_le S hE h27 hx'
  exact ⟨⟨x, hx⟩, h, rfl⟩

theorem Mbar_le_normalizer_Obar (S : Setting G) :
    S.Mbar ≤ normalizer (S7.Obar S : Set S.O) := by
  intro x hx
  exact mem_normalizer_of_conj_le fun y hy => conj_mem_Obar hx hy

theorem eigenHyp_Obar {S : Setting G} (hw : S.width = 4) {g : G} (H : Hyp4 S g)
    (C : Cons311 S g) (hE : timmesfeldLayer S.Mbar = ⊥)
    (h27 : Nat.card (timmesfeldOddCore S.Mbar) = 3 ^ 3) :
    EigenHyp (S7.Obar S) (S.Lbar g) where
  card_Y := by rw [S7.card_Obar, h27]; norm_num
  card_L := by rw [C.card_Lbar, hw]; norm_num
  sq x hx := S4.mul_self_of_mem_Lbar S H.conj_mem hx
  conj x hx y hy := S7.conj_mem_Obar (S.Lbar_le_Mbar g hx) hy
  centY y hy hcomm :=
    S5.eq_one_of_mem_of_commute (g := g) H (by rw [S7.card_Obar, h27]; norm_num) hy hcomm
  centL x hx hcomm := by
    have hxY : x ∈ S7.Obar S :=
      mem_Obar_of_commute hE h27 (S.Lbar_le_Mbar g hx) hcomm
    have h2 : x * x = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem hx
    have hdvd2 : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    have hdvd27 : orderOf x ∣ 27 := by
      have h := Subgroup.orderOf_dvd_natCard (S7.Obar S) hxY
      rwa [show Nat.card (S7.Obar S) = 27 by rw [S7.card_Obar, h27]; norm_num] at h
    have hdvd : orderOf x ∣ 1 := by
      have h := Nat.dvd_gcd hdvd2 hdvd27
      rwa [show Nat.gcd 2 27 = 1 by norm_num] at h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

end CFSG.GF2Type.Smith1979.TriPlus

end
