module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltCell
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltFour
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8CentComp
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1Zc
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltOrd

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Fin

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem alt7_false_of_normalizes (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (hsw : Sb ≤ normalizer (J : Set A)) (e : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin 7)) :
    False :=
  alt7_false hfr hJ hsw (L1.card_centralizer_le_two hfr hJ hsw) e

theorem alt7_false_of_center_bot (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (hZ : center ↥J = ⊥) (e : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨U, hUJ, hU⟩ := exists_four_le_comp_of_center_bot hJ.1 (by norm_num) hZ e
  exact alt7_false_of_normalizes hfr hJ
    (le_normalizer_of_unique hJ (hfr.comp_unique_of_four hJ hUJ hU)) e

theorem alt11_cover (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (e : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin 11)) : IsDoubleCoverOfAlt A 11 := by
  have : Group.IsPerfect ↥J := hJ.1.1
  obtain ⟨U, hUJ, hU⟩ := exists_four_le_comp_of_alt hJ.1 (by norm_num) e
  have hu := hfr.comp_unique_of_four hJ hUJ hU
  have hsw : Sb ≤ normalizer (J : Set A) := le_normalizer_of_unique hJ hu
  have hzc := L1.card_centralizer_le_two hfr hJ hsw
  have hzbJ : zb ∈ J := hfr.zb_mem_of_unique_comp hJ hu
  have hZle : Nat.card ↥(center ↥J) ≤ 2 :=
    CFSG.OddStandard.GlueAlt.card_center_le_two_of_alt (by norm_num) e
  have hJn : J.Normal := Gen.normal_of_unique_comp hJ hu
  rcases hfr.cent_comp_cases hJ hu hzc with hC | hC
  · exact (alt11_false_of_ker_bot hfr hsw (by rw [hC, inf_bot_eq]) e).elim
  · have hzbC : zb ∈ centralizer (J : Set A) := by
      rw [hC]
      exact Subgroup.mem_zpowers zb
    have hzbZ : (⟨zb, hzbJ⟩ : ↥J) ∈ center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hzbC) (y : A) y.2)
    have hZne : center ↥J ≠ ⊥ := by
      intro h
      rw [h, Subgroup.mem_bot] at hzbZ
      have h1 : zb = 1 := congrArg Subtype.val hzbZ
      have := hfr.zb_ord
      rw [h1, orderOf_one] at this
      exact absurd this (by norm_num)
    have hZ2 : Nat.card ↥(center ↥J) = 2 := by
      have hpos : 1 < Nat.card ↥(center ↥J) := by
        rw [Nat.one_lt_iff_ne_zero_and_ne_one]
        exact ⟨Nat.card_pos.ne', fun h => hZne (Subgroup.card_eq_one.mp h)⟩
      omega
    have htop : J = ⊤ := alt11_eq_top hfr hJ hJn hC hZ2 e
    have hcov : IsDoubleCoverOfAlt ↥J 11 := ⟨hJ.1, hZ2, ⟨e⟩⟩
    exact TwoThin.isDoubleCoverOfAlt_of_mulEquiv
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) hcov

end Fin

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
