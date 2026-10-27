module

public import CFSG.GH74.GLS.Bg.Pu5.LPTPBasic
public import CFSG.GH74.GLS.Bg.Pu5.LPTPAbs
public import CFSG.GH74.GLS.Bg.Pu5.Statements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.TwoThin
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Bg.Iii2.CMEngine
open scoped commutatorElement

theorem l292tp_of : L292TP := by
  intro G _ _ hG h3 a b K hK hb hab hbK y _ hya hyb hyZ
  obtain ⟨J, Λ, hxY, hJ, hΛ⟩ := exists_pump hG h3 hK hb hab hbK
  have hlam : IsLam a b K Λ := hΛ.lam
  have hle : bar b Λ ≤ bar b (rigidProduct b) := bar_lam_le_rigidProduct hxY hK hJ hΛ
  set Y := centralizer ({b} : Set G) with hY
  set Ya := centralizer ({a} : Set G) with hYa
  have hRY : rigidProduct b ≤ Y := rigidProduct_le_centralizer b
  have hRsub := rigidProduct_isSubnormal b
  obtain ⟨hyR, -, -, hyc⟩ := hyZ
  have hcomm_b : ∀ l ∈ Λ, ⁅l, y⁆ ∈ pPrimeCoreOf 2 Y := by
    intro l hl
    have hlY : l ∈ Y := (Subgroup.mem_inf.mp (hlam.le hl)).2
    have hcY : ⁅l, y⁆ ∈ Y := by
      simp only [commutatorElement_def]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem hlY hyb) (Y.inv_mem hlY)) (Y.inv_mem hyb)
    obtain ⟨r, hr, hrl⟩ := hle (⟨⟨l, hlY⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩ :
      barMk ↥Y ⟨l, hlY⟩ ∈ bar b Λ)
    have hrR : (r : G) ∈ rigidProduct b := Subgroup.mem_subgroupOf.mp hr
    have hrc : ⁅(r : G), y⁆ ∈ pPrimeCoreOf 2 (rigidProduct b) := hyc _ hrR
    have hrcY : ⁅(r : G), y⁆ ∈ Y := by
      simp only [commutatorElement_def]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem r.2 hyb) (Y.inv_mem r.2)) (Y.inv_mem hyb)
    have h1 : barMk ↥Y ⟨⁅(r : G), y⁆, hrcY⟩ = 1 :=
      barMk_eq_one_of_mem_pPrimeCoreOf hRY hRsub hrc hrcY
    have h2 : barMk ↥Y ⟨⁅l, y⁆, hcY⟩ = 1 := by
      have e1 : (⟨⁅l, y⁆, hcY⟩ : ↥Y) = ⁅(⟨l, hlY⟩ : ↥Y), ⟨y, hyb⟩⁆ := rfl
      have e2 : (⟨⁅(r : G), y⁆, hrcY⟩ : ↥Y) = ⁅r, (⟨y, hyb⟩ : ↥Y)⁆ := rfl
      rw [e2, map_commutatorElement, hrl, ← map_commutatorElement] at h1
      rwa [e1]
    have h3 : (⟨⁅l, y⁆, hcY⟩ : ↥Y) ∈ pPrimeCore 2 ↥Y := (QuotientGroup.eq_one_iff _).mp h2
    exact ⟨⟨⁅l, y⁆, hcY⟩, h3, rfl⟩
  have hcomm_a : ∀ q ∈ bar a K, ⁅q, barMk ↥Ya ⟨y, hya⟩⁆ ∈ bar a (pPrimeCoreOf 2 Y) := by
    rintro _ ⟨k, hk, rfl⟩
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    obtain ⟨l, hl, o, ho, hlo⟩ := hlam.cover k hkK
    have hlK : l ∈ K := (Subgroup.mem_inf.mp (hlam.le hl)).1
    have hlYa : l ∈ Ya := (rr_pcomp hK).1 hlK
    have hoK : o ∈ K := pPrimeCoreOf_le K ho
    have hoYa : o ∈ Ya := (rr_pcomp hK).1 hoK
    have hKsub : (K.subgroupOf Ya).IsSubnormal := by
      obtain ⟨_, _, hsub, _⟩ := (rr_pcomp hK).2
      exact hsub
    have ho1 : barMk ↥Ya ⟨o, hoYa⟩ = 1 :=
      barMk_eq_one_of_mem_pPrimeCoreOf (rr_pcomp hK).1 hKsub ho hoYa
    have hkl : barMk ↥Ya k = barMk ↥Ya ⟨l, hlYa⟩ := by
      have : k = ⟨l, hlYa⟩ * ⟨o, hoYa⟩ := Subtype.ext hlo
      rw [this, map_mul, ho1, mul_one]
    have hcY : ⁅l, y⁆ ∈ Ya := by
      simp only [commutatorElement_def]
      exact Ya.mul_mem (Ya.mul_mem (Ya.mul_mem hlYa hya) (Ya.inv_mem hlYa)) (Ya.inv_mem hya)
    refine ⟨⟨⁅l, y⁆, hcY⟩, Subgroup.mem_subgroupOf.mpr (hcomm_b l hl), ?_⟩
    rw [hkl, ← map_commutatorElement]
    rfl
  have hQ : CFSG.IsComponent (bar a K) := isComponent_bar (rr_pcomp hK)
  have hM : Odd (Nat.card ↥(bar a (pPrimeCoreOf 2 Y))) := odd_card_bar_pPrimeCoreOf a Y
  have hcent := commute_of_odd_commutators_component hQ hM hcomm_a
  refine mem_centralizerSection_of_map_eq (rr_pcomp hK).1 (isPCompIn_two_iff.mp (rr_pcomp hK)).2 hya ?_
  intro m hm
  have h1 := hcent (barMk ↥Ya m) ⟨m, hm, rfl⟩
  rw [map_mul, map_mul, map_inv, ← h1, mul_inv_cancel_right]

end CFSG.GH74.GLS.Bg.Pu5
