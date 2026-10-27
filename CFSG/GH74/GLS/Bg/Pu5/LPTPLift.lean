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

theorem l292lp_of : L292LP := by
  intro G _ _ hG h3 a b K hK hb hab hbK y hyZ hy2 hyb
  obtain ⟨J, Λ, hxY, hJ, hΛ⟩ := exists_pump hG h3 hK hb hab hbK
  have hlam : IsLam a b K Λ := hΛ.lam
  have hle : bar b Λ ≤ bar b (rigidProduct b) := bar_lam_le_rigidProduct hxY hK hJ hΛ
  set Y := centralizer ({b} : Set G) with hY
  have hRY : rigidProduct b ≤ Y := rigidProduct_le_centralizer b
  have hRsub := rigidProduct_isSubnormal b
  obtain ⟨hyK, -, -, hyc⟩ := hyZ
  set yq : barQ ↥Y := barMk ↥Y ⟨y, hyb⟩ with hyq
  have hyΛ : y ∈ Λ := hlam.twoElt y (Subgroup.mem_inf.mpr ⟨hyK, hyb⟩) hy2
  have hyqΛ : yq ∈ bar b Λ := ⟨⟨y, hyb⟩, Subgroup.mem_subgroupOf.mpr hyΛ, rfl⟩
  have hJc : CFSG.IsComponent (bar b J) := isComponent_bar (rr_pcomp hJ)
  have hqs : CFSG.IsQuasisimple ↥(bar b Λ) := by
    rcases hΛ.cases with ⟨-, hv⟩ | ⟨-, hAB, hD⟩
    · rw [hv]
      exact hJc.1
    · rw [hD]
      exact (AssemblyBPredicates.isQuasisimple_iff_native _).1
        (isQuasisimple_range_swapDiag hAB ((AssemblyBPredicates.isQuasisimple_iff_native _).2 hJc.1))
  have hM : Odd (Nat.card ↥(bar b (pPrimeCoreOf 2 K))) := odd_card_bar_pPrimeCoreOf b K
  have hcommΛ : ∀ q ∈ bar b Λ, ⁅q, yq⁆ ∈ bar b (pPrimeCoreOf 2 K) := by
    rintro _ ⟨l, hl, rfl⟩
    have hlΛ : (l : G) ∈ Λ := Subgroup.mem_subgroupOf.mp hl
    have hlK : (l : G) ∈ K := (Subgroup.mem_inf.mp (hlam.le hlΛ)).1
    have hcY : ⁅(l : G), y⁆ ∈ Y := by
      simp only [commutatorElement_def]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem l.2 hyb) (Y.inv_mem l.2)) (Y.inv_mem hyb)
    refine ⟨⟨⁅(l : G), y⁆, hcY⟩, Subgroup.mem_subgroupOf.mpr (hyc _ hlK), ?_⟩
    rw [hyq]
    change barMk ↥Y ⁅l, (⟨y, hyb⟩ : ↥Y)⁆ = ⁅barMk ↥Y l, barMk ↥Y ⟨y, hyb⟩⁆
    exact map_commutatorElement _ _ _
  have hcentΛ : ∀ w ∈ bar b Λ, w * yq = yq * w :=
    commute_of_odd_commutators hqs (Subgroup.le_normalizer hyqΛ) hM hcommΛ
  have hcentRig : ∀ J'' : Subgroup G, IsRigidRankOneComp b J'' → ∀ w ∈ bar b J'', w * yq = yq * w := by
    intro J'' hJ'' w hw
    have hXc : CFSG.IsComponent (bar b J'') := isComponent_bar (rr_pcomp hJ'')
    rcases hΛ.cases with ⟨-, hv⟩ | ⟨-, hAB, hD⟩
    ·
      have hyqJ : yq ∈ bar b J := hv ▸ hyqΛ
      have hcentJ : ∀ w ∈ bar b J, w * yq = yq * w := hv ▸ hcentΛ
      rcases CFSG.LocalCores.distinct_components_commute hXc hJc with h | h
      · rw [h] at hw
        exact hcentJ w hw
      · have := Subgroup.commutator_mem_commutator hw hyqJ
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this
    ·
      set t := sbar a hxY with ht
      have hs2 : orderOf t = 2 := orderOf_sbar (rr_ord hK) hxY
      have hsinv : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two hs2
      have hyqD : yq ∈ (swapDiag hAB).range := hD ▸ hyqΛ
      have hcentD : ∀ w ∈ (swapDiag hAB).range, w * yq = yq * w := hD ▸ hcentΛ
      obtain ⟨hAc, hBc⟩ := commute_of_mem_range_swapDiag hAB hJc.1 hyqD hcentD
      have hJ' : IsRigidRankOneComp b (cmap a J) := isRigidRankOneComp_cmap hJ hxY
      have hbarJ' : bar b (cmap a J) = conjSub t⁻¹ (bar b J) := by
        rw [bar_cmap hxY, hsinv]
      have hBc' : CFSG.IsComponent (conjSub t⁻¹ (bar b J)) := hbarJ' ▸ isComponent_bar (rr_pcomp hJ')
      rcases CFSG.LocalCores.distinct_components_commute hXc hJc with h | h
      · rw [h] at hw
        exact hAc w hw
      rcases CFSG.LocalCores.distinct_components_commute hXc hBc' with h' | h'
      · rw [h'] at hw
        exact hBc w hw
      obtain ⟨c, hc⟩ := hyqD
      have hwc : w * (c : barQ ↥Y) = c * w := by
        have := Subgroup.commutator_mem_commutator hw c.2
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this
      have hwc' : w * (t⁻¹ * (c : barQ ↥Y) * t) = (t⁻¹ * c * t) * w := by
        have hmem : t⁻¹ * (c : barQ ↥Y) * t ∈ conjSub t⁻¹ (bar b J) := conj_mem_conjSub c.2
        have := Subgroup.commutator_mem_commutator hw hmem
        rw [h', Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this
      rw [← hc, swapDiag_apply]
      calc w * (c * (t⁻¹ * c * t)) = (w * c) * (t⁻¹ * c * t) := by group
        _ = (c * w) * (t⁻¹ * c * t) := by rw [hwc]
        _ = c * (w * (t⁻¹ * c * t)) := by group
        _ = c * ((t⁻¹ * c * t) * w) := by rw [hwc']
        _ = (c * (t⁻¹ * c * t)) * w := by group
  have hT : (rigidProduct b).subgroupOf Y ≤ (Subgroup.centralizer ({yq} : Set (barQ ↥Y))).comap (barMk ↥Y) := by
    rw [rigidProduct_subgroupOf]
    refine sSup_le ?_
    rintro _ ⟨J'', hJ'', rfl⟩ r hr
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact hcentRig J'' hJ'' _ ⟨r, hr, rfl⟩
  have hcentR : ∀ r : ↥Y, (r : G) ∈ rigidProduct b → barMk ↥Y r * yq = yq * barMk ↥Y r := by
    intro r hr
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_comap.mp (hT (Subgroup.mem_subgroupOf.mpr hr)))
  have hyR : y ∈ rigidProduct b := by
    have hX : IsPGroup 2 ↥(Subgroup.zpowers (⟨y, hyb⟩ : ↥Y)) := by
      obtain ⟨n, hn⟩ := hy2
      exact TwoThin.isPGroup_zpowers_of_pow_eq_one (n := n) (Subtype.ext (by simpa using hn))
    have hS : CFSG.Open.IsSubnormal ((rigidProduct b).subgroupOf Y) ⊤ :=
      Components.chain_of_mathlib_subnormal hRsub
    have himg : (Subgroup.zpowers (⟨y, hyb⟩ : ↥Y)).map (barMk ↥Y) ≤
        ((rigidProduct b).subgroupOf Y).map (barMk ↥Y) := by
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      exact hle hyqΛ
    have := le_of_isPGroup_of_map_le (barMk ↥Y) barMk_surjective odd_card_ker_barMk _ _ hX hS himg
      (Subgroup.mem_zpowers (⟨y, hyb⟩ : ↥Y))
    exact Subgroup.mem_subgroupOf.mp this
  show y ∈ rigidProduct b ⊓ centralizerSection (rigidProduct b) (pPrimeCoreOf 2 (rigidProduct b))
  refine Subgroup.mem_inf.mpr ⟨hyR, Subgroup.le_normalizer hyR,
    mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hyR), fun k hk => ?_⟩
  have hkcR : ⁅k, y⁆ ∈ rigidProduct b := by
    simp only [commutatorElement_def]
    exact (rigidProduct b).mul_mem (((rigidProduct b).mul_mem ((rigidProduct b).mul_mem hk hyR)
      ((rigidProduct b).inv_mem hk))) ((rigidProduct b).inv_mem hyR)
  have hkcY : ⁅k, y⁆ ∈ Y := hRY hkcR
  refine mem_pPrimeCoreOf_of_barMk_eq_one hRY hRsub hkcR hkcY ?_
  have hkY : k ∈ Y := hRY hk
  have e1 : (⟨⁅k, y⁆, hkcY⟩ : ↥Y) = ⁅(⟨k, hkY⟩ : ↥Y), ⟨y, hyb⟩⁆ := rfl
  rw [e1, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (hcentR ⟨k, hkY⟩ hk)

end CFSG.GH74.GLS.Bg.Pu5
