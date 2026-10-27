module

public import CFSG.ClassicalInvolution.Q3.TL4Res2FXDefs
public import CFSG.ClassicalInvolution.Q3.TL4Res2FOSec
public import CFSG.ClassicalInvolution.Q3.TL4Res2FOLie
public import CFSG.ClassicalInvolution.Q3.TL4Res2FOAut

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G]


theorem oddCent_eq_bot_of_exitTwoClassR {n : ℕ} (hA : CIT3Below n) (hP : TightBelowRPlus 3 n)
    (hX : ExitTwoClassR n) (hG : Nat.card G < n) {J L L₀ : Subgroup G}
    (hc : F2CoreConfig J L L₀) {K : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) {z : G}
    (hz : IsUniqueInvolution K z) : oddCoreImg (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
  obtain ⟨h, -, -, -, hno, hL₀, hn, hlay, -, hZ, hC, hmem⟩ := id hc
  have hzL : z ∈ L₀ := hmem K hK z hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hzZ : z ∉ Subgroup.center G := fun hzc =>
    hno K hK z hz ⟨pCore 2 G, CFSG.pCore_normal, CFSG.pCore_isPGroup, by rw [hZ]; exact hzc⟩
  refine oddCoreImg_eq_bot_of_autOddFreeInner h.odd hL₀ hlay hzL hz2 ?_
  obtain ⟨W, hKW, hWs, hWg, hout⟩ := exists_secLift_or_exitR (hP.twin rfl)
    (tightBelowR_three_iff.mp hP.tbelow) hG h hno hK hz
  rcases hout with hex | ⟨M, -, hM, hΛ⟩
  · exact (hX G hG J L L₀ hc K hK z hz W hKW hWs hWg hex).elim
  have hOW : classicalInvolutionOddCore ↥W = ⊥ :=
    CFSG.ComponentClassification.OddCore.subnormal_corefree h.odd W hWs
  have hLie : LieSystemMod3 (CoreAssembly.conjClass M) :=
    hA ↥W (lt_of_le_of_lt (Subgroup.card_le_card_group W) hG) _ hΛ
  have hmove : ∃ y ∈ L₀, y * z ≠ z * y := by
    by_contra hcon
    push Not at hcon
    exact hzZ (hC ▸ Subgroup.mem_centralizer_iff.mpr hcon)
  have hL₀W : L₀ ≤ W :=
    component_le_of_not_commute hWs (hKW hz.mem) ((CFSG.isComponent_iff_open L₀).mp hL₀) hmove
  have := hn
  have hL₀' : CFSG.IsComponent (L₀.subgroupOf W) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL₀W).symm hL₀.1,
      (Subgroup.normal_subgroupOf (H := W) (N := L₀)).isSubnormal⟩
  have hnc : ∀ M' ∈ CoreAssembly.conjClass M, ¬ M' ≤ Subgroup.center ↥W := by
    rintro _ ⟨w, rfl⟩ hle
    have h1 := hle (conj_mem_conjSub (n := w) hM.mem)
    have h2 := (inferInstance : (Subgroup.center ↥W).Normal).conj_mem _ h1 w⁻¹
    rw [show w⁻¹ * (w * ⟨z, hKW hz.mem⟩ * w⁻¹) * w⁻¹⁻¹ = ⟨z, hKW hz.mem⟩ by group] at h2
    refine hzZ (hC ▸ Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h2 ⟨y, hL₀W hy⟩)
  exact Q3CH.autOddFreeInner_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL₀W)
    (autOddFreeInner_of_lieSystemMod3 hOW hLie hnc hL₀')

theorem exitModelCore_of {n : ℕ} (hA : CIT3Below n) (hP : TightBelowRPlus 3 n)
    (hX : ExitTwoClassR n) : ExitModelCore n := by
  intro G _ _ hG J L L₀ hc K hK z hz hout
  rcases hout with hne | ⟨W, hKW, hWs, hWg, hex⟩
  · exact hne (oddCent_eq_bot_of_exitTwoClassR hA hP hX hG hc hK hz)
  · exact hX G hG J L L₀ hc K hK z hz W hKW hWs hWg hex

theorem exitModelR_of {n : ℕ} (hA : CIT3Below n) (hP : TightBelowRPlus 3 n)
    (hX : ExitTwoClassR n) : ExitModelR n :=
  exitModelR_of_core (exitModelCore_of hA hP hX)

end CFSG.ClassicalInvolution.Q3.TL4
