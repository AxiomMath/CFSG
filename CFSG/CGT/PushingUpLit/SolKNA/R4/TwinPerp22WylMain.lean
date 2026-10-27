module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22WylThmE
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22WylFratt

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

namespace Perp22Wyl

namespace WylFrame

section Final


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {W : Subgroup Y}
  (h : PerpHypR r n Y R S t) (F : WylFrame (CoreAssembly.conjClass (tightCore R)) W t)
  (c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W)
  (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)

include h F c hc

theorem E_le_centralizer : F.E ≤ Subgroup.centralizer ({t} : Set Y) := by
  rw [WylFrame.E, Subgroup.closure_le]
  rintro x (rfl | hx)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · rw [Set.mem_singleton_iff.mp hx]; exact t'_mem_centralizer F c hc

theorem false_of_frame (hr : 4 ≤ r) (hE : TwinThmER r n) (h4 : Thm4RTwinBelow r n)
    (hT : Thm1RTwinInO2 r n)
    (hCent : ∀ i j : Fin 4, i ≠ j → ∀ cc : Y, (cc = F.a i * F.a j ∨ cc = t * (F.a i * F.a j)) →
      Subgroup.centralizer ({cc} : Set Y) ≤ MGrp (CoreAssembly.conjClass (tightCore R)) W ⊔
        oddCoreIn (Subgroup.centralizer ({cc} : Set Y)) ⊔ Subgroup.centralizer ({t} : Set Y)) :
    False := by
  have hB := F.hyp51_B h c hc h4 hT
  have hEB : F.E ≤ F.B := by
    rw [WylFrame.E, Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact F.z_mem_B h c hc
    · rw [Set.mem_singleton_iff.mp hx]; exact F.t'_mem_B h c hc
  have hE4 : IsElemAbelian2 F.E 2 := ⟨by rw [F.E_card c hc]; norm_num, F.E_sq c hc⟩
  obtain ⟨hodd, -⟩ := lemma54_odd_and_eq hB hEB hE4
  have hfac := frattini hr h F c hc
  have hy := F.y_mem_normE c hc 0
  have hg := F.g_mem_normE c hc 0
  have hA : ∀ i j : Fin 4, i ≠ j → ∀ cc : Y, (cc = F.a i * F.a j ∨ cc = t * (F.a i * F.a j)) →
      IsPGroup 2 (Subgroup.closure ({cc, t} : Set Y)) ∧
      cc ∈ Subgroup.closure ({cc, t} : Set Y) ∧ t ∈ Subgroup.closure ({cc, t} : Set Y) ∧
      cc ≠ 1 ∧ Subgroup.closure ({cc, t} : Set Y) ≤ Subgroup.centralizer ({cc} : Set Y) ∧
      alphaOf (Subgroup.closure ({cc, t} : Set Y)) = alphaOf F.E := by
    intro i j hij cc hcc
    obtain ⟨hsq, hc1, hct, hccW⟩ := F.pair_facts h c hc hij hcc
    have hcomm : cc * t = t * cc := hc _ hccW _ (F.z_mem_W c)
    refine ⟨Perp24.isPGroup_two_of_sq (Perp24.closure_pair_sq hsq F.z_sq hcomm),
      Subgroup.subset_closure (Set.mem_insert _ _),
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), hc1, ?_,
      F.alpha_pair h c hc h4 hT hij hcc⟩
    rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · rw [Set.mem_singleton_iff.mp hx]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hCzα : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (alphaOf F.E : Set Y) :=
    Perp24.le_normalizer_alphaOf (F.E_isPGroup c hc) F.z_mem_E F.z_ne_one
      (F.E_le_centralizer h c hc) hfac
  have hMα := F.mgrp_le_of h c hc hCzα (Perp24.mem_normalizer_alphaOf hy)
    (Perp24.mem_normalizer_alphaOf hg)
  have hUα : ∀ i j : Fin 4, i ≠ j → ∀ cc : Y, (cc = F.a i * F.a j ∨ cc = t * (F.a i * F.a j)) →
      Subgroup.centralizer ({cc} : Set Y) ≤ Subgroup.normalizer (alphaOf F.E : Set Y) := by
    intro i j hij cc hcc
    obtain ⟨hp, hcA, htA, hc1, hAC, hαA⟩ := hA i j hij cc hcc
    refine (hCent i j hij cc hcc).trans (sup_le (sup_le hMα ?_) hCzα)
    have hαle : alphaOf (Subgroup.closure ({cc, t} : Set Y)) ≤
        Subgroup.normalizer (alphaOf F.E : Set Y) := by
      rw [hαA]
      exact fun x hx => (alphaOf F.E).le_normalizer hx
    exact oddCore_le_of_alpha hp hcA hc1 htA hAC hαle hCzα
  have htopα := F.thmE_apply h c hc hr hE hCzα hMα hUα
  have hαn : (alphaOf F.E).Normal := Subgroup.normalizer_eq_top_iff.mp htopα
  have hαbot : alphaOf F.E = ⊥ := by
    have hle : alphaOf F.E ≤ classicalInvolutionOddCore Y := le_sSup ⟨hαn, hodd⟩
    rw [h.core.oddFree] at hle
    exact le_bot_iff.mp hle
  have hCzE : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (F.E : Set Y) :=
    Perp24.le_normalizer_of_alphaOf_eq_bot F.z_mem_E F.z_ne_one hαbot hfac
  have hME := F.mgrp_le_of h c hc hCzE hy hg
  have hUE : ∀ i j : Fin 4, i ≠ j → ∀ cc : Y, (cc = F.a i * F.a j ∨ cc = t * (F.a i * F.a j)) →
      Subgroup.centralizer ({cc} : Set Y) ≤ Subgroup.normalizer (F.E : Set Y) := by
    intro i j hij cc hcc
    obtain ⟨hp, hcA, htA, hc1, hAC, hαA⟩ := hA i j hij cc hcc
    refine (hCent i j hij cc hcc).trans (sup_le (sup_le hME ?_) hCzE)
    have hαle : alphaOf (Subgroup.closure ({cc, t} : Set Y)) ≤
        Subgroup.normalizer (F.E : Set Y) := by
      rw [hαA, hαbot]
      exact bot_le
    exact oddCore_le_of_alpha hp hcA hc1 htA hAC hαle hCzE
  have htopE := F.thmE_apply h c hc hr hE hCzE hME hUE
  have hEn : F.E.Normal := Subgroup.normalizer_eq_top_iff.mp htopE
  haveI := h.core.simple
  exact not_tightInO2_of_fstar h.core.nonab F.z_ne_one ⟨F.E, hEn, F.E_isPGroup c hc, F.z_mem_E⟩

end Final

end WylFrame

end Perp22Wyl

end CFSG.CGT.PushingUpLit.SolKNA.R4
