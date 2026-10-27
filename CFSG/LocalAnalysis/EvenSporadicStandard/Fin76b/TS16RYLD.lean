module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYL4
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYSpor
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYSporF1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16Rung
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Root
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2J2Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2HJ3Data

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem OuterS16Hyp.exists_lData
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G} {Q : Sylow 2 G}
    {x : G} {B : Subgroup G} {β : G} (h : OuterS16Hyp G L z t T E Q x B β) :
    ∃ σ v ξ : G, S16LData G L z t β E σ v ξ ∧ S16LData G L z t β E (σ * z) v ξ := by
  have hJ := h.sporadic
  have hcfg := h.outerE.cfg
  obtain ⟨hZ, hcZ, hOE, hout⟩ := outer_inputs_of_sporadic J2.outerEData_P J3.outerEData_j3P hJ
  obtain ⟨EY, hP⟩ := exists_pullHyp h.std h.cyclicC hZ hcZ hOE hout h.relIdx hcfg
  have hsurj := thetaH_surjective h.std h.cyclicC hcfg.z_cent hcfg.z_order hcfg.cent_le hout
    h.relIdx
  have hTD : ThetaData G L z := ThetaData.of_pullHyp hP hsurj
  have hRC : RootFactsClass ↥L :=
    rootFactsClass_of_sporadic J2.rootFactsClass_P J3.rootFactsClass_j3P hJ
  obtain ⟨htL, ht2', hsq', hEeq⟩ := h.outerE.eq_map_rootGroup_of_class h.wFacts hRC
  have hβL : β ∈ L := h.outerB.B_le h.outerB.beta_mem
  have hβt : (⟨β, hβL⟩ : ↥L) ∈ centralizer ({(⟨t, htL⟩ : ↥L)} : Set ↥L) := by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (h.outerB.B_cent h.outerB.beta_mem))
  have hβ3 : orderOf (⟨β, hβL⟩ : ↥L) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact h.outerB.beta_order
  have hM := s16ModelClass_of_sporadic hJ ⟨t, htL⟩ ⟨β, hβL⟩ ht2' hsq' hβt hβ3
  have hF1 := s16F1_of_sporadic hJ
  exact exists_s16LData hTD hcfg.z_sq hcfg.z_not_mem_A h.sqL htL hβL hEeq hM hF1

end CFSG.EvenSporadicStandard.Fin76b
