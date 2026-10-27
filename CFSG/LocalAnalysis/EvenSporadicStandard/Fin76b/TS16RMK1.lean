module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMK0
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RCtx
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Main8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Root

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open
open CFSG.Sporadic.Schreier (j3P j3PermEquiv)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G}

theorem OuterS16Hyp.beta_mem_L (h : OuterS16Hyp G L z t T E Q x B β) : β ∈ L :=
  h.outerB.B_le h.outerB.beta_mem

theorem OuterS16Hyp.z_mem_cent_beta (h : OuterS16Hyp G L z t T E Q x B β) :
    z ∈ centralizer ({β} : Set G) :=
  mem_centralizer_singleton_iff.2 (h.outerE.cfg.z_comm_of_mem_A h.beta_mem_L).symm

theorem OuterS16Hyp.outerBetaFor
    (h : OuterS16Hyp G L z t T E Q x B β) :
    OuterBetaFor ↥L (⟨β, h.beta_mem_L⟩ : ↥L) := by
  have hJ := h.sporadic
  have hRC : RootFactsClass ↥L :=
    rootFactsClass_of_sporadic J2.rootFactsClass_P J3.rootFactsClass_j3P hJ
  obtain ⟨htL, ht2', hsq', -⟩ := h.outerE.eq_map_rootGroup_of_class h.wFacts hRC
  have hBL : BetaDataSqBO ↥L :=
    betaDataSqBO_of_sporadic J2.betaDataSqBO_Models_P J3.betaDataSqBO_j3P hJ
  have hβt : (⟨β, h.beta_mem_L⟩ : ↥L) ∈ centralizer ({(⟨t, htL⟩ : ↥L)} : Set ↥L) := by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (h.outerB.B_cent h.outerB.beta_mem))
  have hβ3 : orderOf (⟨β, h.beta_mem_L⟩ : ↥L) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact h.outerB.beta_order
  exact outerBetaFor_of_class hBL ht2' hsq' (hRC _ ht2' hsq').card_cent hβt hβ3

theorem OuterS16Hyp.m10Config
    (h : OuterS16Hyp G L z t T E Q x B β) :
    M10Config (⟨z, h.z_mem_cent_beta⟩ : ↥(centralizer ({β} : Set G)))
      ((L ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G))) := by
  have hJ := h.sporadic
  have hcfg := h.outerE.cfg
  obtain ⟨hZ, hcZ, hOE, hout⟩ := outer_inputs_of_sporadic J2.outerEData_P J3.outerEData_j3P hJ
  obtain ⟨EY, hP⟩ := exists_pullHyp h.std h.cyclicC hZ hcZ hOE hout h.relIdx hcfg
  have hsurj := thetaH_surjective h.std h.cyclicC hcfg.z_cent hcfg.z_order hcfg.cent_le hout
    h.relIdx
  have hβL : β ∈ L := h.beta_mem_L
  have hO' := outerBetaFor_quotient hZ h.outerBetaFor
  have hM1 := hP.exists_outer_fix hsurj hβL hO'
  have hM2 : ∀ c ∈ centralizer ({z} : Set G), c * β = β * c → c * c ∈ zpowers z ⊔ zpowers β →
      c ∈ L ⊔ zpowers z := fun c hc hcβ hcc =>
    hP.mem_of_sq_mem hβL h.outerB.beta_order hO' hc hcβ hcc
  obtain ⟨S, c⟩ := h.exists_ctx
  obtain ⟨s, hsS, hs1, n, hsn⟩ := exists_noncomm_of_shape c.S2 c.SC c.zS c.facts.1 h.centZ
  have hS : ∃ s : G, s * β = β * s ∧ z * s * z⁻¹ * s⁻¹ ≠ 1 ∧
      ∃ n : ℕ, (z * s * z⁻¹ * s⁻¹) ^ (2 ^ n) = 1 :=
    ⟨s, (c.BS β h.outerB.beta_mem s hsS).symm, hs1, n, hsn⟩
  exact m10Config_of_outerConfig hcfg h.outerB.D_quot h.outerB.D_odd hM1 hM2 hS h.z_mem_cent_beta

end CFSG.EvenSporadicStandard.Fin76b
