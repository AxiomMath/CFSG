module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.CaseC
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Lemma36Tri
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NP
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.StatementHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.StdUHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.TopM12
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.YoshidaCo3Holds

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.EvenSporadicStandard.M12Std

section Yoshida

open _root_.Certificates

theorem yoshida74Co3K_holds : SolomonK.Yoshida74Co3K :=
  SolomonK.yoshida74Co3K_of_orders
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    (CFSG.AGLEmbedding.card_carrier_eq_sporOrd CFSG.Milestones.fam_m_finiteness)
    CFSG.RankThree.PartOne.SPOR.schreierFor_catalog

end Yoshida

section Inner

open _root_.Certificates

theorem m12_gives_co3_of_innerActionK (hY : SolomonK.Yoshida74Co3K) (hI : FS79M12InnerAction)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L)
    (hL : IsSporadic L .M12) : IsSporadic G .Co3 := by
  obtain ⟨t, ht, ht2⟩ := h.exists_involution_centralizer
  exact hY G h.kProper h.simple t ht2
    (m12_inner_nonempty_equiv h hL ht ht2 (hI G L h hL t ht ht2))

end Inner

section Assembly

open _root_.Certificates

theorem false_of_out_rbc {G : Type} [Group G] [Finite G] (hNP : KDNP)
    (hUG : Induction.Balance.UHered G)
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hGH : CFSG.ComponentClassification.UFrontier.GH74ModelsInput)
    (hCTE : CFSG.EvenSporadicStandard.Induction.CTEvenResidualStatement)
    (hL34 : Induction.ChildL34WHered) (hHe : Induction.ChildHeWHered)
    (h4 : M22M23M24Exclusion) (h5 : J1J3J4Exclusion) (h6 : HSMcLLyExclusion)
    (h7 : TwoHSGivesHN) (h8 : LargeExclusion) (h9 : Co2Exclusion) (h10 : TwoFi22Gives)
    (h11 : TwoBGivesM) (h12 : J2Exclusion)
    {L : Subgroup G} {t : G} (hO : Out G L t) : False := by
  have hMcard : Nat.card CFSG.Open.MonsterY443Derived = CFSG.Open.monsterOrder :=
    CFSG.Milestones.fam_m_finiteness
  have htop : TopIsM12 G :=
    topIsM12 hMcard hUG hCIT hGH hCTE hL34 hHe h4 h5 h6 h7 h8 h9 h10 h11 h12 hO
  obtain ⟨n, U, T, s, u, x, hD⟩ := exists_topData yoshida74Co3K_holds hCIT hMcard htop hO
  have hOu := hD.out
  have hzx : centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rcases hD.trichotomy hUG with hA | ⟨K₀, hK₀, hne, hinv, hle, hcl⟩ | ⟨I, hI, h5a, hle, hcl⟩
  ·
    rw [hD.jstar, hzx] at hA
    exact not_isComp_jOf_of_outer hOu.std hOu.m12 hOu.mem hOu.inv hOu.outer hD.xmem hD.xinv
      hD.x240 hA
  ·
    exact hD.false_caseB hUG hCIT hMcard htop hK₀ hne hinv hle hcl
  ·
    refine hD.false_caseC_of_not_fiveALink hUG hCIT hMcard (fun L' => ?_) hI h5a hle hcl
    rw [hD.jstar]
    exact not_fiveALink_into hNP hUG hOu hD.xmem hD.xinv hD.x240 hD.cent hD.facts hD.rbc L'

theorem fs79M12InnerActionHered_of_rbc
    (hCU : CFSG.ComponentClassification.CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hNP : KDNP)
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hGH : CFSG.ComponentClassification.UFrontier.GH74ModelsInput)
    (hCTE : CFSG.EvenSporadicStandard.Induction.CTEvenResidualStatement)
    (hL34 : Induction.ChildL34WHered) (hHe : Induction.ChildHeWHered)
    (h4 : M22M23M24Exclusion) (h5 : J1J3J4Exclusion) (h6 : HSMcLLyExclusion)
    (h7 : TwoHSGivesHN) (h8 : LargeExclusion) (h9 : Co2Exclusion) (h10 : TwoFi22Gives)
    (h11 : TwoBGivesM) (h12 : J2Exclusion) : FS79M12InnerAction := by
  intro G _ _ L h hL t ht ht2
  by_contra hnot
  exact false_of_out_rbc hNP (h.uHered hCU) hCIT hGH hCTE hL34 hHe h4 h5 h6 h7 h8 h9 h10 h11 h12
    ⟨h, hL, ht, ht2, hnot⟩

theorem fs79RbcHered_holds
    (hCU : CFSG.ComponentClassification.CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) :
    FS79RbcHered := by
  intro hNP hCIT hGH hCTE hL34 hHe h4 h5 h6 h7 h8 h9 h10 h11 h12 G _ _ L hL hcase
  rcases hcase with hM | hC | ⟨h2, hS⟩
  · exact ⟨hM, m12_gives_co3_of_innerActionK yoshida74Co3K_holds
      (fs79M12InnerActionHered_of_rbc hCU hNP hCIT hGH hCTE hL34 hHe h4 h5 h6 h7 h8 h9 h10 h11
        h12)
      hL hM⟩
  · exact absurd hC (Co3Std.CentT.fs79Co3Excluded_of_catalog Co3Std.CentT.kdCo3Cat_holds G L hL)
  · exact absurd hS (TwoSuz.twoSuz_not_standard_unconditional hL h2)

end Assembly

end CFSG.EvenSporadicStandard.M12Std.Rbc
