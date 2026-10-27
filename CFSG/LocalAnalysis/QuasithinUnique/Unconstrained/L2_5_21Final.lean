module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21AutFactsProof
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Cl1
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21OutCases
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21B

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

theorem lemma2521Out_of_parts (hshape : OutShape) (hone : OutOneClass) (houter : OutOuter)
    (hC : Lemma2521CaseC) : Lemma2521Out := by
  intro G _ _ T M hs N t zK h hfam
  obtain ⟨hidx0, R, hR⟩ := hshape G N.K N.H N.S (h.outSetting hfam)
  have hidx := h.card_S_le hidx0
  by_cases h2 : Nat.card ↥N.SC = 2
  · exact h.caseA_false hR hidx h2 hone houter hfam
  · by_cases hab : ∀ a ∈ N.SC, ∀ b ∈ N.SC, a * b = b * a
    · have h4 : 4 ≤ Nat.card ↥N.SC :=
        four_le_card_of_ne_two (N.tuple.sylow.isPGroup.to_le N.SC_le_S) h.facts254.SC_ne_bot h2
      exact h.caseB_false hR hidx hab h4
    · push Not at hab
      exact hC G T M hs N t zK R h hfam (h.caseCParams hR hidx hab)

theorem lemma2521_of_parts (hshape : OutShape) (hone : OutOneClass) (houter : OutOuter)
    (hC : Lemma2521CaseC) : Lemma2521 :=
  lemma2521_of_out (lemma2521Out_of_parts hshape hone houter hC)

theorem lemma2521_of_inputs
    (hAsc : Asc75Lemma34Disjoint) (h1 : CaseCClaim1) (hgen : CaseCGeneration)
    (hout : CaseCOutside) : Lemma2521 :=
  lemma2521_of_parts outShape outOneClass outOuter
    (lemma2521CaseC_of_parts hAsc h1 caseCClaim2 hgen
      (caseCGlobal_of_fusion (caseCFusion_of_outside hout)))

theorem lemma2521_of_asc_outside
    (hAsc : Asc75Lemma34Disjoint) (hout : CaseCOutside) : Lemma2521 :=
  lemma2521_of_inputs hAsc caseCClaim1 caseCGeneration hout

theorem lemma2521_of_asc_outAut
    (hAsc : Asc75Lemma34Disjoint) (hAF : OutAutAll) : Lemma2521 :=
  lemma2521_of_asc_outside hAsc (caseCOutside_of_facts hAF)

theorem outAutAll
    : OutAutAll := fun _ _ _ hX => Out21.outAutFacts_of_l2p hX

theorem lemma2521_of_asc
    (hAsc : Asc75Lemma34Disjoint) : Lemma2521 :=
  lemma2521_of_asc_outAut hAsc outAutAll

end CFSG.QuasithinUnique
