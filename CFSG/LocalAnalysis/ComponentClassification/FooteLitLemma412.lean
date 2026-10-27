module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma412Rooted
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitEndPair

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def FooteUniqueContainment (M : Subgroup G) : Prop :=
  ∀ z g : G, ¬ FooteBadPair M z g

theorem foote_lemma_4_12 (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hFI : FooteFourgroupInner) (hRO : FooteL2RootedOuter)
    {M : Subgroup G} (hM : IsFooteM L M)
    (hH : ∀ t : G, FooteInCC M t → ∀ u ∈ footeK L t, FooteInCC M u → u = t)
    (hPE : FooteEvenOrNormalizes M) : FooteUniqueContainment M := by
  intro z g hp
  obtain ⟨V, hV, hVD⟩ := hp.exists_isKleinFour h h47 hST hAsc h2An hA5 hE8 hK hcalc hRO hM hH hPE
  have hNg : conjugate (normalizer (M : Set G)) g = normalizer (conjugate M g : Set G) :=
    UnbalancedCorr.conjugate_normalizer M g
  have hVN : V ≤ normalizer (conjugate M g : Set G) :=
    (hVD.trans inf_le_right).trans (hNg ▸ hp.centralizer_le)
  obtain ⟨w, hwV, hw1, hwin⟩ :=
    exists_mem_sup_of_isKleinFour h hFI (isFooteM_conjugate h hM g) hV hVN
  have hwD := hVD hwV
  exact hp.false_of_inner h h47 hST hAsc h2An hA5 hE8 hK hcalc hM hH hPE
    (orderOf_eq_prime (sq_eq_one_of_isKleinFour hV hwV) hw1) (mem_inf.mp hwD).1
    (mem_centralizer_singleton_iff.mp (mem_inf.mp hwD).2) hwin

end CFSG.ComponentClassification.FooteLit
