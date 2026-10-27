module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma413Two

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem foote_lemma_4_13
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hFI : FooteFourgroupInner) (hRO : FooteL2RootedOuter)
    (hAR : FooteAutRankThree) {M : Subgroup G} (hM : IsFooteM L M)
    (hPE : FooteEvenOrNormalizes M) (hne : ∃ t : G, FooteInCC M t) :
    ∃ t : G, FooteInCC M t ∧ ∃ u ∈ footeK L t, FooteInCC M u ∧ u ≠ t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t₀, ht₀⟩ := hne
  by_cases hsz : ∃ t : G, FooteInCC M t ∧ t ∈ footeK L t
  · obtain ⟨t, ht, htK⟩ := hsz
    exact foote_lemma_4_13_sz h h47 hST hAsc h2An hAR hM hcon ht htK
  · push Not at hsz
    exact foote_lemma_4_13_bender h h47 hST hAsc h2An hA5 hE8 hK hcalc hFI hRO hM hcon hPE hsz
      t₀ ht₀

end CFSG.ComponentClassification.FooteLit
