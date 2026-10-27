module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitEndClosed
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitEvenOrNormalizes
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Simple
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SuzTau
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBAschbacherFive

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem foote_theorem_3_3_of_family
    (hSol : ∀ N : Subgroup G, IsKBalanced N → solomonKStarOf N ≤ solomonKStarOf (⊤ : Subgroup G))
    (hβ : ∀ B : Subgroup G, (∃ b : G, IsTwoComponentAt b B) → FooteFamilyType B →
      Nat.card (center (B ⧸ pPrimeCore 2 B)) ≤ 2)
    {t : G} (hce : FooteCounterexample G t L) [IsSimpleGroup G]
    (hrank2 : ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2)
    (hS : ∀ A ∈ footeFamilyOf L, A ∈ solomonKStar G) {a : G}
    {K M : Subgroup G} (hK : IsTwoComponentAt a K) (hM : IsTwoComponentAt a M)
    (hKF : K ∈ footeFamilyOf L) (hMF : M ∈ footeFamilyOf L) : K = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have ha := hK.1
  set N := centralizer ({a} : Set G) with hN
  have hna : ∃ g h : G, g * h ≠ h * g := by
    obtain ⟨⟨-, -, ⟨-, hLt, hLpc⟩, -, -, -⟩, -⟩ := hce
    obtain ⟨u, v, huv⟩ :=
      exists_mul_ne_mul_of_isQuasisimple (isQuasisimple_quotient_of_isPComponent hLt hLpc)
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
    refine ⟨u', v', fun h => huv ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      show u' * v' = v' * u' from Subtype.ext h]
  have hKN : IsTwoComponentIn K N := ⟨hK.2.1, hK.2.2⟩
  have hMN : IsTwoComponentIn M N := ⟨hM.2.1, hM.2.2⟩
  have hLfam : FooteFamilyType L := hce.1.2.2.2.2.1
  obtain ⟨-, ⟨eML⟩⟩ := id hMF
  have hMfam : FooteFamilyType M := footeFamilyType_of_equiv eML hLfam
  have hMq := isQuasisimple_quotient_of_isPComponent hM.2.1 hM.2.2
  have hZM : center (M ⧸ pPrimeCore 2 M) = ⊥ := by
    by_contra hZ
    have h1 := pRank_le_one_of_center_ne_bot hMq hMfam (hβ M ⟨a, hM⟩ hMfam) hZ
    rw [hrank2 M hMF] at h1
    omega
  have haM : a ∉ M := fun haM => center_ne_bot_of_mem_coreActionKernel haM ha
    (GSLit.mem_coreActionKernel_of_le_centralizer hM.2.1) hZM
  have haN : a ∈ N := mem_centralizer_singleton_iff.mpr rfl
  have hcent : ∀ n ∈ N, n * a = a * n := fun n hn => mem_centralizer_singleton_iff.mp hn
  have haO : a ∈ oddTwoCoreIn N := mem_oddTwoCoreIn_of_central haN hcent ha
  set S : Set (Subgroup G) := {J | IsTwoComponentIn J N ∧ J ∈ solomonKStar G} with hSdef
  have hSfin : S.Finite := Set.toFinite S
  set s := hSfin.toFinset with hs
  have hKs : K ∈ s := hSfin.mem_toFinset.mpr ⟨hKN, hS K hKF⟩
  have hMs : M ∈ s := hSfin.mem_toFinset.mpr ⟨hMN, hS M hMF⟩
  have hr : 2 ≤ s.card := Finset.one_lt_card.mpr ⟨K, hKs, M, hMs, hne⟩
  set e := s.equivFin.symm with he
  set Kf : Fin s.card → Subgroup G := fun i => ((e i : s) : Subgroup G) with hKf
  have hKfS : ∀ i, Kf i ∈ S := fun i => hSfin.mem_toFinset.mp (e i).2
  have hbal : IsKBalanced N := by
    refine ⟨s.card, Kf, fun i j hij => e.injective (Subtype.ext hij), fun J => ⟨fun hJ => ?_,
      ?_⟩, hr, fun i j hij => ?_, ?_, ?_⟩
    · refine ⟨e.symm ⟨J, hSfin.mem_toFinset.mpr hJ⟩, ?_⟩
      simp only [hKf, Equiv.apply_symm_apply]
    · rintro ⟨i, rfl⟩
      exact hKfS i
    · exact commutator_le_oddCoreIn_of_ne (hKfS i).1 (hKfS j).1
        (fun h => hij (e.injective (Subtype.ext h)))
    ·
      refine ⟨e.symm ⟨K, hKs⟩, ?_⟩
      have hKi : Kf (e.symm ⟨K, hKs⟩) = K := by simp only [hKf, Equiv.apply_symm_apply]
      rw [hKi]
      set X := (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K with hX
      have hrM : CFSG.Open.pRank 2 M = 2 := by
        have h := hrank2 M hMF
        rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h
      obtain ⟨E, hEM, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two M
      rw [hrM] at hEcard
      have hMK : M ≤ coreActionKernel K :=
        GSThmB.B5a.le_coreActionKernel_of_ne hK.2.1 hM.2.1 hK.2.2 hM.2.2 hne
      have hEX : E ≤ X := le_inf
        (hEM.trans ((le_twoLayerIn_of_isTwoComponentIn hMN).trans le_sup_right))
        (hEM.trans hMK)
      have haX : a ∈ X :=
        mem_inf.mpr ⟨mem_sup_left haO, GSLit.mem_coreActionKernel_of_le_centralizer hK.2.1⟩
      have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
      have h3 := succ_le_open_pRank_of_commute Nat.prime_two hE hEcard
        (fun x hx => hcent x (hM.2.1 (hEM hx))) ha2 (fun h => haM (hEM h)) hEX haX
      rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup]
      exact h3
    ·
      right; left
      have hKN' : solomonKStarOf N ≤ N := iSup₂_le fun J hJ => hJ.1.1
      have haY : a ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N) :=
        mem_inf.mpr ⟨mem_sup_left haO, GSLit.mem_coreActionKernel_of_le_centralizer hKN'⟩
      exact FooteLit.one_le_pRank_of_orderOf_eq_two (g := ⟨a, haY⟩)
        (by rw [Subgroup.orderOf_mk]; exact ha)
  have hle := hSol N hbal
  rw [solomonKStarOf_top_eq_bot hna ha] at hle
  have hKle : K ≤ solomonKStarOf N := le_iSup₂_of_le K ⟨hKN, hS K hKF⟩ le_rfl
  apply ne_bot_of_isPComponent hK.2.2
  rw [le_bot_iff.mp (hKle.trans hle)]
  exact Subgroup.bot_subgroupOf _

theorem FooteSec4.of_family (hLB : FooteLBalanceInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hOut : FooteL2OutAbelian)
    (hAb : FooteL2AbelianCore) (h9 : FooteL2NineOddInner) (hRk : FooteL2RankThree)
    (hSolv : FooteL2InvolutionSolvable) (hSol : Sol76T13.SolomonThm13Simple) {t : G}
    (hce : FooteCounterexample G t L) (hsimple : IsSimpleGroup G)
    (hrank2 : ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2)
    (hS : ∀ A ∈ footeFamilyOf L, A ∈ solomonKStar G) : FooteSec4 G L := by
  have := hsimple
  refine ⟨hLB, hCI, hGA, hGC, hSA, hOut, hAb, h9, hRk, hSolv, hsimple, ⟨t, hce⟩, ?_, hrank2⟩
  intro a K M hK hM hKF hMF
  have hna : ∃ g h : G, g * h ≠ h * g := by
    obtain ⟨⟨-, -, ⟨-, hLt, hLpc⟩, -, -, -⟩, -⟩ := hce
    obtain ⟨u, v, huv⟩ :=
      exists_mul_ne_mul_of_isQuasisimple (isQuasisimple_quotient_of_isPComponent hLt hLpc)
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
    refine ⟨u', v', fun h => huv ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, show u' * v' = v' * u' from Subtype.ext h]
  exact foote_theorem_3_3_of_family (fun N hN => absurd hN (hSol G hsimple hna hce.1.1 N))
    (card_center_le_two_of_footeFamilyType hGA hGC hSA G) hce hrank2 hS hK hM hKF hMF

theorem false_of_isFooteM
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hFI : FooteFourgroupInner) (hRO : FooteL2RootedOuter)
    (hAR : FooteAutRankThree) (hGen : FooteL2FourgroupGeneration)
    (h410 : FooteLemma410Statement) {M : Subgroup G} (hM : IsFooteM L M) : False := by
  by_cases hne : ∃ t : G, FooteInCC M t
  · exact foote_lemma_4_14_nonempty h h47 hST hAsc h2An hA5 hE8 hK hcalc hFI hRO hAR hM
      (footeEvenOrNormalizes h h47 hST hGen h410 hM) hne
  · refine false_of_footeNoEscape_closed h h47 hST hA5 hE8 hK hcalc hFI hM fun t ht ht2 => ?_
    by_contra hc
    exact hne ⟨t, ht2, ht, hc⟩

theorem footeRankBound_at
    (hLB : FooteLBalanceInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hOut : FooteL2OutAbelian)
    (hAb : FooteL2AbelianCore) (h9 : FooteL2NineOddInner) (hRk : FooteL2RankThree)
    (hSolv : FooteL2InvolutionSolvable) (hSol : Sol76T13.SolomonThm13Simple)
    (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hFI : FooteFourgroupInner) (hRO : FooteL2RootedOuter)
    (hAR : FooteAutRankThree) (hGen : FooteL2FourgroupGeneration)
    (h410 : FooteLemma410Statement) {t : G} (hce : FooteCounterexample G t L)
    (hsimple : IsSimpleGroup G) (hrank2 : ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2)
    (hS : ∀ A ∈ footeFamilyOf L, A ∈ solomonKStar G) :
    ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥(coreActionKernel A) ≤ 2 := by
  intro A hA
  by_contra hlt
  push Not at hlt
  have hsec := FooteSec4.of_family hLB hCI hGA hGC hSA hOut hAb h9 hRk hSolv hSol hce hsimple
    hrank2 hS
  obtain ⟨E, hE, hE2, hE8'⟩ := exists_card_eight_of_le_pRank (H := coreActionKernel A) (by omega)
  obtain ⟨z, hz⟩ := hA.1
  exact false_of_isFooteM hsec h47 hST hAsc h2An hA5 hE8 hK hcalc hFI hRO hAR hGen h410
    (M := footeME L E) ⟨z, A, E, hz, hA, hE2, hE8', hE, rfl⟩

theorem footeRankBound_of_inputs
    (hLB : FooteLBalanceInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hOut : FooteL2OutAbelian)
    (hAb : FooteL2AbelianCore) (h9 : FooteL2NineOddInner) (hRk : FooteL2RankThree)
    (hSolv : FooteL2InvolutionSolvable) (hSol : Sol76T13.SolomonThm13Simple)
    (hM3 : FooteSolomonFamilyInput) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hFI : FooteFourgroupInner) (hRO : FooteL2RootedOuter)
    (hAR : FooteAutRankThree) (hGen : FooteL2FourgroupGeneration)
    (h410 : FooteLemma410Statement) : FooteRankBound :=
  fun _ _ _ t L hmin hce hsimple hrank2 =>
    footeRankBound_at hLB hCI hGA hGC hSA hOut hAb h9 hRk hSolv hSol h47 hST hAsc h2An hA5 hE8 hK
      hcalc hFI hRO hAR hGen h410 hce hsimple hrank2 (hM3 _ t L hmin hce hsimple hrank2)

theorem footeRankBound_of_open_inputs
    (hLB : FooteLBalanceInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (hSA : SolAltLit.SchurAlternatingMultiplierInput)
    (hOut : FooteL2OutAbelian) (hAb : FooteL2AbelianCore) (h9 : FooteL2NineOddInner)
    (hRk : FooteL2RankThree) (hSolv : FooteL2InvolutionSolvable)
    (hSol : Sol76T13.SolomonThm13Simple)
    (hM3 : FooteSolomonFamilyInput) (h47 : FooteThm47Statement)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput)
    (hE8 : FooteL2FourgroupE8) (hcalc : FooteSmallCentralizers) (hFI : FooteFourgroupInner)
    (hRO : FooteL2RootedOuter) (hAR : FooteAutRankThree) (hGen : FooteL2FourgroupGeneration)
    (h410 : FooteLemma410Statement) : FooteRankBound :=
  footeRankBound_of_inputs hLB hCI hGA @Milestones.cl_lit_griess_schur_multipliers_central_covers
    hSA hOut hAb h9 hRk hSolv hSol hM3 h47 GSThmB.suzukiTausskyInput hAsc h2An
    GSThmB.aschbacherTheorem5Input_holds hE8 AschbacherKnownGroup.knownGroupFacts_holds hcalc hFI
    hRO hAR hGen h410

end CFSG.ComponentClassification.FooteLit
