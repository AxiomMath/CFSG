module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneLayer
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInitial
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneTools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aConjFix

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem exists_classical_of_pRank_le_one (hLB : FooteLBalanceInput)
    (hβ : ∀ B : Subgroup G, (∃ b : G, IsTwoComponentAt b B) → FooteFamilyType B →
      Nat.card (center (B ⧸ pPrimeCore 2 B)) ≤ 2)
    {z : G} {A : Subgroup G} (hAmax : FootePointedMaximal z A) (hAfam : FooteFamilyType A)
    (hrank : CFSG.pRank 2 ↥A ≤ 1) :
    ∃ (x : G) (X : Subgroup G), IsTwoComponentAt x X ∧ x ∈ X ∧ CFSG.pRank 2 ↥X ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzA := hAmax.1
  by_cases hz : z ∈ A
  · exact ⟨z, A, hzA, hz, hrank⟩
  obtain ⟨a, haA, ha⟩ := exists_involution_of_isTwoComponentAt hzA
  have haK : a ∈ coreActionKernel A := mem_coreActionKernel_of_pRank_le_one hzA hrank haA ha
  have hne : z ≠ a := fun h => hz (h ▸ haA)
  have hza : z * a = a * z := (mem_centralizer_singleton_iff.mp (hzA.2.1 haA)).symm
  obtain ⟨B, hBa, hstep, ⟨eAB⟩, hcase⟩ :=
    footeStep_cases_index_of_maximal hLB hAmax ha hza hne haK
  have hBmax : FootePointedMaximal a B := hAmax.of_reach (FootePointedReach.single hstep)
  have hBfam : FooteFamilyType B := footeFamilyType_of_equiv eAB.symm hAfam
  rcases hcase with ⟨-, hBfix⟩ | ⟨hBz, hT, hidx⟩
  ·
    refine ⟨a, B, hBa, hBfix ▸ mem_footeFixed_self haA ha, ?_⟩
    have hBa' : IsTwoComponentAt a (footeFixed A a) := hBfix ▸ hBa
    rw [← hBfix, pRank_footeFixed_eq hzA ha haK hBa']
    exact hrank
  obtain ⟨-, hBC, hBpc⟩ := id hBa
  have hBq := isQuasisimple_quotient_of_isPComponent hBC hBpc
  have hAq := isQuasisimple_quotient_of_isPComponent hzA.2.1 hzA.2.2
  set T := UnbalancedGS.gsFixedLayer A a with hTdef
  have hTA : Nat.card (T ⧸ pPrimeCore 2 T) = Nat.card (A ⧸ pPrimeCore 2 A) := by
    have hTL : T ≤ A := (UnbalancedGS.gsFixedLayer_le_inf A a).trans inf_le_left
    obtain ⟨-, eT, -⟩ := restriction_quotient_mulEquiv hTL
      (gsFixedLayer_sup_map_pPrimeCore ha hAq haK.1 haK.2)
    exact Nat.card_congr eT.toEquiv
  have hcardAB : Nat.card (A ⧸ pPrimeCore 2 A) ≤ Nat.card (B ⧸ pPrimeCore 2 B) := by
    rw [← hTA]
    exact hidx
  have hZA : center (A ⧸ pPrimeCore 2 A) ≠ ⊥ := center_ne_bot_of_mem_coreActionKernel haA ha haK
  have hZB : center (B ⧸ pPrimeCore 2 B) ≠ ⊥ := by
    intro hbot
    have h4 : 1 < Nat.card (center (A ⧸ pPrimeCore 2 A)) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hZA
    have h5 : Nat.card (center (B ⧸ pPrimeCore 2 B)) = 1 := by
      rw [hbot]; exact Subgroup.card_bot
    have hpos : 0 < Nat.card (B ⧸ Open.fusionZStar B) := Nat.card_pos
    rw [card_quotient_pPrimeCore_eq ↥A, card_quotient_pPrimeCore_eq ↥B,
      Nat.card_congr eAB.toEquiv, h5, one_mul] at hcardAB
    have h6 := Nat.le_of_mul_le_mul_right (hcardAB.trans (Nat.le_of_eq (one_mul _).symm)) hpos
    omega
  have hBrank : CFSG.pRank 2 ↥B ≤ 1 :=
    pRank_le_one_of_center_ne_bot hBq hBfam (hβ B ⟨a, hBa⟩ hBfam) hZB
  by_cases haB : a ∈ B
  · exact ⟨a, B, hBa, haB, hBrank⟩
  obtain ⟨b, hbB, hb⟩ := exists_involution_of_isTwoComponentAt hBa
  have hbK : b ∈ coreActionKernel B := mem_coreActionKernel_of_pRank_le_one hBa hBrank hbB hb
  have hab : a * b = b * a := (mem_centralizer_singleton_iff.mp (hBC hbB)).symm
  have hne' : a ≠ b := fun h => haB (h ▸ hbB)
  have hzCa : z ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hza
  have hBzC : conjugate B z ≤ centralizer ({a} : Set G) := conjugate_le_of_mem hBC hzCa
  have hBzpc : IsPComponent 2 ((conjugate B z).subgroupOf (centralizer ({a} : Set G))) :=
    isPComponent_conjugate_subgroupOf hzCa hBpc
  have hBza : IsTwoComponentAt a (conjugate B z) := ⟨ha, hBzC, hBzpc⟩
  have hbK' : b ∈ coreActionKernel (conjugate B z) :=
    GSThmB.B5a.le_coreActionKernel_of_ne hBzC hBC hBzpc hBpc hBz hbB
  have haT : a ∈ T := mem_gsFixedLayer_self hzA haA ha haK
  have haBB : a ∈ B ⊔ conjugate B z := by
    have h1 : a ∈ twoLayerIn ((B ⊔ conjugate B z) ⊓ centralizer ({z} : Set G)) := hT ▸ haT
    exact (inf_le_left : (B ⊔ conjugate B z) ⊓ centralizer ({z} : Set G) ≤ _)
      (map_subtype_le _ h1)
  have haL : a ∈ twoLayerOf b := mem_twoLayerOf_of_mem_sup ha hb hab hBa hBza hbK hbK' haBB
  obtain ⟨D, hDb, -, -, hcase'⟩ := footeStep_cases_index_of_maximal hLB hBmax hb hab hne' hbK
  rcases hcase' with ⟨-, hDfix⟩ | ⟨hDa, -, -⟩
  · refine ⟨b, D, hDb, hDfix ▸ mem_footeFixed_self hbB hb, ?_⟩
    have hDb' : IsTwoComponentAt b (footeFixed B b) := hDfix ▸ hDb
    rw [← hDfix, pRank_footeFixed_eq hBa hb hbK hDb']
    exact hBrank
  · exfalso
    apply hDa
    obtain ⟨-, hDC, hDpc⟩ := hDb
    exact conjugate_eq_of_mem_normalizer (twoLayerIn_le_normalizer hDC hDpc haL)

theorem family_rank_two_of_simple_conjClosure
    (hLB : FooteLBalanceInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hβ : ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G),
      (∃ b : G, IsTwoComponentAt b B) → FooteFamilyType B →
        Nat.card (center (B ⧸ pPrimeCore 2 B)) ≤ 2)
    {G : Type} [Group G] [Finite G] {t : G} {L : Subgroup G}
    (hce : FooteCounterexample G t L)
    (hgen : conjClosure L (pLayer G 2) ⊔ zpowers t = ⊤)
    (hsimple : IsSimpleGroup ↥(conjClosure L (pLayer G 2))) :
    ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2 := by
  intro A hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨z, hAmax⟩, ⟨eAL⟩⟩ := hA
  obtain ⟨-, hAt, hLA, -, -⟩ := exists_component_of_counterexample hce
  obtain ⟨⟨-, -, ⟨ht, hLt, hLpc⟩, -, hLfam, -⟩, hcon⟩ := hce
  have hAfam : FooteFamilyType A := footeFamilyType_of_equiv eAL hLfam
  have hzA := hAmax.1
  have hAq := isQuasisimple_quotient_of_isPComponent hzA.2.1 hzA.2.2
  by_cases hZ : center (A ⧸ pPrimeCore 2 A) = ⊥
  · exact pRank_eq_two_of_center_eq_bot hAq hAfam hZ
  exfalso
  have hrank := pRank_le_one_of_center_ne_bot hAq hAfam (hβ G A ⟨z, hzA⟩ hAfam) hZ
  obtain ⟨x, X, hX, hxX, hXr⟩ := exists_classical_of_pRank_le_one hLB (hβ G) hAmax hAfam hrank
  generalize hG₀ : conjClosure L (pLayer G 2) = G₀ at *
  have htN : t ∈ normalizer (G₀ : Set G) := mem_normalizer_of_conjugate_eq hAt
  have hXG₀ : X ≤ G₀ := le_of_commutator_eq_self_of_sup_zpowers hgen htN
    (GSThmB.commutator_eq_self_of_isPComponent hX.2.1 hX.2.2)
  have hnonab : ∃ u v : G₀, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ :=
      exists_mul_ne_mul_of_isQuasisimple (isQuasisimple_quotient_of_isPComponent hLt hLpc)
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
    refine ⟨⟨u', hLA u'.2⟩, ⟨v', hLA v'.2⟩, fun h => huv ?_⟩
    have h1 : (u' : G) * v' = v' * u' := congrArg Subtype.val h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      show u' * v' = v' * u' from Subtype.ext (by simpa using h1)]
  have hodd := oddLieType_of_classical_in_subgroup hCI hnonab (hXG₀ hxX) hX.1 hXG₀ hX hxX hXr
  exact hcon (footeConclusion_of_oddLieType hnonab hodd)

theorem footeRankOneBranch_of_multiplierBound (hLB : FooteLBalanceInput)
    (hCI : GSLit.ClassicalInvolutionInput)
    (hβ : ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G),
      (∃ b : G, IsTwoComponentAt b B) → FooteFamilyType B →
        Nat.card (center (B ⧸ pPrimeCore 2 B)) ≤ 2) :
    FooteRankOneBranch := by
  intro G _ _ t L _ hce _ hgen hsimple A hA
  exact family_rank_two_of_simple_conjClosure hLB hCI hβ hce hgen hsimple A hA

end CFSG.ComponentClassification.FooteLit
