module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOne
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78Inputs

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem card_center_le_two_of_alt_seven (hSA : SolAltLit.SchurAlternatingMultiplierInput)
    {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) (hZ : IsPGroup 2 (center Q))
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin 7)) : Nat.card (center Q) ≤ 2 := by
  obtain ⟨hperf, -⟩ := hQ
  have hdvd := card_center_dvd_card_hopfMultiplier e
  have h6 : (if 7 = 6 ∨ 7 = 7 then 6 else 2) = 6 := by decide
  rw [(hSA 7 (by norm_num)).2, h6] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ
  rw [hk] at hdvd ⊢
  by_contra h
  have h4 : 2 ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by
    by_contra hk2
    exact h (by interval_cases k <;> norm_num))
  have := h4.trans hdvd
  norm_num at this

theorem card_center_le_two_of_footeFamilyType (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (G : Type) [Group G] [Finite G]
    (B : Subgroup G) (hB : ∃ b : G, IsTwoComponentAt b B) (hfam : FooteFamilyType B) :
    Nat.card (center (B ⧸ pPrimeCore 2 B)) ≤ 2 := by
  obtain ⟨b, -, hBC, hBpc⟩ := hB
  have hBq := isQuasisimple_quotient_of_isPComponent hBC hBpc
  have hZp := isPGroup_center_quotient_pPrimeCore ↥B
  obtain ⟨e⟩ := nonempty_fusionZStar_quotient_equiv ↥B
  rcases hfam with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, -, -, hL⟩
  · exact card_center_le_two_of_alt_seven hSA hBq hZp (e.symm.trans e7)
  · exact card_center_le_two_of_lieModel_psl_two hGA hGC hBq hZp e.symm hp hp2 hL

theorem family_rank_two_and_kernel_rank_of_simple_counterexample
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {t : G} {L : Subgroup G} (hce : FooteCounterexample G t L)
    (hLB : FooteLBalanceInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) :
    (∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) ∧
      2 ≤ CFSG.pRank 2 ↥(coreActionKernel L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht : orderOf t = 2 := hce.1.2.2.1.1
  have hLt : L ≤ Subgroup.centralizer ({t} : Set G) := hce.1.2.2.1.2.1
  have hLpc : IsPComponent 2 (L.subgroupOf (Subgroup.centralizer ({t} : Set G))) :=
    hce.1.2.2.1.2.2
  have hLq := isQuasisimple_quotient_of_isPComponent hLt hLpc
  have hLna := exists_mul_ne_mul_of_isQuasisimple hLq
  have hLne : L ≠ ⊥ := by
    rintro rfl
    obtain ⟨a, b, hab⟩ := hLna
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [show a' = 1 from Subtype.ext ((Subgroup.mem_bot).1 a'.2),
      show b' = 1 from Subtype.ext ((Subgroup.mem_bot).1 b'.2)]
  have hna : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hLna
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨(a' : G), (b' : G), fun h => hab ?_⟩
    exact congrArg (QuotientGroup.mk' (pPrimeCore 2 ↥L)) (Subtype.ext h)
  have htop : conjClosure L (pLayer G 2) = ⊤ := by
    rw [pLayer_two_eq_top_of_isSimpleGroup hna ht, conjClosure_top_eq_top hLne]
  have hgen : conjClosure L (pLayer G 2) ⊔ zpowers t = ⊤ := by
    rw [htop]
    simp
  have hO : pPrimeCore 2 G = ⊥ := pPrimeCore_two_eq_bot_of_isSimpleGroup ht
  have hsimpleG₀ : IsSimpleGroup ↥(conjClosure L (pLayer G 2)) :=
    isSimpleGroup_conjClosure_of_counterexample hce hO hgen
  have hβ : ∀ (X : Type) [Group X] [Finite X] (B : Subgroup X),
      (∃ b : X, IsTwoComponentAt b B) → FooteFamilyType B →
        Nat.card (center (B ⧸ pPrimeCore 2 B)) ≤ 2 :=
    fun X _ _ B hB hfam =>
      card_center_le_two_of_footeFamilyType hGA hGC hSA X B hB hfam
  exact ⟨family_rank_two_of_simple_conjClosure hLB hCI hβ hce hgen hsimpleG₀,
    two_le_pRank_coreActionKernel_of_counterexample hce htop⟩

theorem footeRankOneBranch_of_inputs (hLB : FooteLBalanceInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) : FooteRankOneBranch :=
  footeRankOneBranch_of_multiplierBound hLB hCI
    (card_center_le_two_of_footeFamilyType hGA hGC hSA)

theorem footeInitialReductions_of_inputs (h1 : FooteOddCoreReduction)
    (h2 : FooteComponentReduction) (h4 : FooteOuterReduction) (hLB : FooteLBalanceInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) : FooteInitialReductions :=
  footeInitialReductions_of_steps h1 h2 (footeRankOneBranch_of_inputs hLB hCI hGA hGC hSA) h4

end CFSG.ComponentClassification.FooteLit
