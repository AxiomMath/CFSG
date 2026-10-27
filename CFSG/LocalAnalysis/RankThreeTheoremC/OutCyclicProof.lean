module

public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicLift
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoRankAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutElemRankCatalog
public import CFSG.RankThree.PartOne.S11d.OutStructure
public import CFSG.RankThree.PartOne.S11d.OddExcAll
public import CFSG.RankThree.PartOne.AUTSL.OddOutGaps
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.RankThree.PartOne.S11d.SporadicOut
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.OutStructure
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo)

theorem center_eq_bot_of_simple {K : Type} [Group K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) : Subgroup.center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center K := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem localRankLeTwo_of_card_le {K : Type} [Group K] {p : ℕ} (hp : p.Prime)
    (h : ∀ A : Subgroup K, CFSG.Open.IsElemAbelian p A → Nat.card A ≤ p) :
    LocalRankLeTwo p K := by
  intro R hR hcard _ _ _ _
  have h1 := h R ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p R).1 hR)
  rw [hcard] at h1
  have h2 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at h2
  omega

theorem statedClassicalModel_psl_quot {K : Type} [Group K] (hZ : Subgroup.center K = ⊥)
    {n p f : ℕ} (h : StatedClassicalModel K .PSL n p f) :
    StatedClassicalModel (K ⧸ Subgroup.center K) .PSL n p f := by
  obtain ⟨hadm, F, i1, i2, hF, ⟨e⟩⟩ := h
  refine ⟨hadm, F, i1, i2, hF, ?_⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩

theorem statedClassicalModel_psu_quot {K : Type} [Group K] (hZ : Subgroup.center K = ⊥)
    {n p f : ℕ} (h : StatedClassicalModel K .PSU n p f) :
    StatedClassicalModel (K ⧸ Subgroup.center K) .PSU n p f := by
  obtain ⟨hadm, F, i1, i2, hF, ⟨e⟩⟩ := h
  refine ⟨hadm, F, i1, i2, hF, ?_⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩

section Even


theorem outPChain_or_not_dvd_of_even {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hrk : CFSG.pRank p K ≤ 1) (hZ : Subgroup.center K = ⊥) {t : StatedLieTag}
    {n f : ℕ} (hmodel : LieModel K t n 2 f) :
    OutPChain p K ∨ ¬ p ∣ Nat.card (Outer K) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  rcases hmodel with ⟨ht, hcl⟩ | ⟨hn0, ht, hch⟩ | ⟨hn0, ht, hree⟩ | ⟨hn0, ht, hsz⟩
  · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · by_cases hn : n = 2
      · subst hn
        exact Or.inl (outPNice_PSL_two hp hcl).toChain
      · obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hcl
        exact Or.inl (outPNice_PSL_ge_three hp hp2 (by omega) hcl
          (not_dvd_gcd_psl_of_pRank hp hp5 hrk (statedClassicalModel_psl_quot hZ hcl))).toChain
    · exact Or.inl (outPNice_PSU hp hcl
        (not_dvd_gcd_psu_of_pRank hp hp5 hrk (statedClassicalModel_psu_quot hZ hcl))).toChain
    · by_cases hn : n = 2
      · subst hn
        exact Or.inl (outPNice_PSp_two hp hcl).toChain
      · obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hcl
        exact Or.inl (outPNice_PSp_ge_three hp (by omega) hcl).toChain
    · obtain ⟨⟨-, -, -, hp2'⟩, -⟩ := id hcl
      exact absurd rfl hp2'
    · obtain ⟨⟨-, -, hn4⟩, -⟩ := id hcl
      by_cases hn : n = 4
      · subst hn
        exact Or.inl (outPChain_POmegaPlus_four hp (by omega) hcl)
      · exact Or.inl (outPNice_POmegaPlus_ge_five hp hp2 (by omega) hcl).toChain
    · obtain ⟨⟨-, -, hn4⟩, -⟩ := id hcl
      exact Or.inl (outPNice_POmegaMinus hp hp2 hn4 hcl).toChain
  · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (outPNice_G2 hp hch).toChain
    · exact Or.inl (outPNice_F4 hp hch).toChain
    · exact Or.inl (outPNice_E6 hp hp3 hp2 hch).toChain
    · exact Or.inl (outPNice_E7 hp hch).toChain
    · exact Or.inl (outPNice_E8 hp hch).toChain
    · exact Or.inl (outPNice_twistedE6 hp hp3 hch).toChain
    · exact Or.inl (outPNice_trialityD4 hp hch).toChain
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · obtain ⟨⟨-, -, -, h23, -⟩, -⟩ := id hree
      omega
    · exact Or.inl (outPNice_twistedF4 hp hree).toChain
    · refine Or.inr fun hdvd => ?_
      obtain ⟨k, hk⟩ := (Sporadic.Schreier.Tits.AT_Tits_model_Schreier K 2 f hree).1.exists_card_eq
      rw [hk] at hdvd
      have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hdvd)
      omega
  · subst ht
    exact Or.inl (outPNice_Suzuki hp hsz).toChain

end Even

section Odd


theorem outPChain_of_odd {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hLR : LocalRankLeTwo p K) {t : StatedLieTag} {n ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hmodel : LieModel K t n ℓ f) : OutPChain p K := by
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  rcases hmodel with ⟨ht, hcl⟩ | ⟨hn0, ht, hch⟩ | ⟨hn0, ht, hree⟩ | ⟨hn0, ht, hsz⟩
  · cases t
    · by_cases hn2 : n = 2
      · subst hn2
        exact (outPNice_PSL_two_odd hp hp3 hℓ2 hcl).toChain
      · have hn3 : 3 ≤ n := by
          have := hcl.1.2.2.1
          omega
        by_cases hdiag : p ∣ Nat.gcd n (ℓ ^ f - 1)
        · exact (OddRank.not_localRankLeTwo_psl_odd hp hp3 hℓ2 hcl
            (hdiag.trans (Nat.gcd_dvd_left _ _)) (hdiag.trans (Nat.gcd_dvd_right _ _)) hLR).elim
        · exact (outPNice_PSL_ge_three_odd hp hp2 hn3 hcl hdiag).toChain
    · by_cases hdiag : p ∣ Nat.gcd n (ℓ ^ f + 1)
      · exact (OddRank.not_localRankLeTwo_psu_odd hp hp3 hℓ2 hcl
          (hdiag.trans (Nat.gcd_dvd_left _ _)) (hdiag.trans (Nat.gcd_dvd_right _ _)) hLR).elim
      · exact (outPNice_PSU_odd hp hcl hdiag).toChain
    · by_cases hn2 : n = 2
      · subst hn2
        exact AUTSL.oddOutGaps.1 p K ℓ f hp hp5 hℓ2 hcl
      · have hn3 : 3 ≤ n := by
          have := hcl.1.2.2.1
          omega
        exact (outPNice_PSp_ge_three_odd hp hp2 hn3 hcl).toChain
    · exact (outPNice_POmegaOdd_gen hp hp5 hcl).toChain
    · by_cases hn4 : n = 4
      · subst hn4
        exact outPChain_POmegaPlus_four_gen hp hp5 hcl
      · have hn5 : 5 ≤ n := by
          have := hcl.1.2.2
          omega
        exact (outPNice_POmegaPlus_gen_ge_five hp hp5 hn5 hcl).toChain
    · exact (outPNice_POmegaMinus_gen hp hp5 hcl).toChain
    all_goals exact hcl.2.elim
  · exact (oddExceptionalOut_holds p K t ℓ f hp hp5 hℓ hℓ2 ht hch).toChain
  · cases t
    case twistedG2 =>
      have h3 : ℓ = 3 := hree.1.2.2.2.1
      subst h3
      exact AUTSL.oddOutGaps.2 p K f hp hp5 hree
    case twistedF4 => exact absurd hree.1.2.2.2.1 hℓ2
    case Tits => exact absurd hree.1.2.2.2.1 hℓ2
    all_goals
      obtain ⟨-, a, -, hm⟩ := hree
      exact hm.elim
  · exact absurd hsz.1 hℓ2

end Odd

section Final


theorem kFactOutCyclicGe5_holds :
    ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      CFSG.Open.IsCatalogGroup K → ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ T : Sylow p K,
        IsCyclic ↥(T : Subgroup K) → CFSG.Open.pRank p (⊤ : Subgroup (Outer K)) ≤ 1 := by
  intro K _ _ hs hnab hcat p hp hp5 T hT
  have : IsSimpleGroup K := hs
  have : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center K = ⊥ := center_eq_bot_of_simple hnab
  have hA : ∀ A : Subgroup K, CFSG.Open.IsElemAbelian p A → Nat.card A ≤ p := fun A hA =>
    CFSG.AGLEmbedding.card_le_of_isElemAbelian_of_isCyclic_sylow T hT hA
  have hrk : CFSG.pRank p K ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.pRank_le hp.one_lt fun A _ hA' => by
      rw [pow_one]
      exact hA A hA'
  rcases PlaneCases.catalog_cases (TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · have hout : Nat.card (Outer K) ≤ 4 :=
      (Nat.card_congr (equivalence e).toEquiv).trans_le (card_outer_alternating_le_four hn5)
    exact pRank_outer_le_one_of_outer_small hp (Or.inl (by nlinarith))
  · by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      rcases outPChain_or_not_dvd_of_even hp hp5 hrk hZ hmodel with h | h
      · exact pRank_outer_le_one_of_outPChain hp h
      · exact pRank_outer_le_one_of_outer_small hp (Or.inr h)
    · exact pRank_outer_le_one_of_outPChain hp
        (outPChain_of_odd hp hp5 (localRankLeTwo_of_card_le hp hA) hadm.1 hℓ2 hmodel)
  · rcases sporadicOutSmall_of_simple SPOR.sporadicOuterOrderLeTwoSimple_holds s K hnab ⟨e⟩ with
      hlt | hno
    · exact pRank_outer_le_one_of_outer_small hp (Or.inl (by nlinarith))
    · exact pRank_outer_le_one_of_outer_small hp (Or.inr (hno p hp hp5))

end Final

section Coprime


theorem pRank_outer_le_one_of_not_dvd {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) :
    CFSG.Open.pRank p (⊤ : Subgroup (Outer K)) ≤ 1 :=
  CFSG.SectionRank.pRank_le hp.one_lt fun _ _ hE => by
    rw [pow_one]
    exact card_le_of_outer_of_mulAut hp hpK
      (fun A hA => CFSG.AGLEmbedding.OutElemRank.elementaryRankAtMostOne_of_catalogGroup hnab hcat
        hp hp2 hpK A ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA)) hE

end Coprime

end CFSG.LocalAnalysis.RankThreeTheoremC
