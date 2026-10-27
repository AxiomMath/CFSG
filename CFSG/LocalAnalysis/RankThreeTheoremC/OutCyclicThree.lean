module

public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThreeFamilies
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicEsix
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicDFour
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicTwE6
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuter
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.OutStructure
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo)
section Lie

theorem outPChain_or_not_dvd_three {K : Type} [Group K] [Finite K]
    (hrk : ∀ A : Subgroup K, CFSG.Open.IsElemAbelian 3 A → Nat.card A ≤ 3)
    {t : StatedLieTag} {n ℓ f : ℕ} (hadm : StatedLieAdmissible t n ℓ f)
    (hmodel : LieModel K t n ℓ f) :
    OutPChain 3 K ∨ ¬ 3 ∣ Nat.card (Outer K) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hnine : ∀ A : Subgroup K, CFSG.Open.IsElemAbelian 3 A → Nat.card A = 3 ^ 2 → False :=
    fun A hA hc => by
      have := hrk A hA
      rw [hc] at this
      omega
  have hℓ : ℓ.Prime := hadm.1
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    rcases hmodel with ⟨ht, hcl⟩ | ⟨hn0, ht, hch⟩ | ⟨hn0, ht, hree⟩ | ⟨hn0, ht, hsz⟩
    · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · by_cases hn : n = 2
        · subst hn
          exact Or.inl (outPNice_PSL_two hp hcl).toChain
        · obtain ⟨⟨-, -, hn2, -⟩, -⟩ := id hcl
          by_cases hd : 3 ∣ Nat.gcd n (2 ^ f - 1)
          · obtain ⟨A, hA, hc⟩ := exists_nine_of_psl hcl (hd.trans (Nat.gcd_dvd_left _ _))
              (hd.trans (Nat.gcd_dvd_right _ _))
            exact (hnine A hA hc).elim
          · exact Or.inl (outPNice_PSL_ge_three hp hp2 (by omega) hcl hd).toChain
      · by_cases hd : 3 ∣ Nat.gcd n (2 ^ f + 1)
        · obtain ⟨A, hA, hc⟩ := exists_nine_of_psu hcl (hd.trans (Nat.gcd_dvd_left _ _))
            (hd.trans (Nat.gcd_dvd_right _ _))
          exact (hnine A hA hc).elim
        · exact Or.inl (outPNice_PSU hp hcl hd).toChain
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
          obtain ⟨A, hA, hc⟩ := exists_nine_of_POmegaPlus_four hcl
          exact (hnine A hA hc).elim
        · exact Or.inl (outPNice_POmegaPlus_ge_five hp hp2 (by omega) hcl).toChain
      · obtain ⟨⟨-, -, hn4⟩, -⟩ := id hcl
        exact Or.inl (outPNice_POmegaMinus hp hp2 hn4 hcl).toChain
    · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (outPNice_G2 hp hch).toChain
      · exact Or.inl (outPNice_F4 hp hch).toChain
      · by_cases h3 : 3 ∣ 2 ^ f - 1
        · obtain ⟨A, hA, hc⟩ := exists_nine_of_E6 hch h3
          exact (hnine A hA hc).elim
        · exact Or.inl (outPNice_E6_three_of_not_dvd hch h3).toChain
      · exact Or.inl (outPNice_E7 hp hch).toChain
      · exact Or.inl (outPNice_E8 hp hch).toChain
      · obtain ⟨A, hA, hc⟩ := exists_nine_of_twistedE6 hch
        exact (hnine A hA hc).elim
      · exact Or.inl (outPNice_trialityD4 hp hch).toChain
    · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · have h3 : (2 : ℕ) = 3 := hree.1.2.2.2.1
        omega
      · exact Or.inl (outPNice_twistedF4 hp hree).toChain
      · refine Or.inr fun hdvd => ?_
        obtain ⟨k, hk⟩ :=
          (Sporadic.Schreier.Tits.AT_Tits_model_Schreier K 2 f hree).1.exists_card_eq
        rw [hk] at hdvd
        have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hdvd)
        omega
    · subst ht
      exact Or.inl (outPNice_Suzuki hp hsz).toChain
  · rcases hmodel with ⟨ht, hcl⟩ | ⟨hn0, ht, hch⟩ | ⟨hn0, ht, hree⟩ | ⟨hn0, ht, hsz⟩
    · cases t
      · by_cases hn2 : n = 2
        · subst hn2
          exact Or.inl (outPNice_PSL_two_odd_of_ne_two hp hp2 hℓ2 hcl).toChain
        · have hn3 : 3 ≤ n := by
            have := hcl.1.2.2.1
            omega
          by_cases hd : 3 ∣ Nat.gcd n (ℓ ^ f - 1)
          · obtain ⟨A, hA, hc⟩ := exists_nine_of_psl hcl (hd.trans (Nat.gcd_dvd_left _ _))
              (hd.trans (Nat.gcd_dvd_right _ _))
            exact (hnine A hA hc).elim
          · exact Or.inl (outPNice_PSL_ge_three_odd hp hp2 hn3 hcl hd).toChain
      · by_cases hd : 3 ∣ Nat.gcd n (ℓ ^ f + 1)
        · obtain ⟨A, hA, hc⟩ := exists_nine_of_psu hcl (hd.trans (Nat.gcd_dvd_left _ _))
            (hd.trans (Nat.gcd_dvd_right _ _))
          exact (hnine A hA hc).elim
        · exact Or.inl (outPNice_PSU_odd hp hcl hd).toChain
      · by_cases hn2 : n = 2
        · subst hn2
          exact Or.inl (AUTSL.SpTwo.outPNice_PSp_two_odd hp hp2 hℓ2 hcl).toChain
        · have hn3 : 3 ≤ n := by
            have := hcl.1.2.2.1
            omega
          exact Or.inl (outPNice_PSp_ge_three_odd hp hp2 hn3 hcl).toChain
      · exact Or.inl (outPNice_POmegaOdd_of_ne_two hp hp2 hcl).toChain
      · by_cases hn4 : n = 4
        · subst hn4
          obtain ⟨A, hA, hc⟩ := exists_nine_of_POmegaPlus_four hcl
          exact (hnine A hA hc).elim
        · have hn5 : 5 ≤ n := by
            have := hcl.1.2.2
            omega
          exact Or.inl (outPNice_POmegaPlus_ge_five_of_ne_two hp hp2 hn5 hcl).toChain
      · exact Or.inl (outPNice_POmegaMinus_of_ne_two hp hp2 hcl).toChain
      all_goals exact hcl.2.elim
    · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · by_cases h3 : ℓ = 3
        · subst h3
          exact Or.inl (outPNice_G2_three hp hch).toChain
        · exact Or.inl (outPNice_G2_odd hp hℓ2 h3 hch).toChain
      · exact Or.inl (outPNice_F4_odd hp hℓ2 hch).toChain
      · by_cases h3 : 3 ∣ ℓ ^ f - 1
        · obtain ⟨A, hA, hc⟩ := exists_nine_of_E6 hch h3
          exact (hnine A hA hc).elim
        · exact Or.inl (outPNice_E6_three_of_not_dvd hch h3).toChain
      · exact Or.inl (outPNice_E7_gen hp hp2 hch).toChain
      · exact Or.inl (outPNice_E8_gen hp hch).toChain
      · obtain ⟨A, hA, hc⟩ := exists_nine_of_twistedE6 hch
        exact (hnine A hA hc).elim
      · exact Or.inl (outPNice_trialityD4_odd hp hℓ2 hch).toChain
    · cases t
      case twistedG2 =>
        have h3 : ℓ = 3 := hree.1.2.2.2.1
        subst h3
        exact Or.inl (AUTSL.outPNice_twistedG2 hp hree).toChain
      case twistedF4 => exact absurd hree.1.2.2.2.1 hℓ2
      case Tits => exact absurd hree.1.2.2.2.1 hℓ2
      all_goals
        obtain ⟨-, a, -, hm⟩ := hree
        exact hm.elim
    · exact absurd hsz.1 hℓ2

end Lie

section Compose

theorem kFactOutCyclic_holds : KFactOutCyclic := by
  intro K _ _ hs hnab hcat p hp hp2 T hT
  by_cases hp3 : p = 3
  · subst hp3
    have : IsSimpleGroup K := hs
    have : Fact (Nat.Prime 3) := ⟨hp⟩
    have hA : ∀ A : Subgroup K, CFSG.Open.IsElemAbelian 3 A → Nat.card A ≤ 3 := fun A hA =>
      CFSG.AGLEmbedding.card_le_of_isElemAbelian_of_isCyclic_sylow T hT hA
    by_cases hT0 : (T : Subgroup K) = ⊥
    · refine pRank_outer_le_one_of_not_dvd hnab hcat hp hp2 fun hd => ?_
      have h1 := Sylow.card_eq_multiplicity T
      rw [hT0, Subgroup.card_bot] at h1
      have h2 := Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne' hd
      have h3' : 3 ^ (Nat.card K).factorization 3 ≥ 3 ^ 1 :=
        Nat.pow_le_pow_right (by norm_num) h2
      omega
    · rcases PlaneCases.catalog_cases (TCB.tauCetiCatalogBridge K hnab hcat) with
        ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
      · have hout : Nat.card (Outer K) ≤ 4 :=
          (Nat.card_congr (equivalence e).toEquiv).trans_le (card_outer_alternating_le_four hn5)
        exact pRank_outer_le_one_of_outer_small hp (Or.inl (by nlinarith))
      · rcases outPChain_or_not_dvd_three hA hadm hmodel with h | h
        · exact pRank_outer_le_one_of_outPChain hp h
        · exact pRank_outer_le_one_of_outer_small hp (Or.inr h)
      · have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
        obtain ⟨e'⟩ := hbr s
        have hnd := CFSG.AGLEmbedding.not_dvd_card_outer_sporadic hbr s 3 hp hp2
        have hcard : Nat.card (Outer K) =
            Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group) :=
          Nat.card_congr (equivalence (e.trans e')).toEquiv
        exact pRank_outer_le_one_of_outer_small hp (Or.inr (by rw [hcard]; exact hnd))
  · exact kFactOutCyclicGe5_holds K hs hnab hcat p hp
      (hp.five_le_of_ne_two_of_ne_three hp2 hp3) T hT

end Compose

end CFSG.LocalAnalysis.RankThreeTheoremC
