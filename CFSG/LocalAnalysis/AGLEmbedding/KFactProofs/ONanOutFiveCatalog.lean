module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutFiveSeries
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutFiveLinear
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutFiveUnitary
import CFSG.RankThree.PartOne.TCB.Final
import CFSG.RankThree.PartOne.S11d.SporadicOut
import CFSG.RankThree.PartOne.SPOR.OuterSimple
import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
import CFSG.RankThree.PartOne.AUTSL.OddOutGaps
import CFSG.RankThree.PartOne.S11d.OddExcAll
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.Sporadic.Schreier.TitsOuterTwo
public import CFSG.Blueprint.Catalog
import CFSG.RankThree.PartOne.S11d.OutEsix
import CFSG.RankThree.PartOne.S11d.OutExceptional

public section

namespace CFSG.AGLEmbedding.OutFive

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.OutStructure CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms

theorem outPlaneSeries_of_outPChain {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (h : OutPChain p X) : OutPlaneSeries p X := by
  refine ⟨Inn X, inner_normal X, ?_, ?_⟩
  · intro R hRN _ hcard hRI
    have hR : R = ⊥ := by
      rw [eq_bot_iff, ← hRI]
      exact le_inf le_rfl hRN
    rw [hR, Subgroup.card_bot] at hcard
    nlinarith
  · intro R hR hcard hRI
    exact PlaneCases.no_plane_of_outPChain hp h R hR hcard hRI

section FamilyCerts


theorem outPlaneSeries_of_lieModel {T : Type} [Group T] [Finite T] {t : StatedLieTag}
    {n ℓ f p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hadm : StatedLieAdmissible t n ℓ f)
    (hmodel : LieModel T t n ℓ f) : OutPlaneSeries p T := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hp3' : 3 < p := by omega
  have chain : OutPChain p T → OutPlaneSeries p T := outPlaneSeries_of_outPChain hp hp5
  rcases hmodel with ⟨ht, hcl⟩ | ⟨-, ht, hch⟩ | ⟨-, ht, hree⟩ | ⟨-, -, hsz⟩
  · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · by_cases hn2 : n = 2
      · subst hn2
        by_cases hℓ : ℓ = 2
        · subst hℓ
          exact chain (outPNice_PSL_two hp hcl).toChain
        · exact chain (outPNice_PSL_two_odd hp hp3' hℓ hcl).toChain
      · have hn3 : 3 ≤ n := by
          have := hcl.1.2.2.1
          omega
        exact outPlaneSeries_PSL_model hp hp2 hn3 hcl
    · exact outPlaneSeries_PSU_model hp hcl
    · by_cases hn2 : n = 2
      · subst hn2
        by_cases hℓ : ℓ = 2
        · subst hℓ
          exact chain (outPNice_PSp_two hp hcl).toChain
        · exact chain (RankThree.PartOne.AUTSL.oddOutGaps.1 p T ℓ f hp hp5 hℓ hcl)
      · have hn3 : 3 ≤ n := by
          have := hcl.1.2.2.1
          omega
        exact chain (outPNice_PSp_ge_three_odd hp hp2 hn3 hcl).toChain
    · exact chain (outPNice_POmegaOdd_gen hp hp5 hcl).toChain
    · by_cases hn4 : n = 4
      · subst hn4
        exact chain (outPChain_POmegaPlus_four_gen hp hp5 hcl)
      · have hn5 : 5 ≤ n := by
          have := hcl.1.2.2
          omega
        exact chain (outPNice_POmegaPlus_gen_ge_five hp hp5 hn5 hcl).toChain
    · exact chain (outPNice_POmegaMinus_gen hp hp5 hcl).toChain
  · by_cases hℓ : ℓ = 2
    · subst hℓ
      simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact chain (outPNice_G2 hp hch).toChain
      · exact chain (outPNice_F4 hp hch).toChain
      · exact chain (outPNice_E6 hp hp3 hp2 hch).toChain
      · exact chain (outPNice_E7 hp hch).toChain
      · exact chain (outPNice_E8 hp hch).toChain
      · exact chain (outPNice_twistedE6 hp hp3 hch).toChain
      · exact chain (outPNice_trialityD4 hp hch).toChain
    · exact chain (oddExceptionalOut_holds p T t ℓ f hp hp5 hadm.1 hℓ ht hch).toChain
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · have h3 : ℓ = 3 := hree.1.2.2.2.1
      subst h3
      exact chain (RankThree.PartOne.AUTSL.oddOutGaps.2 p T f hp hp5 hree)
    · have h2 : ℓ = 2 := hree.1.2.2.2.1
      subst h2
      exact chain (outPNice_twistedF4 hp hree).toChain
    · refine outPlaneSeries_of_outer_small hp5 (Or.inl ?_)
      rw [(CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound T ℓ f hree).2.2.1]
      norm_num
  · have h2 : ℓ = 2 := hsz.1
    subst h2
    exact chain (outPNice_Suzuki hp hsz).toChain

end FamilyCerts

section FullCerts


theorem outPlaneSeries_of_catalogGroup {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup S) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : OutPlaneSeries p S := by
  rcases TCB.tauCetiCatalogBridge S hnab hcat |> PlaneCases.catalog_cases with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd (e.injective (by rw [map_mul, map_mul, mul_comm])) hab
  · have hout : Nat.card (Outer S) ≤ 4 :=
      (Nat.card_congr (equivalence e).toEquiv).trans_le (card_outer_alternating_le_four hn)
    exact outPlaneSeries_of_outer_small hp5 (Or.inl (by omega))
  · exact outPlaneSeries_of_lieModel hp hp5 hadm hmodel
  · rcases sporadicOutSmall_of_simple SPOR.sporadicOuterOrderLeTwoSimple_holds s S hnab ⟨e⟩ with
      hlt | hno
    · exact outPlaneSeries_of_outer_small hp5 (Or.inl hlt)
    · exact outPlaneSeries_of_outer_small hp5 (Or.inr (hno p hp hp5))

end FullCerts

end CFSG.AGLEmbedding.OutFive
