module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndFacts
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1End175
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndData

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open scoped commutatorElement

theorem isConj_conj {α : Type*} [Group α] (c s : α) : IsConj s (c * s * c⁻¹) :=
  isConj_iff.mpr ⟨c, rfl⟩

theorem sporadicCaseOdd_Co1_of_check
    (hE : co1EndCheck co1EndD co1EndIdx co1EndDB = true)
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .Co1 := by
  intro G _ _ A hH hodd ⟨e⟩
  have : Finite Blueprint.NativeSporadic.Co1 := CFSG.Sporadic.Co1.fam_co1_simplicity.1
  have hII : YCensus (⊤ : Subgroup Blueprint.NativeSporadic.Co1) (· ≤ ⊤) :=
    fun E _ _ h => absurd le_top h
  have hyp : AS76b.Hyp31 A :=
    ⟨hH.standard, hypII_of_yCensus co1AutModel hII hH.standard.1.1 e, hodd,
      by have := hH.rank; omega, hH.not_normal⟩
  obtain ⟨ψ, hψ⟩ := exists_isActionHom co1AutModel hyp.standard.1.1 e
  obtain ⟨g, hg, RK, T, hR, hT, hTN, -, hTR, -, -⟩ :=
    AS76b.section3Config_of h32 h33 RankTwoFoundation.asc75Theorem4 AS76b.asc08Lemma34 G A hyp
  obtain ⟨c₁, c₂, a₀, b₀, hF⟩ := co1_swapFacts_of_check hE
  refine false_of_swapFacts h32 hyp co1AutModel e hψ hF co1_yCensus17 ?_ hg hR hT hTN ?_
  · rintro t ht2 ⟨w, hw⟩
    refine co1_odd_card_center h32 hyp e hψ ht2 ?_
    rw [hw]
    exact isCo1TwoB_of_isConj isCo1TwoB_co1E1 (isConj_conj w co1E1)
  · intro t ht r hr
    have h1 : ⁅t, r⁆ ∈ ⁅T, RK⁆ := commutator_mem_commutator ht hr
    rw [hTR, mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1

end CFSG.ComponentClassification.RankTwoSporadic.Co1
