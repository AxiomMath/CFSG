module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1CaseA
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Close
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSetup

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

theorem standardComponentOddCore_eq_bot_of {G : Type} [Group G] {K : Subgroup G}
    (h : AS76b.oddCoreIn K = ⊥) : standardComponentOddCore K = ⊥ := by
  have e : CFSG.Assembly.oddCore K = standardComponentOddCore K := rfl
  rw [← e]
  rw [AS76b.oddCoreIn] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h

theorem dempwolffOddCore_of
    (hF : Foundation) (hS3 : B1Stage3) : DempwolffOddCore := by
  intro G _ _ L hM T₀ hT₀ h4'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (normalizer (L : Set G))
  have h3 : Sec3 G L T := ⟨hM.hyp, hT⟩
  have h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4 := by
    rw [h3.isSylowOf_T₀.card_eq, ← hT₀.card_eq, h4']
  have hZ : Odd (Nat.card (center L)) := hM.hyp.odd_card_center hF
  refine standardComponentOddCore_eq_bot_of ?_
  by_contra hW
  obtain ⟨L₀, hfr⟩ := hM.exists_b1Frame h3 hF hZ h4 hW
  obtain ⟨eS⟩ := hM.nonempty_mulEquiv_sz
  have hX := h3.facts_of_sz hF hZ hM.one_le eS
  obtain ⟨hA8, -, -⟩ := hX.sylow h3
  obtain ⟨f, hfA, hf1⟩ : ∃ f ∈ gmsA L T, f ≠ 1 := by
    by_contra h
    push Not at h
    have hb : gmsA L T = ⊥ := (eq_bot_iff_forall _).mpr h
    rw [hb, card_bot] at hA8
    norm_num at hA8
  have hstar : centralizer ({f} : Set G) ≤
      normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G) := by
    by_cases hP : AS76b.oddCoreIn (centralizer ({f} : Set G)) = ⊥
    · exact hS3 G L T L₀ hM h3 hF h4 hW hfr f hfA hf1 hP
    · exact hM.centralizer_le_normalizer_of_oddCoreIn_ne_bot h3 hF hZ h4 hfr hfA hf1 hP
  exact hM.false_of_b1Frame h3 hF hZ h4 hW hfr ⟨f, hfA, hf1, hstar⟩

end CFSG.ComponentClassification.GMS78
