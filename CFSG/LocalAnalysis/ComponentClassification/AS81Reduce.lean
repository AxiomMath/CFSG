module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13Basic
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Setup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourReduce

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G]

theorem oddCoreFreeConclusion_of_sup_ne_top {A : Subgroup G}
    (hB : Base G A) (hL : TypeL34 (rankTwoQuot A)) (hbelow : L34GeneralBelow (Nat.card G))
    {R : Subgroup G} (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hne : rankTwoX A ⊔ R ≠ ⊤) : OddCoreFreeConclusion A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hB.hyp.standard
  obtain ⟨hXF, hXs⟩ := AS76b.asc08Lemma34 G A hB.hyp31
  have hXsimple : IsSimpleGroup ↥(rankTwoX A) := by
    rw [show rankTwoX A = CFSG.generalizedFitting G from hXF]
    exact hXs
  have hAX : A ≤ rankTwoX A := le_normalClosure
  have hAG₁ : A ≤ rankTwoX A ⊔ R := hAX.trans le_sup_left
  have hRG₁ : R ≤ rankTwoX A ⊔ R := le_sup_right
  have hcard : Nat.card (rankTwoX A ⊔ R : Subgroup G) < Nat.card G := by
    have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)
    rwa [card_top] at this
  have hA1 : ∀ {B : Subgroup G}, A ≤ B → B = ⊥ → False := by
    intro B hAB hB1
    rw [hB1, le_bot_iff] at hAB
    apply hB.hyp.not_normal
    rw [hAB]
    infer_instance
  have heven : Even (Nat.card (centralizer (A : Set G) ⊓ (rankTwoX A ⊔ R) : Subgroup G)) := by
    have hR1 : R ≠ ⊥ :=
      AS76b.isSylowOf_ne_bot_of_even hR (AS76b.tightlyEmbedded_centralizer hstd).1
    have h2R : 2 ∣ Nat.card R := by
      rcases hR.isPGroup.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hR1
      · exact h
    exact even_iff_two_dvd.mpr (h2R.trans (Subgroup.card_dvd_of_le (le_inf hR.le hRG₁)))
  have hstd₁ := GMS78.standard_subgroupOf hstd hAG₁ heven
  have hnn : ¬ (A.subgroupOf (rankTwoX A ⊔ R)).Normal := by
    intro hn
    have hnX : (A.subgroupOf (rankTwoX A)).Normal := by
      constructor
      intro a ha x
      have h1 := hn.conj_mem ⟨(a : G), hAG₁ ha⟩ ha ⟨(x : G), le_sup_left (b := R) x.2⟩
      rw [mem_subgroupOf] at h1 ⊢
      simpa using h1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf (rankTwoX A)) with h | h
    · rw [subgroupOf_eq_bot] at h
      exact hA1 le_rfl (le_bot_iff.mp fun a ha => h.le_bot ⟨ha, hAX ha⟩)
    · apply hB.hyp.not_normal
      rw [le_antisymm hAX (subgroupOf_eq_top.mp h)]
      infer_instance
  have hrank₁ : 2 ≤ Open.pRank 2 (centralizer ((A.subgroupOf (rankTwoX A ⊔ R) :
      Subgroup ↥(rankTwoX A ⊔ R)) : Set ↥(rankTwoX A ⊔ R))) := by
    obtain ⟨U, hUK, hU, hU4⟩ := RankTwoSporadic.exists_four_le_of_two_le_pRank hB.hyp.rank
    obtain ⟨c, -, hcU⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hR
      (isPGroup_two_of_isElemAbelian hU) hUK
    have hEG₁ : rightConjugate U c ≤ rankTwoX A ⊔ R := hcU.trans hRG₁
    refine CFSG.SectionRank.le_pRank one_lt_two
      (E := (rightConjugate U c).subgroupOf (rankTwoX A ⊔ R)) ?_
      (isElemAbelian_subgroupOf (AS76b.isElemAbelian_rightConjugate hU c) _) ?_
    · intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (mem_centralizer_iff.mp (hR.le (hcU (mem_subgroupOf.mp hx))) y
        (mem_subgroupOf.mp hy))
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hU4, ← rightConjugate_card U c]
      exact Nat.card_congr (subgroupOfEquivOfLe hEG₁).toEquiv
  have hH₁ : RankTwoHypNF ↥(rankTwoX A ⊔ R) (A.subgroupOf (rankTwoX A ⊔ R)) :=
    ⟨hstd₁, hnn, hrank₁⟩
  let eA : ↥(A.subgroupOf (rankTwoX A ⊔ R)) ≃* ↥A := subgroupOfEquivOfLe hAG₁
  have hL₁ : TypeL34 (rankTwoQuot (A.subgroupOf (rankTwoX A ⊔ R))) :=
    statedClassicalModel_of_mulEquiv
      (QuotientGroup.congr (center _) (center _) eA (Subgroup.map_center_eq eA)) hL
  have h1 := hbelow _ _ hcard hH₁ hL₁
  have hle : (rankTwoX (A.subgroupOf (rankTwoX A ⊔ R))).map (rankTwoX A ⊔ R).subtype ≤
      rankTwoX A := by
    rw [map_le_iff_le_comap]
    have : ((rankTwoX A).comap (rankTwoX A ⊔ R).subtype).Normal :=
      (normalClosure_normal (s := (A : Set G))).comap _
    exact normalClosure_le_normal fun a ha => hAX (mem_subgroupOf.mp ha)
  have hX₁ : (rankTwoX (A.subgroupOf (rankTwoX A ⊔ R))).map (rankTwoX A ⊔ R).subtype =
      rankTwoX A := by
    refine le_antisymm hle ?_
    have hnN : (((rankTwoX (A.subgroupOf (rankTwoX A ⊔ R))).map
        (rankTwoX A ⊔ R).subtype).subgroupOf (rankTwoX A)).Normal := by
      constructor
      intro n hn x
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨m, hm, hmn⟩ := hn
      have hx₁ : (x : G) ∈ rankTwoX A ⊔ R := le_sup_left (b := R) x.2
      refine ⟨⟨x, hx₁⟩ * m * ⟨x, hx₁⟩⁻¹, (normalClosure_normal).conj_mem m hm _, ?_⟩
      simp [← hmn]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((rankTwoX (A.subgroupOf (rankTwoX A ⊔ R))).map
        (rankTwoX A ⊔ R).subtype).subgroupOf (rankTwoX A)) with h | h
    · exfalso
      rw [subgroupOf_eq_bot] at h
      refine hA1 (B := ⊥) (fun a ha => h.le_bot ⟨?_, hAX ha⟩) rfl
      exact ⟨⟨a, hAG₁ ha⟩, le_normalClosure ha, rfl⟩
    · exact subgroupOf_eq_top.mp h
  let eX : ↥(rankTwoX (A.subgroupOf (rankTwoX A ⊔ R))) ≃* ↥(rankTwoX A) :=
    ((rankTwoX (A.subgroupOf (rankTwoX A ⊔ R))).equivMapOfInjective _
      (rankTwoX A ⊔ R).subtype_injective).trans (MulEquiv.subgroupCongr hX₁)
  refine oddCoreFreeConclusion_of_l34Conclusion hB.oddCore ?_
  unfold L34Conclusion IsSporadic at h1 ⊢
  rcases h1 with ⟨⟨e⟩, h3⟩ | ⟨⟨eZ⟩, ⟨e⟩⟩
  · refine Or.inl ⟨⟨(QuotientGroup.congr (center _) (center _) eX
      (Subgroup.map_center_eq eX)).symm.trans e⟩, ?_⟩
    rwa [← Nat.card_congr (Subgroup.centerCongr eX).toEquiv]
  · exact Or.inr ⟨⟨(Subgroup.centerCongr eA).symm.trans eZ⟩, ⟨eX.symm.trans e⟩⟩

end CFSG.ComponentClassification.AS81
