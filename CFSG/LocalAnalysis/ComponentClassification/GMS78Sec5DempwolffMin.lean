module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Swap
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma39
public import CFSG.LocalAnalysis.ComponentClassification.GMS78GapHKS

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.Blueprint

@[expose] def DempwolffRuMin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SzMinCounter G L 1 →
    ∀ T₀ : Subgroup G, IsSylowOf 2 T₀ (centralizer (L : Set G)) → Nat.card T₀ = 4 → False

theorem szRes_of_dempwolffRuMin (hRu : DempwolffRuMin)
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (m : ℕ), SzMinCounter G L m →
      ¬ (m = 1 ∧ ∃ T₀ : Subgroup G, IsSylowOf 2 T₀ (centralizer (L : Set G)) ∧
        Nat.card T₀ = 4) → False) : SzRes := by
  refine szRes_of_szMinCounter fun G _ _ L m hM => ?_
  by_cases hc : m = 1 ∧ ∃ T₀ : Subgroup G, IsSylowOf 2 T₀ (centralizer (L : Set G)) ∧
      Nat.card T₀ = 4
  · obtain ⟨rfl, T₀, hT₀, h4⟩ := hc
    exact hRu G L hM T₀ hT₀ h4
  · exact h G L m hM hc

theorem sz_case_of_foundation_min
    (hF : Foundation) (hHKS : HKSRegularNormalAffine) (hRu : DempwolffRuMin)
    (hNS : GMS5NotSylow) (hSw : GMS5Swap) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
      standardComponentOddCore G = ⊥ → ∀ m : ℕ, 1 ≤ m →
        SuzukiModel (rankTwoQuot A) 2 (2 * m + 1) →
          m = 1 ∧ NativeSporadic.IsSporadic (rankTwoX A) .Ru := by
  refine sz_case_of_szRes (szRes_of_dempwolffRuMin hRu fun G _ _ L m hM hc => ?_)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (normalizer (L : Set G))
  have h3 : Sec3 G L T := ⟨hM.hyp, hT⟩
  have hZ : Odd (Nat.card (center L)) := hM.hyp.odd_card_center hF
  obtain ⟨e⟩ := hM.nonempty_mulEquiv_sz
  have hX := h3.facts_of_sz hF hZ hM.one_le e
  have h313 := h3.lemma313_of_sz_of_odd hF hZ hM.one_le e
  obtain ⟨y₀, hy₀⟩ := hX.exists_isTorus h3
  obtain ⟨R, y, d, hS⟩ :=
    h3.exists_szR hF hZ hM.one_le e (hy₀.exists_translation_of_affine h313 hX h3 hF hHKS)
  have h34 : NoStronglyClosedAbelian G := fun S _ hAS hAab hA1 hcl =>
    hM.hyp.lemma34 S hAS hAab hA1 hcl
  obtain ⟨R₂, hR₂⟩ := hS.exists_isR₂ h34
  have hne : ¬ (m = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) :=
    fun h => hc ⟨h.1, _, h3.isSylowOf_T₀, h.2⟩
  exact hM.false_of_gms5 hNS hSw hS h34 hR₂ hne

end CFSG.ComponentClassification.GMS78
