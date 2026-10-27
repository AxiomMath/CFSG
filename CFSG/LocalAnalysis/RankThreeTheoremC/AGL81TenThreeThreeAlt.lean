module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup

@[expose] def Asc81bAltBlockAut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L →
    (NineThreeSix M S L ∨ NineThreeSeven M S L ∨ NineThreeEight M S L) →
    ∀ X : Subgroup G, normalizer (S : Set G) ⊓ L = X →
    ∀ b (hb : b ∈ M), b ∈ normalizer (S : Set G) → Odd (orderOf b) →
      b ∈ normalizer (L : Set G) →
      (∀ w (hw : w ∈ barM M X),
        QuotientGroup.mk' (CFSG.pCore 2 ↥(barM M X)) ⟨w, hw⟩ ∈
          wSup (↥(barM M X) ⧸ CFSG.pCore 2 ↥(barM M X)) →
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ * w *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩)⁻¹ * w⁻¹ ∈ pCoreOf 2 (barM M X)) →
      ∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ * y =
        y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩

@[expose] def Asc81bAltBlockAutNX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L →
    (NineThreeSix M S L ∨ NineThreeSeven M S L ∨ NineThreeEight M S L) →
    ∀ X : Subgroup G, normalizer (S : Set G) ⊓ L = X →
    ∀ b (hb : b ∈ M), b ∈ normalizer (S : Set G) → Odd (orderOf b) →
      b ∈ normalizer (L : Set G) →
      (∀ w (hw : w ∈ barM M X),
        QuotientGroup.mk' (CFSG.pCore 2 ↥(barM M X)) ⟨w, hw⟩ ∈
          wSup (↥(barM M X) ⧸ CFSG.pCore 2 ↥(barM M X)) →
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ * w *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩)⁻¹ * w⁻¹ ∈ pCoreOf 2 (barM M X)) →
      ∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ * y =
        y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩

variable {G : Type} [Group G] [Finite G]

theorem tenThreeThreeAt_alt_nx (hAlt : Asc81bAltBlockAutNX)
    {Φ : Subgroup G → Subgroup G → Subgroup G → Prop}
    (hΦ : ∀ M S L, Φ M S L →
      (NineThreeSix M S L ∨ NineThreeSeven M S L ∨ NineThreeEight M S L) ∧ ¬ InClassXBlock L) :
    TenThreeThreeAt G Φ := by
  intro M H L hK hA hNH _ hL hLn hΦL b hb hbo hbJ
  right
  have hLM : L ≤ M := hL.le
  obtain ⟨-, hbL, -, hW⟩ := bar_action hLM hLn hb hbo hbJ
  have hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L := by rw [hNH]
  have hbS : b ∈ normalizer (pCoreOf 2 H : Set G) := by rw [hNH]; exact hb.1
  have hbLn : b ∈ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLM).mp hLn hb.2
  refine commutator_mem_pCoreOf_of_centralizes hLM hb.2 ?_
  exact hAlt G M (pCoreOf 2 H) L hK hA hL (hΦ _ _ _ hΦL).2 (hΦ _ _ _ hΦL).1 (H ⊓ L) hNS b hb.2 hbS
    hbo hbLn hW

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
