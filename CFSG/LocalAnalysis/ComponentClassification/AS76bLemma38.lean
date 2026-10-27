module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma37
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma38Core

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34 Lemma22 Lemma37 Lemma22Full
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem lemma38_of_le
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {A W L R T : Subgroup G} (hA : Hyp31 A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hWA : W ≤ A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : L ≤ A ⊓ centralizer (W : Set G))
    (hNL : normalizer (A : Set G) ⊓ centralizer (W : Set G) ≤ normalizer (L : Set G))
    (hRL : IsSylowOf 2 R
      (centralizer (W : Set G) ⊓ centralizer (L : Set G) ⊓ normalizer (R : Set G)))
    (hTRL : T ≤ R ⊔ L) (hTL : T ⊓ L = ⊥) (hTR : Nat.card T = Nat.card R)
    (hRT : ¬ centralizer (W : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G))
    (hL2 : ∀ n : ℕ, 2 ^ n = Nat.card R → Nonempty (↥L ≃* SL(2, GaloisField 2 n)) →
      ∀ g : G, ¬ conj R g ≤ L) :
    standardComponentIsStandard (L.subgroupOf (centralizer (W : Set G))) ∧
      ¬ (L.subgroupOf (centralizer (W : Set G))).Normal := by
  have hRCL : R ≤ centralizer (L : Set G) :=
    hR.le.trans (centralizer_le fun x hx => (hLA hx).1)
  refine ⟨?_, not_normal_of_card_eq (hLA.trans inf_le_right) hRCL hRL hTRL hTL hTR hRT⟩
  rcases lemma37_bender_of_le h4 h32 h34 hA hR hWA hL hLA hNL hRL with
    h | ⟨c, -, -, -, hRc, n, -, hn, he⟩
  · exact h
  · exfalso
    apply hL2 n hn he c⁻¹
    calc conj R c⁻¹ ≤ conj (conj L c) c⁻¹ := map_mono hRc
      _ = L := by rw [conj_conj, inv_mul_cancel, conj_one]

theorem lemma38
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {A W R T : Subgroup G} (hA : Hyp31 A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hWA : W ≤ A) (hL : CFSG.Open.IsQuasisimple ↥(layerCentralizer A W))
    (hRL : IsSylowOf 2 R (centralizer (W : Set G) ⊓
      centralizer (layerCentralizer A W : Set G) ⊓ normalizer (R : Set G)))
    (hTRL : T ≤ R ⊔ layerCentralizer A W) (hTL : T ⊓ layerCentralizer A W = ⊥)
    (hTR : Nat.card T = Nat.card R)
    (hRT : ¬ centralizer (W : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G))
    (hL2 : ∀ n : ℕ, 2 ^ n = Nat.card R →
      Nonempty (↥(layerCentralizer A W) ≃* SL(2, GaloisField 2 n)) →
      ∀ g : G, ¬ conj R g ≤ layerCentralizer A W) :
    standardComponentIsStandard ((layerCentralizer A W).subgroupOf (centralizer (W : Set G))) ∧
      ¬ ((layerCentralizer A W).subgroupOf (centralizer (W : Set G))).Normal :=
  lemma38_of_le h4 h32 h34 hA hR hWA hL (layerCentralizer_le A W)
    (normalizer_inf_le_normalizer_layerCentralizer A W) hRL hTRL hTL hTR hRT hL2

end CFSG.ComponentClassification.AS76b
