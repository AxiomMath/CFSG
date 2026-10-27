module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableW
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32S

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519

@[expose] def Lemma2_4_32_KW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G),
    A3A3x T M H S L s x z₁ z₂ →
    IsGamma2 M (centralizerElem z₂) → IsSylowTwoOf (sOne S x) (centralizerElem z₂) →
    oddCoreIn (centralizerElem z₂) = ⊥ →
    ∀ K : Subgroup G, IsComponentIn K (centralizerElem z₂) →
      z₁ * z₂ ∈ Subgroup.normalizer (K : Set G) → ⁅K, Subgroup.zpowers (z₁ * z₂)⁆ = K →
      ¬ K ≤ M →
      ((¬ CentralQuotientAlt K 6 ∧ ¬ CentralQuotientAlt K 7) → Ch1.InducesInner (z₁ * z₂) K) →
      IsListedComponentW M (sOne S x) K (z₁ * z₂) →
      A3A3K T M H S L s x z₁ z₂ K

theorem lemma2_4_32_KW_of_lek (hP : Prop121Three) (h1 : K32TableW) (hL : K32LeK) (h2 : K32ExclA7)
    (h3 : K32ExclA8) (h4 : K32ExclBig) : Lemma2_4_32_KW := by
  intro G _ _ T M H S L s x z₁ z₂ hA hΓ hS hodd K hKc hzN hcomm hKM hinn hlist
  have ctx : K32Ctx T M H S L s x z₁ z₂ K := ⟨hA, hΓ, hS, hodd, hKc, hzN, hcomm, hKM, hinn⟩
  have h8 : KInEight K := h1 G T M H S L s x z₁ z₂ K ctx hlist
  exact k32_A3A3K_of ctx (k32Struct_of hP hL G T M H S L s x z₁ z₂ K ctx h8) h8 h2 h3 h4

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s x z₁ z₂ : G}

theorem lemma2_4_32W (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hSA : ConstrainedSetupAt) (hlin : Lin2BlockExcluded) (ha5 : A5BlockExcluded)
    (ha3 : SingleA3Excluded) (h2397 : Lemma2_3_9_7W) (hK : Lemma2_4_32_KW) : Lemma2_4_32 := by
  intro G _ _ T M H S L s x z₁ z₂ hA
  have hcs := hA.cs
  have hB := basic31 hD h27_1 hA.toA3A3
  obtain ⟨hΓ2, hS₁, hS₁M⟩ := remark31_G₂ hD h27_1 hA
  refine ⟨hΓ2, ?_⟩
  obtain ⟨K, hKc⟩ := exists_component_centralizer₂ hD h27_1 hSA hlin ha5 ha3 hA
  have hodd := oddCoreIn_centralizer₂_eq_bot hD h27_1 hA
  have hz := z_central hB hA
  have hT := hcs.setting.isSylowTwoOf_M
  obtain ⟨hzN, hcomm, hKM, -⟩ := IsGamma0.component_normalized_commutator_not_le hcs.setting
    (Or.inr hΓ2) hS₁M hT hA.sOne_le_T hz hA.z_ne hA.sq_z hKc
  obtain ⟨hinn, hlist⟩ := h2397 G T M hcs.setting (centralizerElem z₂) (sOne S x) T (z₁ * z₂)
    (Or.inr hΓ2) hS₁M hT hA.sOne_le_T hz hA.z_ne hA.sq_z K hKc
  exact ⟨K, hK G T M H S L s x z₁ z₂ hA hΓ2 hS₁ hodd K hKc hzN hcomm hKM hinn hlist⟩

end CFSG.QuasithinUnique.DoubleA3
