module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.AbstractGroup
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Quasithin
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def vModule {G : Type} [Group G] (S L₁ L₂ : Subgroup G) : Subgroup G :=
  sInf {K : Subgroup G | Quasithin.omegaOneCenterOf S ≤ K ∧ S ≤ Subgroup.normalizer (K : Set G) ∧
    L₁ ≤ Subgroup.normalizer (K : Set G) ∧ L₂ ≤ Subgroup.normalizer (K : Set G)}

theorem omegaOneCenterOf_le_vModule {G : Type} [Group G] (S L₁ L₂ : Subgroup G) :
    Quasithin.omegaOneCenterOf S ≤ vModule S L₁ L₂ :=
  le_sInf fun _ hK => hK.1

theorem vModule_le {G : Type} [Group G] {S L₁ L₂ K : Subgroup G}
    (h : Quasithin.omegaOneCenterOf S ≤ K) (hS : S ≤ Subgroup.normalizer (K : Set G))
    (h₁ : L₁ ≤ Subgroup.normalizer (K : Set G)) (h₂ : L₂ ≤ Subgroup.normalizer (K : Set G)) :
    vModule S L₁ L₂ ≤ K :=
  sInf_le ⟨h, hS, h₁, h₂⟩

private theorem mem_normalizer_vModule {G : Type} [Group G] {S L₁ L₂ T : Subgroup G}
    (hT : ∀ K : Subgroup G, Quasithin.omegaOneCenterOf S ≤ K →
      S ≤ Subgroup.normalizer (K : Set G) → L₁ ≤ Subgroup.normalizer (K : Set G) →
      L₂ ≤ Subgroup.normalizer (K : Set G) → T ≤ Subgroup.normalizer (K : Set G)) :
    T ≤ Subgroup.normalizer (vModule S L₁ L₂ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [vModule, Subgroup.mem_sInf] at hx ⊢
    intro K hK
    exact (Subgroup.mem_normalizer_iff.mp (hT K hK.1 hK.2.1 hK.2.2.1 hK.2.2.2 hg) x).mp (hx K hK)
  · intro hx
    rw [vModule, Subgroup.mem_sInf] at hx ⊢
    intro K hK
    exact (Subgroup.mem_normalizer_iff.mp (hT K hK.1 hK.2.1 hK.2.2.1 hK.2.2.2 hg) x).mpr (hx K hK)

theorem normalizer_vModule_S {G : Type} [Group G] (S L₁ L₂ : Subgroup G) :
    S ≤ Subgroup.normalizer (vModule S L₁ L₂ : Set G) :=
  mem_normalizer_vModule fun _ _ h _ _ => h

theorem normalizer_vModule_L₁ {G : Type} [Group G] (S L₁ L₂ : Subgroup G) :
    L₁ ≤ Subgroup.normalizer (vModule S L₁ L₂ : Set G) :=
  mem_normalizer_vModule fun _ _ _ h _ => h

theorem normalizer_vModule_L₂ {G : Type} [Group G] (S L₁ L₂ : Subgroup G) :
    L₂ ≤ Subgroup.normalizer (vModule S L₁ L₂ : Set G) :=
  mem_normalizer_vModule fun _ _ _ _ h => h

end CFSG.AGLEmbeddingD2.McLaughlin
