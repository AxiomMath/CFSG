module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin

@[expose] def Lemma2_4_35_used : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    A3A3K T M H S L s x z₁ z₂ K →
      ∃ e : ↥K ≃* alternatingGroup (Fin 6), ∃ u ∈ blockU2 L s, u ∉ Subgroup.zpowers z₂ ∧
        ∃ τ : Equiv.Perm (Fin 6), τ.IsSwap ∧ InducesPerm e u τ

@[expose] def Lemma2_4_36_cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    A3A3K T M H S L s x z₁ z₂ K →
      centralizerElem z₂ ⊓ Subgroup.centralizer (K : Set G) ≤ baum S

@[expose] def Lemma2_4_37_used : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    A3A3K T M H S L s x z₁ z₂ K →
      ∀ y ∈ conjClass z₂, y ∈ baum S → y ∈ baum S ⊓ K ∨ y ∈ conjR (baum S ⊓ K) s

@[expose] def Lemma2_4_34_used : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    A3A3K T M H S L s x z₁ z₂ K → ¬ blockU2 L s ≤ Subgroup.centralizer (K : Set G)

@[expose] def Lemma2_4_36_surj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    A3A3K T M H S L s x z₁ z₂ K → ∀ α : MulAut ↥K, ∃ g ∈ centralizerElem z₂, ∀ k : ↥K,
      ((α k : ↥K) : G) = g⁻¹ * (k : G) * g

theorem Lemma2_4_36.cent (h : Lemma2_4_36) : Lemma2_4_36_cent := by
  intro G _ _ T M H S L s x z₁ z₂ K hK
  obtain ⟨-, ⟨hBeq, -, -, -⟩, -⟩ := h G T M H S L s x z₁ z₂ K hK
  exact hBeq.le.trans inf_le_left

end CFSG.QuasithinUnique.DoubleA3
