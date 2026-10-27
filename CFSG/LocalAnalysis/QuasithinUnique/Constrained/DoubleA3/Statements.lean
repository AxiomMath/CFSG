module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Defs

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

@[expose] def Lemma2_4_30 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s : G), A3A3 T M H S L s →
    (∀ x ∈ T, x ∉ S → pCoreOf 2 H ⊔ conjR (pCoreOf 2 H) x = baum S ∧ baum S = thompsonJ S) ∧
    IsGamma2 M H ∧
    (∀ x ∈ T, x ∉ S → ∀ B : Subgroup G, IsMaxElemAbelian (baum S) B →
      ((∀ g ∈ S, conjR B g = B) ↔ (B = pCoreOf 2 H ∨ B = conjR (pCoreOf 2 H) x))) ∧
    (∀ x ∈ T, x ∉ S →
      baum S ⊔ conjJoin S L = blockD S L ⊔ (conjJoin S L ⊔ conjR (blockU0 S L) x) ∧
      blockD S L ⊓ (conjJoin S L ⊔ conjR (blockU0 S L) x) = ⊥ ∧
      (∀ d ∈ blockD S L, ∀ y ∈ conjJoin S L ⊔ conjR (blockU0 S L) x, d * y = y * d) ∧
      IsElemAbelian 2 (blockD S L) ∧
      Nonempty (↥(conjJoin S L ⊔ conjR (blockU0 S L) x) ≃*
        (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)))) ∧
    ((baum S).relIndex S = 2 ∧ S = baum S ⊔ Subgroup.zpowers s ∧
      Nat.card T = 4 * Nat.card (baum S))

@[expose] def Lemma2_4_32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G),
    A3A3x T M H S L s x z₁ z₂ →
    IsGamma2 M (centralizerElem z₂) ∧ ∃ K : Subgroup G, A3A3K T M H S L s x z₁ z₂ K

@[expose] def Lemma2_4_34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    A3A3K T M H S L s x z₁ z₂ K → ⁅K, blockU2 L s⁆ = K

@[expose] def Lemma2_4_35 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    A3A3K T M H S L s x z₁ z₂ K →
      ∃ e : ↥K ≃* alternatingGroup (Fin 6),
        (∃ u ∈ blockU2 L s, u ∉ Subgroup.zpowers z₂ ∧ (∀ l ∈ L, u * l = l * u) ∧
          ∃ τ : Equiv.Perm (Fin 6), τ.IsSwap ∧ InducesPerm e u τ) ∧
        ¬ ∃ σ : Equiv.Perm (Fin 6), InducesPerm e x σ

@[expose] def Lemma2_4_36 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    A3A3K T M H S L s x z₁ z₂ K →
      ((IsSylowTwoOf (baum S ⊓ K) K ∧ Nonempty (↥(baum S ⊓ K) ≃* DihedralGroup 4)) ∧
        baum S = (baum S ⊓ K) ⊔ conjR (baum S ⊓ K) s ∧
        (baum S ⊓ K) ⊓ conjR (baum S ⊓ K) s = ⊥ ∧
        ∀ a ∈ baum S ⊓ K, ∀ b ∈ conjR (baum S ⊓ K) s, a * b = b * a) ∧
      (centralizerElem z₂ ⊓ Subgroup.centralizer (K : Set G) =
          baum S ⊓ Subgroup.centralizer (K : Set G) ∧
        IsCyclic ↥(baum S ⊓ Subgroup.centralizer (K : Set G)) ∧
        Nat.card ↥(baum S ⊓ Subgroup.centralizer (K : Set G)) = 4 ∧
        ∀ α : MulAut ↥K, ∃ g ∈ centralizerElem z₂, ∀ k : K,
          ((α k : K) : G) = g⁻¹ * (k : G) * g) ∧
      (T ⊓ Subgroup.centralizer (conjJoin S L : Set G) = ⊥ ∧ Nat.card T = 2 ^ 8)

@[expose] def Lemma2_4_37 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    A3A3K T M H S L s x z₁ z₂ K →
      {y | y ∈ conjClass z₂ ∧ y ∈ baum S} =
          {y | y ∈ conjClass z₂ ∧ y ∈ baum S ⊓ K} ∪
            {y | y ∈ conjClass z₂ ∧ y ∈ conjR (baum S ⊓ K) s} ∧
        {y | y ∈ conjClass z₂ ∧ y ∈ baum S ⊓ K}.ncard = 5

end CFSG.QuasithinUnique.DoubleA3
