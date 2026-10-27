module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair

section NatSum

variable {X : Type} [Group X] [Finite X]

@[expose] def IsNatSum (L U : Subgroup X) : Prop :=
  ∃ N₁ N₂ : Subgroup X, IsNaturalLThreeTwo L N₁ ∧ N₁ ⊔ N₂ = U ∧
    (N₂ = ⊥ ∨ (IsNaturalLThreeTwo L N₂ ∧ N₁ ⊓ N₂ = ⊥ ∧
      ∃ f : ↥N₁ ≃* ↥N₂, ∀ l ∈ L, ∀ a b : ↥N₁,
        (b : X) = l * (a : X) * l⁻¹ → (f b : X) = l * (f a : X) * l⁻¹))

@[expose] noncomputable def actOn (L U : Subgroup X) (h : L ≤ Subgroup.normalizer (U : Set X)) :
    ↥L →* MulAut ↥U :=
  (Subgroup.normalizerMonoidHom U).comp (Subgroup.inclusion h)

end NatSum

@[expose] def wSub (G : Type) [Group G] (M T : Subgroup G) (U : Subgroup ↥M) : Subgroup G :=
  ⨆ A ∈ {A : Subgroup G | (∃ g : G, A = (U.map M.subtype).map (MulAut.conj g).toMonoidHom) ∧ A ≤ T}, A

section UOf

variable {G : Type} [Group G] [Finite G]

@[expose] def uOf (M T : Subgroup G) (L : Subgroup ↥M) : Subgroup G :=
  (⁅L, gnV (T.subgroupOf M)⁆ : Subgroup ↥M).map M.subtype

end UOf

end CFSG.LocalAnalysis.RankThreeUC.S15
