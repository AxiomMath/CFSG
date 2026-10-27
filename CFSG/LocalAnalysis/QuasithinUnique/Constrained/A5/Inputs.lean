module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def LemmaC54_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 5 → conjJoin S L = L →
    ∀ α : ↥L →* alternatingGroup (Fin 5), Function.Surjective α → α.ker = CFSG.pCore 2 L →
      ∃ (θ : ↥(L ⊔ baum S) →* Equiv.Perm (Fin 5)) (τ₁ τ₂ : Equiv.Perm (Fin 5)),
        Function.Surjective θ ∧
        θ.ker = (pCoreOf 2 (L ⊔ baum S)).subgroupOf (L ⊔ baum S) ∧
        (∀ (l : G) (hl : l ∈ L), θ ⟨l, Subgroup.mem_sup_left hl⟩ =
          ((α ⟨l, hl⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))) ∧
        τ₁.IsSwap ∧ τ₂.IsSwap ∧ τ₁.Disjoint τ₂ ∧
        ((baum S).subgroupOf (L ⊔ baum S)).map θ =
          Subgroup.closure ({τ₁, τ₂} : Set (Equiv.Perm (Fin 5)))

end CFSG.QuasithinUnique.A5
