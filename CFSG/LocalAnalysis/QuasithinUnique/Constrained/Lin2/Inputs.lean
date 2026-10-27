module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

@[expose] def SingerNormalizerCyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Z D P : Subgroup G),
    IsElemAbelian 2 Z → Z ≠ ⊥ → D ≤ Subgroup.normalizer (Z : Set G) → IsCyclic ↥D →
    ActsRegularlyOn D (nonIdentity Z) → IsPGroup 2 P → P ≤ Subgroup.normalizer (Z : Set G) →
    P ≤ Subgroup.normalizer ((D ⊔ Subgroup.centralizer (Z : Set G) : Subgroup G) : Set G) →
    ∃ t ∈ P, P = (P ⊓ Subgroup.centralizer (Z : Set G)) ⊔ Subgroup.zpowers t

@[expose] def TIAbelianTwoGroupCommute : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V A : Subgroup G),
    IsElemAbelian 2 V → IsElemAbelian 2 A → Nat.card V = Nat.card A → fusionIsTI V →
    fusionIsTI A → (∀ g : G, conjR A g ≠ V → conjR A g ⊓ V = ⊥) → IsPGroup 2 ↥(V ⊔ A) →
    V ⊓ Subgroup.normalizer (A : Set G) ≠ ⊥ → ⁅V, A⁆ = ⊥

end CFSG.QuasithinUnique.Lin2
