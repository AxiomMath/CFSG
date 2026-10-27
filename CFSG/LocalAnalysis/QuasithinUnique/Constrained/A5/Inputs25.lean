module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Defs

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

@[expose] def LemmaC54_3_s2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 5 → conjJoin S L ≠ L →
    baum S ≤ Subgroup.normalizer (L : Set G) ∧
    blockU L ≤ s2Q1 S L ∧
    s2Q1 S L = baum S ⊓ Subgroup.centralizer (blockU L : Set G) ∧
    IsInternalDirect (blockU L) (s2I S L) (s2Q1 S L) ∧
    ∀ α : ↥L →* alternatingGroup (Fin 5), Function.Surjective α → α.ker = CFSG.pCore 2 L →
      ∃ (θ : ↥(L ⊔ baum S) →* Equiv.Perm (Fin 5)) (τ₁ τ₂ : Equiv.Perm (Fin 5)),
        Function.Surjective θ ∧
        θ.ker = (pCoreOf 2 (L ⊔ baum S)).subgroupOf (L ⊔ baum S) ∧
        (∀ (l : G) (hl : l ∈ L), θ ⟨l, Subgroup.mem_sup_left hl⟩ =
          ((α ⟨l, hl⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))) ∧
        τ₁.IsSwap ∧ τ₂.IsSwap ∧ τ₁.Disjoint τ₂ ∧
        ((baum S).subgroupOf (L ⊔ baum S)).map θ =
          Subgroup.closure ({τ₁, τ₂} : Set (Equiv.Perm (Fin 5))) ∧
        ((thompsonJ S).subgroupOf (L ⊔ baum S)).map θ =
          Subgroup.closure ({τ₁, τ₂} : Set (Equiv.Perm (Fin 5)))

@[expose] def LemmaC56_14_s2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 5 → conjJoin S L ≠ L →
    ∀ x : G, x ∈ T → x ∈ Subgroup.normalizer (S : Set G) →
      ⁅blockU L, conjR (blockU L) x⁆ ≠ ⊥ →
      (s2Q1 S L = blockU L ⊔ s2I S L ∧
        s2I S L ≤ Subgroup.centralizer (conjR (blockU L) x : Set G)) ∧
      (baum S = conjR (blockU L) x ⊔ s2Q1 S L ∧ baum S = s2Q1 S L ⊔ conjR (s2Q1 S L) x ∧
        ⁅blockU L, baum S⁆ = ⁅blockU L, conjR (blockU L) x⁆ ∧
        ⁅blockU L, conjR (blockU L) x⁆ =
          blockU L ⊓ Subgroup.centralizer (conjR (blockU L) x : Set G) ∧
        blockU L ⊓ Subgroup.centralizer (conjR (blockU L) x : Set G) =
          blockU L ⊓ conjR (blockU L) x) ∧
      conjR ⁅blockU L, baum S⁆ x = ⁅blockU L, baum S⁆ ∧
      conjR (frattiniOf (s2I S L)) x = frattiniOf (s2I S L)

@[expose] def CompChi0Block : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H₁ K : Subgroup G), UniqueSetting G T M →
    IsGamma0 M H₁ → CharTwo H₁ → quasithinIsCComponent K H₁ → ¬ K ≤ M → IsChi0Block H₁ K

@[expose] def NoProperA5Block : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S₁ S₀ K L : Subgroup G),
    CharTwo X → IsSylowTwoOf S₁ X → S₀ ≤ S₁ → S₀.relIndex S₁ = 2 →
    quasithinIsCComponent K X → IsChi0Block X K → IsShort2 L → IsAltType L 5 → L ≤ K →
    S₀ ≤ Subgroup.normalizer (L : Set G) → quasithinIsLocal S₀ L → L = K

@[expose] def Kc3Inspection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L S₀ T₀ : Subgroup G),
    CFSG.IsQuasisimple ↥K → Kc3Group (↥K ⧸ Subgroup.center ↥K) → IsPGroup 2 ↥(Subgroup.center ↥K) →
    L ≤ K → IsShort2 L → IsAltType L 5 → S₀ ≤ Subgroup.normalizer (L : Set G) → IsPGroup 2 S₀ →
    IsPGroup 2 T₀ → S₀ ≤ T₀ → T₀ ≤ Subgroup.normalizer (K : Set G) → IsSylowTwoOf T₀ (K ⊔ T₀) →
    ∃ X S₁ : Subgroup G, CharTwo X ∧ L ⊔ S₀ ≤ X ∧ X ≤ K ⊔ T₀ ∧ IsSylowTwoOf S₁ X ∧ S₀ ≤ S₁ ∧
      ¬ quasithinIsLocal S₁ L

end CFSG.QuasithinUnique.A5
