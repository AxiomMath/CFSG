module

public import CFSG.Open.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G]

@[expose] def IsOTwoPerfect (J : Subgroup G) : Prop :=
  ∀ (N : Subgroup ↥J) [N.Normal], IsPGroup 2 (↥J ⧸ N) → N = ⊤

@[expose] def IsChiBlock (X J : Subgroup G) : Prop :=
  CFSG.Open.IsSubnormal J X ∧ IsOTwoPerfect J ∧
    ((∃ n : ℕ, 3 ≤ n ∧ Odd n ∧
        Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin n))) ∨
      ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* PSL(2, GaloisField 2 n)))

@[expose] def chiBlockProduct (X : Subgroup G) : Subgroup G :=
  ⨆ J ∈ {J : Subgroup G | IsChiBlock X J}, J

@[expose] def aschbacherC (X T : Subgroup G) : Subgroup G :=
  ⨆ T₀ ∈ {T₀ : Subgroup G | T₀ ≤ T ∧ T₀ ≠ ⊥ ∧ (T₀.subgroupOf T).Characteristic},
    normalizer (T₀ : Set G) ⊓ X

@[expose] def KFact282 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T : Subgroup G), CFSG.Open.IsKGroup ↥X →
    X ⊓ centralizer (CFSG.Open.pCoreOf 2 X : Set G) ≤ CFSG.Open.pCoreOf 2 X →
    CFSG.ABGLocalTools.IsSylowOf 2 T X → T ≠ ⊥ → X ≤ chiBlockProduct X ⊔ aschbacherC X T

theorem le_of_kfact282 (h : KFact282) {G : Type} [Group G] [Finite G] {X T : Subgroup G}
    (hK : CFSG.Open.IsKGroup ↥X)
    (hF : X ⊓ centralizer (CFSG.Open.pCoreOf 2 X : Set G) ≤ CFSG.Open.pCoreOf 2 X)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X) (hT1 : T ≠ ⊥) {M : Subgroup G}
    (hC : ∀ T₀ : Subgroup G, T₀ ≤ T → T₀ ≠ ⊥ → (T₀.subgroupOf T).Characteristic →
      normalizer (T₀ : Set G) ⊓ X ≤ M)
    (hJ : ∀ J : Subgroup G, IsChiBlock X J → J ≤ M) : X ≤ M := by
  refine (h G X T hK hF hT hT1).trans (sup_le (iSup₂_le fun J hJ' => hJ J hJ') ?_)
  exact iSup₂_le fun T₀ hT₀ => hC T₀ hT₀.1 hT₀.2.1 hT₀.2.2

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
