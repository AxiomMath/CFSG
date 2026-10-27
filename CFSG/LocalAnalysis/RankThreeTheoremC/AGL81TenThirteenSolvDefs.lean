module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeList

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def IsSolvThreeTarget (K : Type) [Group K] : Prop :=
  IsAltTwoP 3 K ∨ IsLieOver K (.twistedA 3) 2 1 ∨ IsLieOver K (.B 3) 2 1 ∨
    Nonempty (K ≃* alternatingGroup (Fin 9))

@[expose] def SolvThreeAutCond {Y I₀ : Type} [Group Y] [Group I₀] (Y₀ : Subgroup Y)
    (σ : I₀ →* Y) : Prop :=
  Nonempty (I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3)) ∨
    ∃ y ∈ Y₀, (∃ k : ℕ, y ^ 3 ^ k = 1) ∧ ∃ α : I₀ →* I₀, (∀ g, σ (α g) = y * σ g * y⁻¹) ∧
      ∃ g : I₀, α g * g⁻¹ ∉
        CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀) ⊔ CFSG.pCore 2 I₀

@[expose] def SolvThreeDirectCond {Y : Type} [Group Y] (Y₀ J : Subgroup Y) : Prop :=
  Nat.card (↥(⨆ y ∈ Y₀, J.map (MulAut.conj y).toMonoidHom) ⧸
      CFSG.pCore 2 ↥(⨆ y ∈ Y₀, J.map (MulAut.conj y).toMonoidHom)) =
    Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) ^ ((normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀).index

@[expose] def KFactThreeFourSolvThree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow 3 Y)
    (I₀ : Type) [Group I₀] [Finite I₀] (σ : I₀ →* Y),
    K.Normal → NineThreeListGroup 3 K → Subgroup.center K = ⊥ →
    pRank 3 (⊤ : Subgroup Y) ≤ 3 →
    pRank 3 (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
    (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
    E ≤ R → IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
    (if 3 ≤ pRank 3 (R : Subgroup Y) then GLBWeakCore 3 (R : Subgroup Y)
      else GLBCore 3 1 E) ≤ Y₀ →
    pCoreOf 2 Y₀ ≤ centralizer (K : Set Y) →
    Nat.Coprime 3 (Nat.card σ.ker) → σ.range ≤ Y₀ → IsSubnormal σ.range Y₀ →
    IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀) → SolvThreeAutCond Y₀ σ →
    SolvThreeDirectCond Y₀
      ((CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ) →
    ¬ (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤
      centralizer (K : Set Y) →
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤ K ∧
      IsSolvThreeTarget K

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81TenThreeSolvStructCfg : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    AGL81CfgData 3 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ I₀ ∈ cZero (H ⊓ L), IsSymThreeOrSUThreeTwo (↥I₀ ⧸ CFSG.pCore 2 ↥I₀) →
    SolvThreeDirectCond (d1X0 3 M H)
        (((CFSG.ComponentClassification.AS76b.oUpperTwo I₀).subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := H) 3))) ∧
      (¬ Nonempty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* Equiv.Perm (Fin 3)) →
        ∃ y ∈ H ⊓ M, (∃ k : ℕ, y ^ 3 ^ k = 1) ∧ y ∈ normalizer (I₀ : Set G) ∧
          ∃ g ∈ I₀, y * g * y⁻¹ * g⁻¹ ∉
            CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ⊔ pCoreOf 2 I₀)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
