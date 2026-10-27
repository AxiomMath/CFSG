module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Defs
public import CFSG.RankThree.PartOne.CTP.StrongPLinear

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis (SylowDichotomyAt)

@[expose] def CentralFusionAt (K : Type) [Group K] [Finite K] : Prop :=
  ¬ 3 ∣ Nat.card (Outer K) ∧
    ∀ T : Sylow 3 K, ∀ A : Subgroup K, A ≤ (T : Subgroup K) →
      (∀ a ∈ A, ∀ t ∈ (T : Subgroup K), a * t = t * a) → Nat.card A = 3 →
        ∃ g ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
          A.map (MulAut.conj g).toMonoidHom ≠ A

@[expose] def OmegaDichAt (K : Type) [Group K] [Finite K] : Prop :=
  (∀ S : Sylow 3 K, IsMulCommutative (S : Subgroup K)) ∨ HasNoncommPair 3 K ∨
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) ∨ CentralFusionAt K

@[expose] def HeisDichAt (K : Type) [Group K] [Finite K] : Prop :=
  SylowDichotomyAt K 3 ∨ CentralFusionAt K

@[expose] def DichThreeAt (K : Type) [Group K] [Finite K] : Prop :=
  OmegaDichAt K ∧ HeisDichAt K

@[expose] def DichThree : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → 3 ∣ Nat.card K → DichThreeAt K

@[expose] def HeisDichThree : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → 3 ∣ Nat.card K → HeisDichAt K

@[expose] def OuterThreeInner : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ S : Sylow 3 K, ¬ IsMulCommutative (S : Subgroup K) →
      (Nat.card K).factorization 3 ≤ 3 →
      ∀ α : MulAut K, α ^ 3 = 1 → (∀ s ∈ (S : Subgroup K), α s = s) → α ∈ inner K

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
