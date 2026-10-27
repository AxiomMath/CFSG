module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFive

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

abbrev modTwoCore (K : Subgroup G) : Type :=
  ↥K ⧸ pCore 2 ↥K

@[expose] def IsThreeOnePlusTwo (X : Type) [Group X] : Prop :=
  CFSG.IsExtraspecialPGroup 3 X ∧ Nat.card X = 27 ∧ ∀ x : X, x ^ 3 = 1

structure TwelveFiveData (M H : Subgroup G) (d : ℕ)
    (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ) : Prop where
  mem_sigma : d ∈ sigmaSet G M
  j_eq : jSub M H = oPPrimeHull d M
  mem₁ : L₁ ∈ weakBlockSet M H
  mem₂ : L₂ ∈ weakBlockSet M H
  mem₃ : L₃ ∈ weakBlockSet M H
  join_eq : jSub M H = L₁ ⊔ L₂ ⊔ L₃
  type₁ : IsL3TwoPow n₁ (↥L₁ ⧸ pCore 2 ↥L₁)
  type₂ : IsL3TwoPow n₂ (↥L₂ ⧸ pCore 2 ↥L₂)
  type₃ : IsL3TwoPow n₃ (↥L₃ ⧸ pCore 2 ↥L₃)
  odd₁ : Odd n₁
  odd₂ : Odd n₂
  odd₃ : Odd n₃

@[expose] def TwelveSix (M H : Subgroup G) (p d : ℕ)
    (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ) : Prop :=
  TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃ →
    (∀ W : Subgroup G, Nat.card W = 3 → W ≤ L₁ → centralizer (W : Set G) ≤ M) ∧
    (∀ W : Subgroup G, Nat.card W = 3 → W ≤ L₂ → centralizer (W : Set G) ≤ M) ∧
    (∀ W : Subgroup G, Nat.card W = 3 → W ≤ L₃ → centralizer (W : Set G) ≤ M) ∧
    n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1 ∧
    sigmaSet G M = {7} ∧
    p = 3 ∧
    (CFSG.Blueprint.LieModel (modTwoCore (kSub p M H)) .PSp 2 3 1 ∨
      Nonempty (modTwoCore (kSub p M H) ≃* alternatingGroup (Fin 9))) ∧
    (∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P (kSub p M H ⊓ M) →
      kSub p M H ⊓ M =
        (kSub p M H ⊓ normalizer (thompsonSubgroup P : Set G)) ⊔ pCoreOf 2 (kSub p M H))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
