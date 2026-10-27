module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeGraphRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeGraphOdd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeGraphEven
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeGraphSign

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def SpThreeKindCoverInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k κ) → SpGlobalCoverType e f κ

@[expose] def SpThreeLinearEvenRecognitionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .linearEven) →
        SpGlobalCoverType e f .linearEven ∨ Sp2mKindType (spGlobal e) 3 f .omegaPlus

@[expose] def SpThreeUnitaryEvenRecognitionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .unitaryEven) →
        SpGlobalCoverType e f .unitaryEven ∨ Sp2mKindType (spGlobal e) 3 f .omegaMinus

@[expose] def threeOmegaRootKind : Sp2mKind → Sp2mKind
  | .omegaPlus => .linearEven
  | _ => .unitaryEven

@[expose] def SpThreeOmegaRowUniqueInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k (threeOmegaRootKind κ)) → SpOmegaRowGlobal e t f κ →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) →
        g ∈ normalizer (spGlobal e : Set G)

section Rows

theorem spThreeGraphRowInput_linearOdd_of_cover (h : SpThreeKindCoverInput .linearOdd) :
    SpThreeGraphRowInput .linearOdd := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot
  exact false_of_coverType_linearOdd hset (by norm_num) hKc hf e ht hKt
    (h G L hset f K hKc hf e t ht hKt hroot)

theorem spThreeGraphRowInput_unitaryOdd_of_cover (h : SpThreeKindCoverInput .unitaryOdd) :
    SpThreeGraphRowInput .unitaryOdd := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot
  exact false_of_coverType_unitaryOdd hset (by norm_num) hKc hf e ht hKt
    (h G L hset f K hKc hf e t ht hKt hroot)

theorem spThreeGraphRowInput_linearEven_of_recognition (h : SpThreeLinearEvenRecognitionInput)
    (hu : SpThreeOmegaRowUniqueInput .omegaPlus) : SpThreeGraphRowInput .linearEven := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot
  rcases h G L hset f K hKc hf e t ht hKt hroot with hc | hty
  · exact false_of_coverType_linearEven hset (by norm_num) hKc hf e ht hKt hc
  · exact false_of_sp2mKindType_omegaPlus_three omegaPlusSignInput_four hset hKc hf e ht hKt hty
      (hu G L hset f K hKc hf e t ht hKt hroot)

theorem spThreeGraphRowInput_unitaryEven_of_recognition (h : SpThreeUnitaryEvenRecognitionInput)
    (hu : SpThreeOmegaRowUniqueInput .omegaMinus) : SpThreeGraphRowInput .unitaryEven := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot
  rcases h G L hset f K hKc hf e t ht hKt hroot with hc | hty
  · exact false_of_coverType_unitaryEven hset (by norm_num) hKc hf e ht hKt hc
  · exact false_of_sp2mKindType_omegaMinus_three hset hKc hf e ht hKt hty
      (hu G L hset f K hKc hf e t ht hKt hroot)

theorem spThreeGraphRowsInput_of_inputs (hLE : SpThreeLinearEvenRecognitionInput)
    (hUE : SpThreeUnitaryEvenRecognitionInput) (hLO : SpThreeKindCoverInput .linearOdd)
    (hUO : SpThreeKindCoverInput .unitaryOdd) (huP : SpThreeOmegaRowUniqueInput .omegaPlus)
    (huM : SpThreeOmegaRowUniqueInput .omegaMinus) : SpThreeGraphRowsInput :=
  spThreeGraphRowsInput_of_rows (spThreeGraphRowInput_linearEven_of_recognition hLE huP)
    (spThreeGraphRowInput_unitaryEven_of_recognition hUE huM)
    (spThreeGraphRowInput_linearOdd_of_cover hLO) (spThreeGraphRowInput_unitaryOdd_of_cover hUO)

end Rows

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

end CFSG.SeitzReduction.SymplecticPilot
