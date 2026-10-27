module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2FiveSixField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SevenSwapFiveSix

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

@[expose] def LinearTwoFieldKindAtInput (n₀ : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [CharP K 2], Nat.card K = 2 → n = n₀ →
    ∀ (e : L ≃* LinearFlag.projectiveSL n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (a b : Fin n) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL n K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G),
      center (((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))))) = ⊥ →
      ∀ Kc : Subgroup (centralizer (modelToG e X₀ : Set G) ⧸
        oddCore (centralizer (modelToG e X₀ : Set G))), IsComponent Kc →
      ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
          (centralizer (modelToG e X₀ : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) ≤ Kc →
      ∀ hsN : QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩ ∈
        normalizer (Kc : Set (centralizer (modelToG e X₀ : Set G) ⧸
          oddCore (centralizer (modelToG e X₀ : Set G)))),
      Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range →
      LieModel Kc .PSL (n - 2) 2 (2 * 1) → False

@[expose] def LinearTwoSwapRowAtInput (n₀ : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [CharP K 2], Nat.card K = 2 → n = n₀ →
    ∀ (e : L ≃* LinearFlag.projectiveSL n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ (a b : Fin n) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL n K)),
        X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
        ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G),
        ∃ Kc : Subgroup (centralizer (modelToG e X₀ : Set G) ⧸
            oddCore (centralizer (modelToG e X₀ : Set G))),
          IsComponent Kc ∧
          ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
              (centralizer (modelToG e X₀ : Set G))).map
                (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))) ≤
            Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e X₀ : Set G))) ⟨t, htX⟩)).toMonoidHom ∧
          Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e X₀ : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc ∧
          ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e X₀ : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ ∧
          center Kc = ⊥ ∧
          Nonempty (Kc ≃* ((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
              (centralizer (modelToG e X₀ : Set G))).map
                (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G)))))) → False

@[expose] def LinearTwoSmallKindAtInput (n₀ : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [CharP K 2], Nat.card K = 2 → n = n₀ →
    ∀ (e : L ≃* LinearFlag.projectiveSL n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (a b : Fin n) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL n K)),
      X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
      ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G),
      NeighbourOvergroupSLmSmall
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩)
        (((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
          (centralizer (modelToG e X₀ : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))))) (n - 2) 1 →
      False

theorem linearTwoFieldKindFiveSixInput_of_at (h5 : LinearTwoFieldKindAtInput 5)
    (h6 : LinearTwoFieldKindAtInput 6) : LinearTwoFieldKindFiveSixInput := by
  intro G _ _ L hset n K _ _ hK hn5 hn6
  rcases (show n = 5 ∨ n = 6 by omega) with h | h
  · exact h5 G L hset n K hK h
  · exact h6 G L hset n K hK h

theorem linearTwoSwapRowFiveSixInput_of_at (h5 : LinearTwoSwapRowAtInput 5)
    (h6 : LinearTwoSwapRowAtInput 6) : LinearTwoSwapRowFiveSixInput := by
  intro G _ _ L hset n K _ _ hK hn5 hn6
  rcases (show n = 5 ∨ n = 6 by omega) with h | h
  · exact h5 G L hset n K hK h
  · exact h6 G L hset n K hK h

theorem linearTwoSmallKindFiveSixInput_of_at (h5 : LinearTwoSmallKindAtInput 5)
    (h6 : LinearTwoSmallKindAtInput 6) : LinearTwoSmallKindFiveSixInput := by
  intro G _ _ L hset n K _ _ hK hn5 hn6
  rcases (show n = 5 ∨ n = 6 by omega) with h | h
  · exact h5 G L hset n K hK h
  · exact h6 G L hset n K hK h

theorem linearTwoFieldKindAtInput_six_of_revComm (hrev : LinearTwoFieldRevCommSixInput) :
    LinearTwoFieldKindAtInput 6 := by
  intro G _ _ L hset n K _ _ hK hn e t ht hKt a b hab X₀ hX₀ hX₀c htX hZ Kc hKcomp hDK hsN hτ
    hmodel
  exact false_of_fieldKind_two_six_of_revComm hrev hset hK e hn ht hKt hab hX₀ hX₀c htX hZ hKcomp
    hDK hsN hτ hmodel

section Assembly

theorem linearTwoFiveSixInput_of_at_of_revComm (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor3 : CatSLmSporadicAt 3) (hSpor4 : CatSLmSporadicAt 4)
    (hF5 : LinearTwoFieldKindAtInput 5) (hS5 : LinearTwoSwapRowAtInput 5)
    (hR5 : LinearTwoSmallKindAtInput 5) (hrev : LinearTwoFieldRevCommSixInput)
    (hS6 : LinearTwoSwapRowAtInput 6) (hR6 : LinearTwoSmallKindAtInput 6) :
    LinearTwoFiveSixInput :=
  linearTwoFiveSixInput_of_kinds hGLS hSpor3 hSpor4
    (linearTwoFieldKindFiveSixInput_of_at hF5 (linearTwoFieldKindAtInput_six_of_revComm hrev))
    (linearTwoSwapRowFiveSixInput_of_at hS5 hS6) (linearTwoSmallKindFiveSixInput_of_at hR5 hR6)

end Assembly

end CFSG.SeitzReduction.LinearPilot
