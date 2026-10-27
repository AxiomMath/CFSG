module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SevenSwapMain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

@[expose] def LinearTwoFieldKindFiveSixInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [CharP K 2], Nat.card K = 2 → 5 ≤ n → n ≤ 6 →
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

@[expose] def LinearTwoSwapRowFiveSixInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [CharP K 2], Nat.card K = 2 → 5 ≤ n → n ≤ 6 →
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

@[expose] def LinearTwoSmallKindFiveSixInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [CharP K 2], Nat.card K = 2 → 5 ≤ n → n ≤ 6 →
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

theorem linearTwoFiveSixInput_of_kinds (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor3 : CatSLmSporadicAt 3) (hSpor4 : CatSLmSporadicAt 4)
    (hF : LinearTwoFieldKindFiveSixInput) (hS : LinearTwoSwapRowFiveSixInput)
    (hR : LinearTwoSmallKindFiveSixInput) : LinearTwoFiveSixInput := by
  intro G _ _ L hset n K _ _ _ hK hn5 hn6 e t ht hKt
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  have hSpor : CatSLmSporadicAt (n - 2) := by
    rcases (show n - 2 = 3 ∨ n - 2 = 4 by omega) with h | h
    · rw [h]; exact hSpor3
    · rw [h]; exact hSpor4
  have hcat : SLmCatalogueClausesAt (n - 2) :=
    slmCatalogueClausesAt_of_gls3_sporadic (by omega) hGLS hSpor
  have hdet : SLmEvenTypeDetAt (n - 2) := slmEvenTypeDetAt (by omega)
  refine hS G L hset n K hK hn5 hn6 e t ht hKt fun a b hab X₀ hX₀ hX₀c htX => ?_
  rcases neighbour_overgroup_linear_two_field_or_small hset hcat hdet hK e hn5 htC ht hab hX₀ hX₀c
      rfl htX rfl with ⟨⟨Kc, hKcomp, hDKK, hrow⟩, hZ⟩ | hsmall
  · rcases hrow with ⟨-, hDK, -, hsN, hτ, -, hmodel, -⟩ | ⟨hKt', hcomm, hZK, hiso⟩
    · exact (hF G L hset n K hK hn5 hn6 e t ht hKt a b hab X₀ hX₀ hX₀c htX hZ Kc hKcomp hDK.le
        hsN hτ hmodel).elim
    · exact ⟨Kc, hKcomp, hDKK, hKt', hcomm, hZK, hiso⟩
  · exact (hR G L hset n K hK hn5 hn6 e t ht hKt a b hab X₀ hX₀ hX₀c htX hsmall).elim

end CFSG.SeitzReduction.LinearPilot
