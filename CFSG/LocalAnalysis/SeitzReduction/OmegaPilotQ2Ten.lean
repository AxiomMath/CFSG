module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2SwapMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Minus

@[expose] def OmegaMinusTwoTenHR8Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG e (anisoPerp (K := K) (by norm_num) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))))).Normal →
        ∀ htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G),
          NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))) ⟨t, htX⟩)
            (((modelToG e (anisoPerp (K := K) (by norm_num) b c)).subgroupOf
                (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))))) 4 1

@[expose] def OmegaMinusTwoTenFieldInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG e (anisoPerp (K := K) (by norm_num) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))))).Normal →
        (∀ htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G),
          NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))) ⟨t, htX⟩)
            (((modelToG e (anisoPerp (K := K) (by norm_num) b c)).subgroupOf
                (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))))) 4 1) →
        OmegaRowAt t (modelToG e (anisoTorus (K := K) (by norm_num) b c))
          (modelToG e (anisoPerp (K := K) (by norm_num) b c)) .field → False


theorem omegaMinusTwoTen_swap {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : SeitzSetting G L) {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK2 : Nat.card K = 2)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {m f : ℕ}
    (hN : ∀ htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G),
      NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))) ⟨t, htX⟩)
        (((modelToG e (anisoPerp (K := K) (by norm_num) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))))) m f)
    (hr : OmegaRowAt t (modelToG e (anisoTorus (K := K) (by norm_num) b c))
      (modelToG e (anisoPerp (K := K) (by norm_num) b c)) .swap) : False := by
  obtain rfl : b = 1 := eq_one_of_ne_zero_of_card_two hK2 (coeff_ne_zero_of_irreducible' hirr)
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  obtain ⟨Ψ, hinj, hrange⟩ := exists_swapParam_anisoTorus hset hKc le_rfl hirr e htC ht hN hr
  exact false_of_swapTriangleFrame hset
    (isSolvable_outer_of_mulEquiv_minus (by norm_num) le_rfl hKc hirr e) e
    (swapPairExclusion_coordinateMinus_two hK2 le_rfl _ hirr) ht hKt e
    (swapTriangleFrame_anisoTorus le_rfl hirr) Ψ hinj hrange

theorem omegaMinusTwoTenInput_of_inputs (hHR8 : OmegaMinusTwoTenHR8Input)
    (hfield : OmegaMinusTwoTenFieldInput) : OmegaMinusTwoTenInput := by
  intro G _ _ L hset K _ _ _ b c hirr hK2 e t ht hKt hnn
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hN := hHR8 G L hset K b c hirr hK2 e t ht hKt hnn
  obtain ⟨-, htX, -⟩ := neighbour_data_anisoTorus (by norm_num) hirr e htC rfl rfl
  obtain ⟨r, hr⟩ := exists_omegaRowAt_of_neighbourOvergroupOmega htX (hN htX)
  cases r with
  | field => exact hfield G L hset K b c hirr hK2 e t ht hKt hnn hN hr
  | swap => exact omegaMinusTwoTen_swap hset hirr hK2 e ht hKt hN hr

end Minus

section Plus

@[expose] def OmegaPlusTwoTenHR8Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 2) K)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
            (plusAnisoPerp (K := K) 3 b c)).subgroupOf
            (centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr) : Set G))))).Normal →
        ∀ htX : t ∈ centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
            (plusAnisoTorus 3 hirr) : Set G),
          NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
              (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                (plusAnisoTorus 3 hirr) : Set G))) ⟨t, htX⟩)
            (((modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                (plusAnisoPerp (K := K) 3 b c)).subgroupOf
                (centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                  (plusAnisoTorus 3 hirr) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                  (plusAnisoTorus 3 hirr) : Set G))))) 4 1

@[expose] def OmegaPlusTwoTenFieldInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 2) K)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
            (plusAnisoPerp (K := K) 3 b c)).subgroupOf
            (centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr) : Set G))))).Normal →
        (∀ htX : t ∈ centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
            (plusAnisoTorus 3 hirr) : Set G),
          NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
              (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                (plusAnisoTorus 3 hirr) : Set G))) ⟨t, htX⟩)
            (((modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                (plusAnisoPerp (K := K) 3 b c)).subgroupOf
                (centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                  (plusAnisoTorus 3 hirr) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                  (plusAnisoTorus 3 hirr) : Set G))))) 4 1) →
        OmegaRowAt t (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm) (plusAnisoTorus 3 hirr))
          (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm) (plusAnisoPerp (K := K) 3 b c))
          .field → False

@[expose] def OmegaPlusTwoTenFrameInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (c : K) (hirr : ∀ s : K, s ^ 2 + 1 * s + c ≠ 0),
    Nat.card K = 2 → SwapTriangleFrame (plusAnisoTorus 3 hirr) (plusAnisoPerp (K := K) 3 1 c)


theorem omegaPlusTwoTen_swap (hframe : OmegaPlusTwoTenFrameInput) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : SeitzSetting G L) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK2 : Nat.card K = 2)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 2) K)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {m' f' : ℕ}
    (hN : ∀ htX : t ∈ centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
        (plusAnisoTorus 3 hirr) : Set G),
      NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
          (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm) (plusAnisoTorus 3 hirr) :
            Set G))) ⟨t, htX⟩)
        (((modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
            (plusAnisoPerp (K := K) 3 b c)).subgroupOf
            (centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm) (plusAnisoTorus 3 hirr) :
              Set G))))) m' f')
    (hr : OmegaRowAt t (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
        (plusAnisoTorus 3 hirr))
      (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm) (plusAnisoPerp (K := K) 3 b c)) .swap) :
    False := by
  obtain rfl : b = 1 := eq_one_of_ne_zero_of_card_two hK2 (coeff_ne_zero_of_irreducible' hirr)
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  obtain ⟨Ψ, hinj, hrange⟩ :=
    exists_swapParam_plusAnisoTorus hset hKc le_rfl hirr e htC ht hN hr
  exact false_of_swapTriangleFrame hset
    (isSolvable_outer_of_mulEquiv_plus (by norm_num) le_rfl hKc e) e
    (swapPairExclusion_coordinatePlus_two hK2 (by norm_num)) ht hKt _
    (hframe K c hirr hK2) Ψ hinj hrange

theorem omegaPlusTwoTenInput_of_inputs (hHR8 : OmegaPlusTwoTenHR8Input)
    (hfield : OmegaPlusTwoTenFieldInput) (hframe : OmegaPlusTwoTenFrameInput) :
    OmegaPlusTwoTenInput := by
  intro G _ _ L hset K _ _ _ b c hirr hK2 e t ht hKt hnn
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hN := hHR8 G L hset K b c hirr hK2 e t ht hKt hnn
  obtain ⟨-, htX, -⟩ := neighbour_data_plusAnisoTorus le_rfl hirr
    (e.trans (plusAnisoProjEquiv 3 hirr).symm) htC rfl rfl
  obtain ⟨r, hr⟩ := exists_omegaRowAt_of_neighbourOvergroupOmega htX (hN htX)
  cases r with
  | field => exact hfield G L hset K b c hirr hK2 e t ht hKt hnn hN hr
  | swap => exact omegaPlusTwoTen_swap hframe hset hirr hK2 e ht hKt hN hr

end Plus

end CFSG.SeitzReduction.OmegaPilot
