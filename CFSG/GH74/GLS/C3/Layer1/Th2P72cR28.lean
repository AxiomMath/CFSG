module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR27

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs

@[expose] def B_row4b_714 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → ¬ IsTerminalPair 2 x K → Th2Row.r4b.holds x y K T S →
      (∀ B ∈ Th2Row.r4b.BT x K T S, Th2Row.r4b.level.IsBal B) →
        ∀ (B : Subgroup G) (t : G) (J : Subgroup G), Th2Pick .r4b x y K T S B t J →
          2 ≤ pRank 2 ↥(B ⊓ (T ⊓ CxK x K)) → Th2Row.r4b.level.theta B = ⊥ →
            (∀ B₀ : Subgroup G, B₀ ≤ T → CFSG.IsElementaryAbelian 2 ↥B₀ → 4 ≤ pRank 2 ↥B₀ →
              ∀ u ∈ B₀, u ∈ T ⊓ CxK x K → orderOf u = 2 →
                ∀ y' ∈ B₀, y' ∉ (T ⊓ K) ⊔ (T ⊓ CxK x K) →
                  ∀ J' : Subgroup G, PumpUpLT 2 x K u J' → CFSG.IsQuasisimple ↥J') →
              False

theorem b_thm2_p72c_row4b_of_leaf
    (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (h102a : B_ivk_10_2a) (hKG : B_ivk_oddcent)
    (h218 : B_IG_21_8) (h2110 : B_IG_21_10) (hleaf : B_row4b_714) : B_thm2_p72c_row4b := by
  intro G _ _ hG x y K T S hstd hnt hrow hbal B t J hpick hE2
  by_contra hθ
  have hθ' : Th2Row.r4b.level.theta B = ⊥ := hθ
  refine hleaf G hG x y K T S hstd hnt hrow hbal B t J hpick hE2 hθ' ?_
  intro B₀ hB₀T hB₀el hB₀rk u huB huQ hu2 y' hy'B hy'R J' hJ'
  exact p713_of_B0 hL34 h102 h102a hKG h218 h2110 hG hstd hrow hbal hpick.mem hθ' hB₀T hB₀el
    hB₀rk huB huQ hu2 hy'B hy'R hJ'

end CFSG.GH74.GLS
