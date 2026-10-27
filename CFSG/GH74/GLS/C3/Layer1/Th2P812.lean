module

public import CFSG.GH74.GLS.C3.Layer1.Th2CaseI
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def B_thm2_A7_exc : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → ¬ IsExceptionalA7Triple x y K

@[expose] def B_thm2_p812_II : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G) (ρ : Th2Row)
    (B : Subgroup G), Th2M2 x y K T S M ρ B → K ≤ M →
      IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K) →
        ∀ L : Subgroup G, IsMinSubnormalIn K M L → IsPCompIn 2 M L → L = pPrimeCoreOf 2 L ⊔ K →
          2 ≤ pRank 2 ↥(T ⊓ CxK x K) → gammaK 2 (T ⊓ CxK x K) 1 ≤ M

theorem Th2Std.two_le_pRank_Q {G : Type} [Group G] [Finite G] (hA7 : B_thm2_A7_exc)
    (hG : C3Hyp G) {x y : G} {K T S : Subgroup G} (h : Th2Std x y K T S) :
    2 ≤ pRank 2 ↥(T ⊓ CxK x K) := by
  rcases h.v2ss.isV2Triple.2.2.1 with h1 | h1
  · rw [Th2.pRank_eq_of_isSylowOf h.sylow_Q]
    exact h1
  · exact (hA7 G hG x y K T S h h1).elim

theorem b_thm2_p812_of (hA7 : B_thm2_A7_exc) (hII : B_thm2_p812_II) : B_thm2_p812 := by
  intro G _ _ hG x y K T S M hchoice hKM hQ L hL hLcomp hLeq
  have hrk : 2 ≤ pRank 2 ↥(T ⊓ CxK x K) := hchoice.std.two_le_pRank_Q hA7 hG
  refine ⟨?_, hrk⟩
  rcases hchoice with h1 | ⟨ρ, B, h2⟩
  · exact (Th2.CaseI.gammaK_le_normalizer_of_standard h1.standard h1.sylowQ).trans h1.le_M
  · exact hII G hG x y K T S M ρ B h2 hKM hQ L hL hLcomp hLeq hrk

end CFSG.GH74.GLS
