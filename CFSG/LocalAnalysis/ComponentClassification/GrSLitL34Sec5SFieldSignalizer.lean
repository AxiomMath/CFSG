module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open Matrix
open scoped MatrixGroups

@[expose] def L34FieldSignalizerGluing : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (P : Subgroup G), L34FieldNormalSetting G t P →
    ∃ W : Subgroup G, Odd (Nat.card W) ∧ normalizer (P : Set G) ≤ normalizer (W : Set G) ∧
      ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
        8 ≤ Nat.card E → GrSLit.wGroup E = W

theorem gwTwoBalanced_of_l34FieldNormalSetting {G : Type} [Group G] [Finite G] {t : G}
    {P : Subgroup G} (h : L34FieldNormalSetting G t P) : GWTwoBalanced G :=
  GrSLit.gwTwoBalanced_of_locallyTwoBalanced GrSLit.solomonCommutingCoreInput h.1.2.2.2.2.2.1

theorem odd_card_wGroup {G : Type} [Group G] [Finite G] (hB : GWTwoBalanced G) {A : Subgroup G}
    (hA : IsElemTwo A) (h16 : 16 ≤ Nat.card A) : Odd (Nat.card (GrSLit.wGroup A)) := by
  rw [wGroup_eq_completion hA]
  exact Nat.coprime_two_left.mp
    (CFSG.ClassicalInvolution.Balance.isComplete_deltaCore hA.isElemAbelian h16
      (twoBalancedWrt_of_gwTwoBalanced hB hA)).1.1

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
