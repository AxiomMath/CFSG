module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup CFSG.LocalCores

theorem four_pow_dvd_card (Y : Type) [Group Y] [Finite Y] :
    4 ^ Nat.card (ComponentIndex Y) ∣ Nat.card Y := by
  classical
  have hfour : ∀ K : ComponentIndex Y, ∃ A : Subgroup (K.1 ⧸ center K.1),
      CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 4 := by
    intro K
    have : IsSimpleGroup (K.1 ⧸ center K.1) := K.2.1.2.1
    have hnc : ∃ a b : K.1 ⧸ center K.1, a * b ≠ b * a := K.2.1.2.2
    have hq := CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup hnc
    have hcen : center (K.1 ⧸ center K.1) = ⊥ :=
      CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hnc
    exact CFSG.LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
      (CFSG.LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hq
        (by rw [hcen, Subgroup.card_bot]; exact odd_one))
  choose A _hA hAc using hfour
  let φ : (∀ K : ComponentIndex Y, ↥(A K)) →* (∀ K : ComponentIndex Y, K.1 ⧸ center K.1) :=
    MonoidHom.pi fun K => (A K).subtype.comp (Pi.evalMonoidHom _ K)
  have hφ : Function.Injective φ := fun x y hxy => funext fun K =>
    Subtype.ext (congrFun hxy K)
  let E : Subgroup (∀ K : ComponentIndex Y, K.1 ⧸ center K.1) := φ.range
  have hEcard : Nat.card E = 4 ^ Nat.card (ComponentIndex Y) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm, Nat.card_pi]
    simp only [hAc, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have h1 : Nat.card E ∣ Nat.card (∀ K : ComponentIndex Y, K.1 ⧸ center K.1) :=
    Subgroup.card_subgroup_dvd_card E
  have h2 : Nat.card (∀ K : ComponentIndex Y, K.1 ⧸ center K.1) =
      Nat.card (layer Y ⧸ center (layer Y)) :=
    Nat.card_congr (layerCentralQuotientEquiv Y).toEquiv
  have h3 : Nat.card (∀ K : ComponentIndex Y, K.1 ⧸ center K.1) ∣ Nat.card (layer Y) := by
    rw [h2]
    exact Subgroup.card_quotient_dvd_card (center (layer Y))
  have h4 : Nat.card (layer Y) ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card (layer Y)
  rw [← hEcard]
  exact h1.trans (h3.trans h4)

end CFSG.EvenSporadicStandard.M12Std.SolomonK
