module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RankFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONKFacts
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksL34
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.ONSchreier CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec4.Census

theorem three_le_pRank_of_lifts' {Q X : Type*} [Group Q] [Finite Q] [Group X] {φ : Q →* X}
    (hφ : Function.Surjective φ) (hker : φ.ker = center Q) {W : Subgroup X}
    (hW4 : 4 ≤ Nat.card W) (hcomm : ∀ y y' : Q, φ y ∈ W → φ y' ∈ W → y * y' = y' * y)
    (hsq : ∀ y : Q, φ y ∈ W → ∃ c : Q, φ c = 1 ∧ y ^ 2 = c ^ 2) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) : 3 ≤ CFSG.pRank 2 Q := by
  obtain ⟨A, hA, hcard⟩ := TransitiveLift.exists_isElementaryAbelian_card hφ hker.le hcomm hsq
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    omega
  have hzk : φ z = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hzZ
  have hz2' : z ^ 2 = 1 := by rw [← hz2, pow_orderOf_eq_one]
  have hΩ : 2 ≤ Nat.card {c : Q // φ c = 1 ∧ c ^ 2 = 1} := by
    have : Nontrivial {c : Q // φ c = 1 ∧ c ^ 2 = 1} :=
      ⟨⟨⟨1, map_one φ, one_pow 2⟩, ⟨z, hzk, hz2'⟩, fun h => hz1 (congrArg Subtype.val h).symm⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.mpr this
  refine TransitiveLift.le_pRank_of_card hA (k := 3) ?_
  rw [hcard]
  calc 2 ^ 3 = 4 * 2 := by norm_num
    _ ≤ _ := Nat.mul_le_mul hW4 hΩ

theorem three_le_pRank_of_L34' {Q : Type} [Group Q] [Finite Q]
    (hL : LieModel (Q ⧸ center Q) .PSL 3 2 2) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) : 3 ≤ CFSG.pRank 2 Q := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel hL (by decide)
  have : CharP K 2 := CFSG.LieType.Steinberg.CentralExt.GriessNative.charP_two_of_card
    (by norm_num) hK rfl
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  let e' : Q ⧸ center Q ≃* Assembly.RankThreeEven.projSL 3 K :=
    e.trans (RankThree.PartTwo.KFacts.KS44.projSLEquivStatedProj K).symm
  have hφ : Function.Surjective (e'.toMonoidHom.comp (QuotientGroup.mk' (center Q))) :=
    e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : (e'.toMonoidHom.comp (QuotientGroup.mk' (center Q))).ker = center Q := by
    ext y
    rw [MonoidHom.mem_ker]
    change e' (QuotientGroup.mk y) = 1 ↔ _
    rw [map_eq_one_iff e' e'.injective, QuotientGroup.eq_one_iff]
  refine three_le_pRank_of_lifts' hφ hker (W := (DoubleCoverRanksTwo.rootHom (K := K)).range)
    ?_ (fun y y' hy hy' => DoubleCoverRanksTwo.commute_lift_rootHom hφ hker.le hy hy')
    (fun y hy => ?_) hzZ hz2
  · rw [DoubleCoverRanksTwo.card_range_rootHom, hK4]
  · obtain ⟨a, ha⟩ := hy
    exact DoubleCoverRanksTwo.exists_sq_eq_sq_E hφ hker.le (by omega)
      (ha ▸ DoubleCoverRanksTwo.rootHom_mem_range_uHom a)

section ON


theorem three_le_pRank_onL : 3 ≤ CFSG.pRank 2 ↥onL := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card (center ↥onL) := by rw [card_center_onL]; norm_num
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center ↥onL) 2 hdvd
  have : Finite ↥onL := Nat.finite_of_card_ne_zero (by rw [card_onL]; norm_num)
  refine three_le_pRank_of_L34' (Or.inl ⟨by decide, lQuot_classicalModel⟩) (z := (z : ↥onL))
    z.2 ?_
  rw [Subgroup.orderOf_coe, hz]

theorem on_pRank_K (X : Type) [Group X] (hX : IsOddCentralExt ↥onL X) : 3 ≤ CFSG.pRank 2 X :=
  three_le_pRank_of_oddCentralExt three_le_pRank_onL hX

end ON

end CFSG.EvenSporadicStandard.Induction
