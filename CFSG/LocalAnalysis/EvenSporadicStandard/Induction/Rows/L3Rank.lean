module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RankFacts
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksL34
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Census

theorem three_le_pRank_of_lifts_cover {Q X : Type*} [Group Q] [Finite Q] [Group X] {φ : Q →* X}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center Q) {W : Subgroup X}
    (hW4 : 4 ≤ Nat.card W) (hcomm : ∀ y y' : Q, φ y ∈ W → φ y' ∈ W → y * y' = y' * y)
    (hsq : ∀ y : Q, φ y ∈ W → ∃ c : Q, φ c = 1 ∧ y ^ 2 = c ^ 2) {z : Q} (hzk : φ z = 1)
    (hz2 : orderOf z = 2) : 3 ≤ CFSG.pRank 2 Q := by
  obtain ⟨A, hA, hcard⟩ := TransitiveLift.exists_isElementaryAbelian_card hφ hker hcomm hsq
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    omega
  have hz2' : z ^ 2 = 1 := by rw [← hz2, pow_orderOf_eq_one]
  have hΩ : 2 ≤ Nat.card {c : Q // φ c = 1 ∧ c ^ 2 = 1} := by
    have : Nontrivial {c : Q // φ c = 1 ∧ c ^ 2 = 1} :=
      ⟨⟨⟨1, map_one φ, one_pow 2⟩, ⟨z, hzk, hz2'⟩, fun h => hz1 (congrArg Subtype.val h).symm⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.mpr this
  refine TransitiveLift.le_pRank_of_card hA (k := 3) ?_
  rw [hcard]
  calc 2 ^ 3 = 4 * 2 := by norm_num
    _ ≤ _ := Nat.mul_le_mul hW4 hΩ

section L3

variable {G : Type} [Group G] {n : ℕ}

theorem exists_projSL_of_lieModel_psl_three (hn : 1 ≤ n) (h : LieModel G .PSL 3 2 n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      Nonempty (G ≃* CFSG.Assembly.RankThreeEven.projSL 3 K) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel h (by decide)
  have : CharP K 2 :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.charP_two_of_card hn hK rfl
  exact ⟨K, inferInstance, inferInstance, this, hK,
    ⟨e.trans (CFSG.RankThree.PartTwo.KFacts.KS44.projSLEquivStatedProj K).symm⟩⟩

theorem three_le_pRank_psl_three [Finite G] (hn : 2 ≤ n) (h : LieModel G .PSL 3 2 n) :
    3 ≤ CFSG.pRank 2 G := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_projSL_of_lieModel_psl_three (by omega) h
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : Finite ↥(CFSG.Assembly.RankThreeEven.projSL 3 K) := Finite.of_equiv G e.toEquiv
  rw [pRank_two_eq_of_mulEquiv' e]
  have hcomm : ∀ y y' : ↥(CFSG.Assembly.RankThreeEven.projSL 3 K),
      (MonoidHom.id _) y ∈ (DoubleCoverRanksTwo.uHom (K := K)).range →
      (MonoidHom.id _) y' ∈ (DoubleCoverRanksTwo.uHom (K := K)).range → y * y' = y' * y := by
    rintro y y' ⟨v, rfl⟩ ⟨v', rfl⟩
    rw [← map_mul, ← map_mul, mul_comm v v']
  have hsq : ∀ y : ↥(CFSG.Assembly.RankThreeEven.projSL 3 K),
      (MonoidHom.id _) y ∈ (DoubleCoverRanksTwo.uHom (K := K)).range →
        ∃ c, (MonoidHom.id _) c = 1 ∧ y ^ 2 = c ^ 2 := fun y hy =>
    ⟨1, rfl, by rw [one_pow]; exact DoubleCoverRanksTwo.sq_eq_one_of_mem_range_uHom hy⟩
  obtain ⟨A, hA, hcard⟩ := TransitiveLift.exists_isElementaryAbelian_card
    (φ := MonoidHom.id ↥(CFSG.Assembly.RankThreeEven.projSL 3 K)) Function.surjective_id
    (by simp) hcomm hsq
  refine TransitiveLift.le_pRank_of_card hA (k := 3) ?_
  rw [hcard, DoubleCoverRanksTwo.card_range_uHom]
  have h1 : 1 ≤ Nat.card {c : ↥(CFSG.Assembly.RankThreeEven.projSL 3 K) //
      (MonoidHom.id _) c = 1 ∧ c ^ 2 = 1} :=
    Nat.card_pos_iff.2 ⟨⟨⟨1, rfl, one_pow 2⟩⟩, inferInstance⟩
  calc 2 ^ 3 = 4 * 4 / 2 := by norm_num
    _ ≤ Nat.card K * Nat.card K := by
      have := Nat.mul_le_mul hK4 hK4
      omega
    _ ≤ Nat.card K * Nat.card K * _ := Nat.le_mul_of_pos_right _ h1

theorem three_le_pRank_of_cover_L3 {J : Type} [Group J] [Finite J] (hn : 2 ≤ n)
    (hL : LieModel G .PSL 3 2 n) {φ : J →* G} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ center J) : 3 ≤ CFSG.pRank 2 J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGfin : Finite G := Finite.of_surjective φ hφ
  by_cases hdvd : 2 ∣ Nat.card φ.ker
  · obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_projSL_of_lieModel_psl_three (by omega) hL
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hK3 : 3 ≤ Nat.card K := by omega
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) 2 hdvd
    set φ' : J →* ↥(CFSG.Assembly.RankThreeEven.projSL 3 K) := e.toMonoidHom.comp φ with hφ'
    have hφ's : Function.Surjective φ' := e.surjective.comp hφ
    have hker' : φ'.ker ≤ center J := by
      intro y hy
      apply hker
      rw [MonoidHom.mem_ker]
      have h1 : e (φ y) = 1 := hy
      exact e.injective (by rw [h1, map_one])
    refine three_le_pRank_of_lifts_cover hφ's hker'
      (W := (DoubleCoverRanksTwo.rootHom (K := K)).range) ?_
      (fun y y' hy hy' => DoubleCoverRanksTwo.commute_lift_rootHom hφ's hker' hy hy')
      (fun y hy => ?_) (z := (z : J)) ?_ ?_
    · rw [DoubleCoverRanksTwo.card_range_rootHom]
      exact hK4
    · obtain ⟨a, ha⟩ := hy
      exact DoubleCoverRanksTwo.exists_sq_eq_sq_E hφ's hker' hK3
        (ha ▸ DoubleCoverRanksTwo.rootHom_mem_range_uHom a)
    · have hzk : φ (z : J) = 1 := MonoidHom.mem_ker.1 z.2
      simp [hφ', hzk]
    · rw [Subgroup.orderOf_coe, hz]
  · rw [← CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two φ.ker
      hdvd, pRank_two_eq_of_mulEquiv' (QuotientGroup.quotientKerEquivOfSurjective φ hφ)]
    exact three_le_pRank_psl_three hn hL

theorem three_le_pRank_of_quotient_L3 {X : Type} [Group X] [Finite X] (hn : 2 ≤ n)
    (hL : LieModel (X ⧸ center X) .PSL 3 2 n) : 3 ≤ CFSG.pRank 2 X :=
  three_le_pRank_of_cover_L3 hn hL (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])

end L3

end CFSG.EvenSporadicStandard.Induction
