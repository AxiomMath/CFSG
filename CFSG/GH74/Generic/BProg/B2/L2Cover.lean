module

public import CFSG.RankThree.PerfectCover.HopfCentralCoversLift
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.Alternating.Multipliers.Small
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.RankThree.PerfectCover CFSG.LieType.Steinberg.CentralExt CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

namespace L2Cover

theorem card_hopfMultiplier_psl2
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) :
    ∃ m : ℕ, Odd m ∧ Nat.card (hopfMultiplier PSL(2, F)) = 2 * m := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = Nat.card F := Fintype.card_eq_nat_card
  by_cases h9 : Nat.card F = 9
  · refine ⟨3, by decide, ?_⟩
    obtain ⟨e⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
        F (hcardF.trans h9)
    obtain ⟨-, h6⟩ := CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six
    have h1 := Nat.card_congr ((hopfMultiplierEquivGriess _).symm.trans
      ((griessHopfMultiplierCongr e).trans (hopfMultiplierEquivGriess _))).toEquiv
    rw [h1, h6]
  · refine ⟨1, odd_one, ?_⟩
    obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.psl_two_hopfMultiplier
      (k := F) (by omega) (by omega)
    have h1 := Nat.card_congr ((hopfMultiplierEquivGriess _).symm.trans e).toEquiv
    rw [h1, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have hg : Nat.gcd 2 (Fintype.card F - 1) = 2 := by
      obtain ⟨k, hk⟩ := hodd
      exact Nat.gcd_eq_left ⟨k, by omega⟩
    rw [hg]

theorem card_center_dvd_card_hopfMultiplier_qs {K X : Type} [Group K] [Group X] [Finite K]
    (hK : IsQuasisimple K) (e : K ⧸ center K ≃* X) :
    Nat.card (center K) ∣ Nat.card (hopfMultiplier X) := by
  have := hK.1
  have h1 := Subgroup.card_dvd_of_surjective
    (hopfMultiplierToKer_surjective (centralQuotientMap e) (centralQuotientMap_surjective e)
      (centralQuotientMap_ker e).le)
  rwa [centralQuotientMap_ker e] at h1

theorem l2_cover_two_group
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) (h2 : IsPGroup 2 ↥(center J))
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (e : J ⧸ center J ≃* PSL(2, F)) :
    center J = ⊥ ∨ (Nat.card (center J) = 2 ∧ Nonempty (J ≃* SL(2, F))) := by
  classical
  obtain ⟨m, hm, hcardM⟩ := card_hopfMultiplier_psl2 hodd h5
  have hdvd : Nat.card (center J) ∣ 2 * m := hcardM ▸ card_center_dvd_card_hopfMultiplier_qs hq e
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (center J)) m := by
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
  have hdvd2 : Nat.card (center J) ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h1 | h2'
  · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h1)
  · refine Or.inr ⟨h2', ?_⟩
    have h4 : ∃ s : Finset F, s.card = 4 := by
      have := Fintype.ofFinite F
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
      exact ⟨s, hs⟩
    have hS₀ : Group.IsPerfect SL(2, F) :=
      CFSG.LinearGroups.special_linear_dimension_two_perfect h4
    set p₀ : SL(2, F) →* PSL(2, F) := QuotientGroup.mk' (center SL(2, F)) with hp₀def
    have hp₀ : Function.Surjective p₀ := QuotientGroup.mk'_surjective _
    have hk₀ : p₀.ker = center SL(2, F) := QuotientGroup.ker_mk' _
    have hcard2 : Nat.card p₀.ker = 2 := by
      rw [hk₀, CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 2 (by norm_num)]
      obtain ⟨k, hk⟩ := hodd
      exact Nat.gcd_eq_left ⟨k, by omega⟩
    obtain ⟨α, hαs, -⟩ := exists_lift_of_odd_index hS₀ hq.1 p₀ hp₀ hk₀.le
      (centralQuotientMap e) (centralQuotientMap_surjective e) (centralQuotientMap_ker e).le
      (by rw [centralQuotientMap_ker e]; exact h2) m hm (by rw [hcardM, hcard2])
    have hcardSL : Nat.card SL(2, F) = Nat.card PSL(2, F) * 2 := by
      rw [card_eq_card_mul_card_ker p₀ hp₀, hcard2]
    have hcardK : Nat.card J = Nat.card PSL(2, F) * 2 := by
      rw [card_eq_card_mul_card_ker (centralQuotientMap e) (centralQuotientMap_surjective e),
        centralQuotientMap_ker e, h2']
    have hb : Function.Bijective α :=
      hαs.bijective_of_nat_card_le (by rw [hcardSL, hcardK])
    exact ⟨(MulEquiv.ofBijective α hb).symm⟩

theorem isPGroup_two_center_of_no_odd {J : Type} [Group J] [Finite J]
    (h : ¬ ∃ z : J, z ≠ 1 ∧ (∀ g : J, g * z = z * g) ∧ Odd (orderOf z)) :
    IsPGroup 2 ↥(center J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : J)).ne'
  have hdvd : 2 ^ k ∣ orderOf (g : J) := ⟨m, hkm⟩
  have hord : orderOf ((g : J) ^ (2 ^ k)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hkm]
    exact Nat.mul_div_cancel_left m (pow_pos two_pos k)
  have hcen : ∀ y : J, y * ((g : J) ^ (2 ^ k)) = ((g : J) ^ (2 ^ k)) * y := by
    intro y
    have hc : Commute y (g : J) := Subgroup.mem_center_iff.1 g.2 y
    exact (hc.pow_right (2 ^ k)).eq
  have h1 : (g : J) ^ (2 ^ k) = 1 := by
    by_contra hne
    exact h ⟨_, hne, hcen, hord ▸ hm⟩
  refine ⟨k, ?_⟩
  have : m = 1 := by rw [← hord, h1, orderOf_one]
  rw [← Subgroup.orderOf_coe, hkm, this, mul_one]

theorem lieModel_psl2_of_equiv {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) (hF2 : p ^ f ≠ 2)
    (hF3 : p ^ f ≠ 3) (e : Y ≃* PSL(2, F)) : LieModel Y .PSL 2 p f := by
  have hadm : StatedLieAdmissible .PSL 2 p f :=
    ⟨hp, hf, le_rfl, fun h => hF2 (Prod.mk.inj h).2, fun h => hF3 (Prod.mk.inj h).2⟩
  exact Or.inl ⟨by decide, ⟨hadm, F, inferInstance, inferInstance, hF,
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F)⟩⟩⟩

end L2Cover

theorem l2_cover_cases
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hJ : LieModel (J ⧸ center J) .PSL 2 p f) :
    (∃ z : J, z ≠ 1 ∧ (∀ g : J, g * z = z * g) ∧ Odd (orderOf z)) ∨
      (center J = ⊥ ∧ LieModel J .PSL 2 p f) ∨
      (Nat.card (center J) = 2 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
        Nat.card K = p ^ f ∧ Nonempty (J ≃* SL(2, K))) := by
  by_cases hz : ∃ z : J, z ≠ 1 ∧ (∀ g : J, g * z = z * g) ∧ Odd (orderOf z)
  · exact Or.inl hz
  right
  have h2 := L2Cover.isPGroup_two_center_of_no_odd hz
  obtain ⟨-, hf, hF2, hF3, F, _, _, hF, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data hJ
  have hoddq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hodd : Odd (Nat.card F) := hF ▸ hoddq
  have h5 : 5 ≤ Nat.card F := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have hmod := Nat.odd_iff.1 hoddq
    rw [hF]
    omega
  rcases L2Cover.l2_cover_two_group hq h2 hodd h5 e with hZ | ⟨hc, ⟨φ⟩⟩
  · refine Or.inl ⟨hZ, L2Cover.lieModel_psl2_of_equiv hp hf hF hF2 hF3 ?_⟩
    exact (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  · exact Or.inr ⟨hc, F, inferInstance, inferInstance, hF, ⟨φ⟩⟩

end CFSG.GH74.Generic.BProg.B2
