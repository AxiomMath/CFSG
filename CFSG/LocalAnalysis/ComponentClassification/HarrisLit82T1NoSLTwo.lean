module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitClassical
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSchur
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs
public import CFSG.GH74.Generic.GKFLinear

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover CFSG.Blueprint
  CFSG.Blueprint.Multiplier CFSG.GH74.Generic
open scoped MatrixGroups

theorem psl2_cover_of_griessOdd (hGA : TBLit.GriessMultipliersOdd) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K)
    (h2 : IsPGroup 2 ↥(center K)) (hm : CFSG.Models.LieModel (K ⧸ center K) .PSL 2 p f) :
    center K = ⊥ ∨ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (K ≃* StatedSL 2 F) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := classical_psl_of_lieModel (by norm_num) hm
  have hoddp : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hmJ : CFSG.Models.LieModel (StatedProj (StatedSL 2 F)) .PSL 2 p f :=
    ⟨hm.1, Or.inl ⟨hm.1, F, inferInstance, inferInstance, hcard, ⟨MulEquiv.refl _⟩⟩⟩
  have hexc : Odd (exceptionalOrders .PSL 2 p f).1 ∧ Odd (exceptionalOrders .PSL 2 p f).2 := by
    unfold exceptionalOrders
    split <;> simp_all
    all_goals decide
  have h1 : Nat.gcd 2 (p ^ f - 1) = 2 := by
    obtain ⟨k, hk⟩ := hoddp
    exact Nat.gcd_eq_left ⟨k, by omega⟩
  have hgen : (genericOrders .PSL 2 p f) = (2, 1) := Prod.ext h1 rfl
  have hcardM : Nat.card (hopfMultiplier (StatedProj (StatedSL 2 F))) =
      2 * ((exceptionalOrders .PSL 2 p f).1 * (exceptionalOrders .PSL 2 p f).2) := by
    rw [← Nat.card_congr (hopfMultiplierEquivGriess _).toEquiv,
      card_griessHopfMultiplier_eq_odd hGA hmJ hp2 (Or.inl rfl), hgen]
    simp
  have hmodd : Odd ((exceptionalOrders .PSL 2 p f).1 * (exceptionalOrders .PSL 2 p f).2) :=
    hexc.1.mul hexc.2
  have hdvd := card_center_dvd_hopfMultiplier hK e
  rw [hcardM] at hdvd
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (center K))
      ((exceptionalOrders .PSL 2 p f).1 * (exceptionalOrders .PSL 2 p f).2) := by
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hmodd)
  have hdvd2 : Nat.card (center K) ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h1' | h2'
  · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h1')
  · refine Or.inr ⟨F, inferInstance, inferInstance, hcard, ?_⟩
    have h4 : ∃ s : Finset F, s.card = 4 := by
      have := Fintype.ofFinite F
      have h4le : 4 ≤ Nat.card F := by
        obtain ⟨-, -, -, hne2, hne3⟩ := hm.1
        have hq2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by
          obtain ⟨-, hf, -⟩ := hm.1
          omega) p)
        have h2'' : p ^ f ≠ 2 := fun h => hne2 (by rw [h])
        have h3' : p ^ f ≠ 3 := fun h => hne3 (by rw [h])
        rw [hcard]
        omega
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4le)
      exact ⟨s, hs⟩
    have hS₀ : Group.IsPerfect SL(2, F) := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
    obtain ⟨α, hαs, -⟩ := exists_lift_of_odd_index hS₀ hK.1 (pLin 2 F) (pLin_surjective 2 F)
      (pLin_ker 2 F).le (centralQuotientMap e) (centralQuotientMap_surjective e)
      (centralQuotientMap_ker e).le (by rw [centralQuotientMap_ker e]; exact h2) _ hmodd (by
        rw [hcardM, pLin_ker, CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 2
          (by norm_num), hcard, h1])
    have hcardSL : Nat.card SL(2, F) = Nat.card (StatedProj (StatedSL 2 F)) * 2 := by
      rw [card_eq_card_mul_card_ker (pLin 2 F) (pLin_surjective 2 F), pLin_ker,
        CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 2 (by norm_num), hcard, h1]
    have hcardK : Nat.card K = Nat.card (StatedProj (StatedSL 2 F)) * 2 := by
      rw [card_eq_card_mul_card_ker (centralQuotientMap e) (centralQuotientMap_surjective e),
        centralQuotientMap_ker e, h2']
    have hb : Function.Bijective α :=
      hαs.bijective_of_nat_card_le (by rw [hcardSL, hcardK])
    exact ⟨((MulEquiv.ofBijective α hb).symm).trans (specialLinearGroupEquivStatedSL 2 F)⟩

theorem isSLTwoOver_of_psl2Cover (hGA : TBLit.GriessMultipliersOdd) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K)
    (h2 : IsPGroup 2 ↥(center K)) (hZ : center K ≠ ⊥)
    (hm : Blueprint.LieModel (K ⧸ center K) .PSL 2 p f) : IsSLTwoOver (p ^ f) K := by
  rcases psl2_cover_of_griessOdd hGA hp hp2 hK h2
      (models_lieModel_of_lieModel_of_ne_zero (by norm_num) hm) with hbot | ⟨F, _, _, hF, ⟨e⟩⟩
  · exact absurd hbot hZ
  · let := Fintype.ofFinite F
    exact ⟨F, inferInstance, inferInstance, by rw [Fintype.card_eq_nat_card, hF],
      ⟨e.trans (specialLinearGroupEquivStatedSL 2 F).symm⟩⟩

theorem false_of_intrinsic_slTwo
    (hCI : GSLit.ClassicalInvolutionInput) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hcat : ¬ Blueprint.Catalog G) {u : G}
    (hu : orderOf u = 2) {J : Subgroup G} (hJ : IsTwoComponentIn J (centralizer {u}))
    (huJ : u ∈ J) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : IsSLTwoOver (p ^ k) (↥J ⧸ pPrimeCore 2 ↥J)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hq
  have hchar : ringChar F ≠ 2 :=
    FooteLit.ringChar_ne_two_of_card (hp.odd_of_ne_two hp2) (by rw [Nat.card_eq_fintype_card, hF])
  have hrank : CFSG.pRank 2 J ≤ 1 := by
    have hnd : ¬ 2 ∣ Nat.card (pPrimeCore 2 J) := fun h =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
    rw [← GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hnd,
      UnbalancedLayer.pRank_eq_of_mulEquiv one_lt_two e]
    exact TBLit.pRank_two_SL2_le_one hchar
  obtain ⟨t, n, p', f, -, -, -, hm⟩ := FooteLit.oddLieType_of_classical_twoComponent hCI hnonab hu
    hJ.1 ((isTwoComponentIn_iff hJ.1).mp hJ) huJ hrank
  exact hcat (Blueprint.lieModel_catalog G t n p' f hm)

end CFSG.ComponentClassification.HarrisLit.T1
