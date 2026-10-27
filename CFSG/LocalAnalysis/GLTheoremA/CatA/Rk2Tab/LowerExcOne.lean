module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
public import CFSG.RankThree.PartTwo.Census.Exceptional.Geck
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Arith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Arith
public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.RankThree.GroupTheory.SteinbergBYHighTwoRankCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartTwo.Census.Exceptional CFSG.LieType.Chevalley
open CFSG.RankThree.CentralCover
open scoped MatrixGroups

theorem le_evenRank_of_mulEquiv_center_quotient {K G : Type} [Group K] [Finite K] [Group G]
    [Finite G] (e : (K ⧸ Subgroup.center K) ≃* G) (hZ : Subgroup.center K = ⊥) {k : ℕ}
    (h : k ≤ CFSG.twoLocalOddRank G) : k ≤ evenRank K := by
  have hKZ : k ≤ CFSG.twoLocalOddRank (K ⧸ Subgroup.center K) := by
    rwa [CFSG.RankThree.PartOne.Census3.twoLocalOddRank_eq_of_mulEquiv e]
  have hKK : k ≤ CFSG.twoLocalOddRank K := by
    have qe : (K ⧸ Subgroup.center K) ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    rwa [CFSG.RankThree.PartOne.Census3.twoLocalOddRank_eq_of_mulEquiv qe] at hKZ
  rwa [CFSG.RankThree.GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank] at hKK

theorem le_twoLocalPrimeRank_three_of_commuting_SL2_charTwo {G : Type} [Group G] [Finite G]
    {K : Type} [Field K] (h2 : ringChar K = 2) {k : ℕ}
    (φ : Fin (k + 1) → SL(2, K) →* G) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, K), φ i A * φ j B = φ j B * φ i A) :
    k ≤ CFSG.Open.twoLocalPrimeRank 3 G := by
  have hu : orderOf (φ (Fin.last k) (sl2Upper 1)) = 2 := by
    rw [orderOf_injective (φ (Fin.last k)) (hφ _)]
    exact orderOf_sl2Upper_one h2
  have hmain := card_le_localRank_three_of_commuting_SL2 (ι := Fin k)
    (φ := fun i => φ i.castSucc) (fun i => hφ _)
    (fun i j hij A B => hcomm _ _ (fun h => hij (Fin.castSucc_injective k h)) A B) hu
    (fun i A => hcomm _ _ (Fin.castSucc_ne_last i) A _)
  rw [Fintype.card_fin] at hmain
  exact hmain

private theorem dvd_card_of_pos_twoLocalRank (G : Type*) [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (h : 0 < CFSG.Open.twoLocalPrimeRank p G) : p ∣ Nat.card G := by
  obtain ⟨H, -, hpR⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_attained p hp G h
  obtain ⟨E, hEH, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  have hpos : 0 < CFSG.Open.pRank p H := by rw [hpR]; exact h
  have h1 : p ∣ Nat.card E := by
    rw [hEcard]
    exact dvd_pow_self p hpos.ne'
  exact h1.trans ((Subgroup.card_dvd_of_le hEH).trans (Subgroup.card_subgroup_dvd_card H))

def e7OrthogonalRoots : Fin 7 → Fin 7 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0], ![1, 1, 1, 2, 1, 0, 0],
    ![1, 2, 3, 4, 3, 2, 1], ![0, 1, 0, 0, 0, 0, 0], ![1, 1, 1, 2, 2, 2, 1],
    ![1, 0, 1, 0, 0, 0, 0]]

def e8OrthogonalRoots : Fin 8 → Fin 8 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0],
    ![1, 2, 2, 4, 4, 3, 2, 1], ![2, 2, 4, 5, 4, 3, 2, 1], ![1, 2, 2, 3, 2, 2, 2, 1],
    ![1, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 3, 2, 1, 0, 0]]

theorem six_le_twoLocalPrimeRank_adjointGroup_E7 (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2) : 6 ≤ CFSG.Open.twoLocalPrimeRank 3 (adjointGroup Tag.E7 F) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite (adjointGroup Tag.E7 F) :=
    CFSG.LieType.Chevalley.generated_group_finite Tag.E7 F
  have h2 : ringChar F = 2 :=
    (FiniteField.even_card_iff_char_two (F := F)).2 (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨ι, hι, hcomm⟩ := exists_commuting_rootSL2 (K := F) Tag.E7 e7OrthogonalRoots
    (by decide +kernel)
  exact le_twoLocalPrimeRank_three_of_commuting_SL2_charTwo h2 ι hι hcomm

theorem six_le_twoLocalOddRank_adjointGroup_E7 (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2) : 6 ≤ CFSG.twoLocalOddRank (adjointGroup Tag.E7 F) := by
  have h6 := six_le_twoLocalPrimeRank_adjointGroup_E7 F hF
  have h3 : 3 ∣ Nat.card (adjointGroup Tag.E7 F) :=
    dvd_card_of_pos_twoLocalRank _ Nat.prime_three (by omega)
  exact h6.trans
    (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank Nat.prime_three (by norm_num) h3)

theorem seven_le_twoLocalPrimeRank_adjointGroup_E8 (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2) : 7 ≤ CFSG.Open.twoLocalPrimeRank 3 (adjointGroup Tag.E8 F) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite (adjointGroup Tag.E8 F) :=
    CFSG.LieType.Chevalley.generated_group_finite Tag.E8 F
  have h2 : ringChar F = 2 :=
    (FiniteField.even_card_iff_char_two (F := F)).2 (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨ι, hι, hcomm⟩ := exists_commuting_rootSL2 (K := F) Tag.E8 e8OrthogonalRoots
    (by decide +kernel)
  exact le_twoLocalPrimeRank_three_of_commuting_SL2_charTwo h2 ι hι hcomm

theorem seven_le_twoLocalOddRank_adjointGroup_E8 (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2) : 7 ≤ CFSG.twoLocalOddRank (adjointGroup Tag.E8 F) := by
  have h7 := seven_le_twoLocalPrimeRank_adjointGroup_E8 F hF
  have h3 : 3 ∣ Nat.card (adjointGroup Tag.E8 F) :=
    dvd_card_of_pos_twoLocalRank _ Nat.prime_three (by omega)
  exact h7.trans
    (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank Nat.prime_three (by norm_num) h3)

theorem rk2_low_e7_one (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E7) (hn : lab.n = 1) :
    6 ≤ evenRank K := by
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E7 0 2 lab.n :=
    lieModel_of_markedModel_E7 htag hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨e⟩⟩ := hM'.chevalleyExceptionalModel
    (by decide : StatedLieTag.E7 ∈ chevalleyExceptionalTags)
  haveI : Finite F := hFin
  haveI : Finite (adjointGroup Tag.E7 F) :=
    CFSG.LieType.Chevalley.generated_group_finite Tag.E7 F
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.center_eq_bot_of_E7 hQ'
      (by omega) hFcard e
  have htwo : Nat.card F = 2 := by rw [hFcard, hn, pow_one]
  have hAdj : AdjointQuotient .E7 F ≃* adjointGroup Tag.E7 F :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := Tag.E7) (K := F))).trans
      QuotientGroup.quotientBot
  exact le_evenRank_of_mulEquiv_center_quotient (e.trans hAdj) hZ
    (six_le_twoLocalOddRank_adjointGroup_E7 F htwo)

theorem rk2_low_e8_one (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E8) (hn : lab.n = 1) :
    7 ≤ evenRank K := by
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E8 0 2 lab.n :=
    lieModel_of_markedModel_E8 htag hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨e⟩⟩ := hM'.chevalleyExceptionalModel
    (by decide : StatedLieTag.E8 ∈ chevalleyExceptionalTags)
  haveI : Finite F := hFin
  haveI : Finite (adjointGroup Tag.E8 F) :=
    CFSG.LieType.Chevalley.generated_group_finite Tag.E8 F
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.center_eq_bot_of_E8 hQ'
      (by omega) hFcard e
  have htwo : Nat.card F = 2 := by rw [hFcard, hn, pow_one]
  have hAdj : AdjointQuotient .E8 F ≃* adjointGroup Tag.E8 F :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := Tag.E8) (K := F))).trans
      QuotientGroup.quotientBot
  exact le_evenRank_of_mulEquiv_center_quotient (e.trans hAdj) hZ
    (seven_le_twoLocalOddRank_adjointGroup_E8 F htwo)

end CFSG.LocalAnalysis.GLTheoremA
