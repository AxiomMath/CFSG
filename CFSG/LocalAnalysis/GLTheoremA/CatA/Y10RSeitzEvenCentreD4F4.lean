module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzEvenCentreLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerOrthOne
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerExcOne
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrder
public import CFSG.LieType.Steinberg.CentralExt.GriessFFourTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Chevalley CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.Census.Exceptional

theorem noncentralWitness_of_le_twoLocalPrimeRank {K R : Type} [Group K] [Finite K] [Group R]
    [Finite R] (θ : K ⧸ Subgroup.center K ≃* R) {q k : ℕ} (hq : q.Prime)
    (hqZ : ¬ q ∣ Nat.card (Subgroup.center K)) (hk0 : 1 ≤ k)
    (hk : k ≤ CFSG.Open.twoLocalPrimeRank q R) : NoncentralWitness K q k := by
  classical
  have hpos : 0 < CFSG.Open.twoLocalPrimeRank q R := lt_of_lt_of_le (by omega) hk
  have hpos' : 0 < CFSG.RankThreeEvenClassification.Helpers.twoLocalRank q R := hpos
  obtain ⟨H, hHloc, hHrank⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_attained q hq R hpos'
  obtain ⟨P, hPne, hP2, hH⟩ := hHloc
  have hkH : k ≤ CFSG.Open.pRank q H := by
    rw [hHrank]
    exact hk
  subst hH
  obtain ⟨E, hEH, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank hq.one_lt (Subgroup.normalizer (P : Set R))
  have hdvd : q ^ k ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow q hkH
  obtain ⟨E', hE'card, -, hE'E⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hq (H := ⊥) (L := E) (n := k) (by simp) hdvd bot_le
  exact noncentralWitness_of_center_quotient θ hq hqZ hPne hP2
    (isElemAbelian_mono hE hE'E) hE'card (hE'E.trans hEH)


theorem seitzEvenCentre_D4 {K : Type} [Group K] [Finite K]
    (hK : Rk2IsLabel K ⟨.D, 4, 1⟩) : NoncentralWitness K 3 3 := by
  classical
  obtain ⟨hQ, -, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaPlus 4 2 1 := hM
  obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  letI : Field F := hfield
  letI : Finite F := hfinite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hcard2 : Nat.card F = 2 := by rw [hcard]; norm_num
  have hcard' : Fintype.card F = 2 ^ 1 := by
    rw [← Nat.card_eq_fintype_card]; exact hcard2
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hv : ∃ v : Fin 4 ⊕ Fin 4 → F, quadPlus 4 F v ≠ 0 := by
    let i0 : Fin 4 := ⟨0, by omega⟩
    let v : Fin 4 ⊕ Fin 4 → F :=
      Pi.single (Sum.inl i0) (1 : F) + Pi.single (Sum.inr i0) (1 : F)
    refine ⟨v, ?_⟩
    rw [quadPlus_apply]
    have hv1 : v (Sum.inl i0) = 1 := by simp [v]
    have hv2 : v (Sum.inr i0) = 1 := by simp [v]
    have hterm : ∀ i : Fin 4, v (Sum.inl i) * v (Sum.inr i) = if i = i0 then 1 else 0 := by
      intro i
      by_cases hi : i = i0
      · subst hi; rw [hv1, hv2, if_pos rfl, one_mul]
      · rw [if_neg hi]
        have h1 : v (Sum.inl i) = 0 := by simp [v, hi]
        rw [h1, zero_mul]
    simp only [hterm]
    rw [Finset.sum_ite_eq']
    simp
  have hbot : (StatedScalars (Fin 4 ⊕ Fin 4) F).subgroupOf
      (StatedOmega (StatedQuadPlus 4 F)) = ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadPlus 4 F) (Q₀ := StatedQuadPlus 4 F) (coe_quadPlus 4 F) hv
  let φ₁ : StatedProj (StatedOmega (StatedQuadPlus 4 F)) ≃*
      StatedOmega (StatedQuadPlus 4 F) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot)
  let φ₂ : StatedOmega (StatedQuadPlus 4 F) ≃*
      orthElementaryGroup (quadPlus 4 F) :=
    CFSG.ClassicalGroups.Orthogonal.statedOmegaEquiv (coe_quadPlus 4 F)
      (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus (by omega))
  have hQ' : CFSG.Open.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.1 hQ
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.noThreeCover_omegaPlus_four
      F K hQ' ⟨e⟩
  obtain ⟨E, U, hE, hEcard, hU, hU2, hEU⟩ :=
    quadPlusWitness (F := F) (m := 4) (by norm_num)
  have hEcard' : Nat.card E = 3 ^ 3 := by simpa using hEcard
  exact noncentralWitness_of_center_quotient (e.trans (φ₁.trans φ₂))
    Nat.prime_three hZ hU hU2 hE hEcard' hEU

private def f4FourOrthogonalRoots : Fin 4 → Fin CFSG.Blueprint.Chevalley.Tag.F4.rank → ℤ :=
  ![![0, 1, 0, 0], ![0, 1, 2, 0], ![0, 1, 2, 2], ![2, 3, 4, 2]]

theorem three_le_twoLocalPrimeRank_adjointGroup_F4 (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2) : 3 ≤ CFSG.Open.twoLocalPrimeRank 3 (adjointGroup Tag.F4 F) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite (adjointGroup Tag.F4 F) :=
    CFSG.LieType.Chevalley.generated_group_finite Tag.F4 F
  have h2 : ringChar F = 2 :=
    (FiniteField.even_card_iff_char_two (F := F)).2 (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨ι, hι, hcomm⟩ :=
    exists_commuting_rootSL2 (K := F) Tag.F4 f4FourOrthogonalRoots (by decide +kernel)
  exact le_twoLocalPrimeRank_three_of_commuting_SL2_charTwo h2 ι hι hcomm

theorem seitzEvenCentre_F4 {K : Type} [Group K] [Finite K]
    (hK : Rk2IsLabel K ⟨.F4, 0, 1⟩) : NoncentralWitness K 3 3 := by
  classical
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .F4 0 2 1 :=
    lieModel_of_markedModel_F4 rfl hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel
      (by decide : StatedLieTag.F4 ∈ CFSG.Blueprint.chevalleyExceptionalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  have htwo : Nat.card F = 2 := by rw [hFcard]; norm_num
  haveI : Finite (adjointGroup Tag.F4 F) :=
    CFSG.LieType.Chevalley.generated_group_finite Tag.F4 F
  let θ : K ⧸ Subgroup.center K ≃* adjointGroup Tag.F4 F :=
    φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .F4 F)
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hMcard : Nat.card (CFSG.Open.griessHopfMultiplier
      (CFSG.Blueprint.AdjointQuotient .F4 F)) = 2 :=
    (CFSG.LieType.Steinberg.CentralExt.GriessExceptional.f4_two_card_griessHopfMultiplier
      htwo).2
  have hdvd : Nat.card (Subgroup.center K) ∣
      Nat.card (CFSG.Open.griessHopfMultiplier (CFSG.Blueprint.AdjointQuotient .F4 F)) :=
    CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_hopf hQ' φ
  rw [hMcard] at hdvd
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) := fun h3 =>
    absurd (h3.trans hdvd) (by norm_num)
  exact noncentralWitness_of_le_twoLocalPrimeRank θ Nat.prime_three hZ (by norm_num)
    (three_le_twoLocalPrimeRank_adjointGroup_F4 F htwo)


end CFSG.LocalAnalysis.GLTheoremA.Y10F
