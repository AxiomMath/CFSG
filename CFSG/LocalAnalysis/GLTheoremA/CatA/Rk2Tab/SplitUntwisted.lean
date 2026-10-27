module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.PRankSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.CentralLift
public import CFSG.LieType.Steinberg.Adjoint.Torus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerExcOne
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLiftLocal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerOrthOne
public import CFSG.Open.StatedDefs
public import CFSG.LieType.Steinberg.CentralExt.GriessOmegaEightTwo
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.LocalAnalysis.GL83PartI.I713.Chain
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open scoped MatrixGroups
open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal.Spin CFSG.Blueprint.Chevalley CFSG.Blueprint.Multiplier CFSG.LieType.Chevalley CFSG.StandardType CFSG.SignalizerFunctorTheorem.NonLocal


theorem rk2_split_low_E7 {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .E7) (hpq : p ∣ 2 ^ lab.n - 1) :
    6 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag
  subst htag
  obtain ⟨hQ, hl, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E7 0 2 n :=
    lieModel_of_markedModel_E7 rfl hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E7 ∈ CFSG.Blueprint.chevalleyExceptionalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hn1 : 1 ≤ n := hl.1
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hFcard
  have hpq' : p ∣ Nat.card F - 1 := by rw [hFcard]; exact hpq
  have hcard : Nat.card (TableBExc.torusPow .E7 F p) = p ^ 7 :=
    TableBExc.card_torusPow_E7 hp hpq'
  have hV : TableBExc.torusPow .E7 F p ≤
      (torusGroup .E7 F).subgroupOf (adjointGroup .E7 F) :=
    fun g hg => Subgroup.mem_subgroupOf.mpr ((TableBExc.mem_torusPow.mp hg).1)
  have hVp : ∀ g ∈ TableBExc.torusPow .E7 F p, g ^ p = 1 :=
    fun g hg => (TableBExc.mem_torusPow.mp hg).2
  obtain ⟨E, X, hX, hX2, hE, hEcard, hXE⟩ :=
    exists_elemAbelian_le_normalizer_rootSubgroup (p := p) hV hVp
      (isRoot_single .E7 0)
  have hEcard' : Nat.card E = p ^ 7 := hEcard.trans hcard
  let θ : K ⧸ Subgroup.center K ≃* adjointGroup .E7 F :=
    φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E7 F)
  have hz : Subgroup.center K = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.center_eq_bot_of_E7
      hQ' hn1 hFcard φ
  have hZ : ¬ p ∣ Nat.card (Subgroup.center K) := by
    rw [hz, Subgroup.card_bot]
    exact fun h => hp.ne_one (Nat.dvd_one.1 h)
  have hbound : 7 ≤ CFSG.Open.twoLocalPrimeRank p K :=
    le_twoLocalPrimeRank_of_center_quotient θ hp hp2 hZ hX hX2 hE hEcard' hXE
  have hz0 : CFSG.Open.pRank p (Subgroup.center K) = 0 :=
    pRank_eq_zero_of_not_dvd_card hp hZ
  rw [hz0]
  omega

theorem rk2_split_low_E8 {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .E8) (hpq : p ∣ 2 ^ lab.n - 1) :
    7 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag
  subst htag
  obtain ⟨hQ, hl, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E8 0 2 n :=
    lieModel_of_markedModel_E8 rfl hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E8 ∈ CFSG.Blueprint.chevalleyExceptionalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hn1 : 1 ≤ n := hl.1
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hFcard
  have hpq' : p ∣ Nat.card F - 1 := by rw [hFcard]; exact hpq
  have hcard : Nat.card (TableBExc.torusPow .E8 F p) = p ^ 8 :=
    TableBExc.card_torusPow_E8 hp hpq'
  have hV : TableBExc.torusPow .E8 F p ≤
      (torusGroup .E8 F).subgroupOf (adjointGroup .E8 F) :=
    fun g hg => Subgroup.mem_subgroupOf.mpr ((TableBExc.mem_torusPow.mp hg).1)
  have hVp : ∀ g ∈ TableBExc.torusPow .E8 F p, g ^ p = 1 :=
    fun g hg => (TableBExc.mem_torusPow.mp hg).2
  obtain ⟨E, X, hX, hX2, hE, hEcard, hXE⟩ :=
    exists_elemAbelian_le_normalizer_rootSubgroup (p := p) hV hVp
      (isRoot_single .E8 0)
  have hEcard' : Nat.card E = p ^ 8 := hEcard.trans hcard
  let θ : K ⧸ Subgroup.center K ≃* adjointGroup .E8 F :=
    φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E8 F)
  have hz : Subgroup.center K = ⊥ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.center_eq_bot_of_E8
      hQ' hn1 hFcard φ
  have hZ : ¬ p ∣ Nat.card (Subgroup.center K) := by
    rw [hz, Subgroup.card_bot]
    exact fun h => hp.ne_one (Nat.dvd_one.1 h)
  have hbound : 8 ≤ CFSG.Open.twoLocalPrimeRank p K :=
    le_twoLocalPrimeRank_of_center_quotient θ hp hp2 hZ hX hX2 hE hEcard' hXE
  have hz0 : CFSG.Open.pRank p (Subgroup.center K) = 0 :=
    pRank_eq_zero_of_not_dvd_card hp hZ
  rw [hz0]
  omega

theorem rk2_split_low_BC {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .B ∨ lab.tag = .C) (hpq : p ∣ 2 ^ lab.n - 1) :
    lab.rank - 1 + CFSG.Open.pRank p (Subgroup.center K) ≤
      CFSG.Open.twoLocalPrimeRank p K := by
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have ht : markTag lab = .PSp := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markTag, hB]
    · simp [CFSG.StandardType.markTag, hC]
  have hrk : markRank lab = lab.rank := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markRank, hB]
    · simp [CFSG.StandardType.markRank, hC]
  have hch : markChar lab = 2 := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markChar, hB]
    · simp [CFSG.StandardType.markChar, hC]
  have hdg : markDeg lab = lab.n := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markDeg, hB]
    · simp [CFSG.StandardType.markDeg, hC]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hrk, hch, hdg] at hM'
  obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  letI : Field F := hfield
  letI : Finite F := hfinite
  have hcard' : Fintype.card F = 2 ^ lab.n := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hn : 2 ≤ lab.n := by
    rcases Nat.lt_or_ge lab.n 2 with h2 | h2
    · have hn1 : lab.n = 1 := by
        have := hlab.1; omega
      rw [hn1] at hpq
      norm_num at hpq
      exact absurd hpq hp.ne_one
    · exact h2
  have hrdvd : p ∣ Nat.card F - 1 := by rw [hcard]; exact hpq
  have hℓ : 1 ≤ lab.rank := by
    rcases htag with hB | hC
    · have h := hlab; simp only [CFSG.Assembly.LargeEvenInLambda2, hB] at h
      exact le_trans (by norm_num) h.2.1
    · have h := hlab; simp only [CFSG.Assembly.LargeEvenInLambda2, hC] at h
      exact le_trans (by norm_num) h.2.1
  obtain ⟨E, hE, hEcard, hEnorm⟩ :=
    exists_isElemAbelian_torus_statedSp (F := F) (ℓ := lab.rank) (r := p) hℓ hp hp2 hrdvd
  have hbot : (StatedScalars (Fin lab.rank ⊕ Fin lab.rank) F).subgroupOf
      (StatedSp lab.rank F) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot
  let φ : StatedProj (StatedSp lab.rank F) ≃* StatedSp lab.rank F :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot)
  have hZ : ¬ p ∣ Nat.card (Subgroup.center K) := by
    intro hdiv
    have hdvdZ : Nat.card (Subgroup.center K) ∣
        Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
      _root_.CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_hopf hQ
        (MulEquiv.refl _)
    have hSC : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) .PSp lab.rank 2 lab.n :=
      hM'.statedClassicalModel (by decide)
    have h4 : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) ∣ 4 :=
      card_griess_psp_dvd_four hSC hn
    have h24 : p ∣ 4 := hdiv.trans (hdvdZ.trans h4)
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h24))
    exact hp2 this
  have hbound : lab.rank ≤ CFSG.Open.twoLocalPrimeRank p K :=
    le_twoLocalPrimeRank_of_center_quotient (e.trans φ) hp hp2 hZ
      (spSiegel_ne_bot hℓ) (isPGroup_spSiegel (F := F) lab.rank)
      hE hEcard hEnorm
  have hz0 : CFSG.Open.pRank p (Subgroup.center K) = 0 :=
    pRank_eq_zero_of_not_dvd_card hp hZ
  rw [hz0]
  omega


open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal
open CFSG.Assembly.RankThreeEven (localRank)

theorem rk2_split_low_D_three {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .D) (hrank : lab.rank = 3) (hpq : p ∣ 2 ^ lab.n - 1) :
    lab.rank - 1 + CFSG.Open.pRank p (Subgroup.center K) ≤
      CFSG.Open.twoLocalPrimeRank p K := by
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have hn1 : 1 ≤ lab.n := hlab.1
  have hn : 2 ≤ lab.n := by
    rcases Nat.lt_or_ge lab.n 2 with h2 | h2
    · have hn1' : lab.n = 1 := by omega
      rw [hn1'] at hpq
      norm_num at hpq
      exact absurd hpq hp.ne_one
    · exact h2
  obtain ⟨F, hF, hFin, hcardF, ⟨e₀⟩⟩ :=
    exists_model_psl_of_isLabel hM (d := 4) (n := lab.n)
      (by simp [CFSG.StandardType.markTag, htag, hrank])
      (by simp [CFSG.StandardType.markRank, htag, hrank])
      (by simp [CFSG.StandardType.markChar, htag])
      (by simp [CFSG.StandardType.markDeg, htag])
  letI : Field F := hF
  letI : Finite F := hFin
  letI : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = 2 ^ lab.n := by
    rw [← Nat.card_eq_fintype_card]; exact hcardF
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hq : 4 ≤ Fintype.card F := by
    have h4 : 4 ≤ Nat.card F := by
      rw [hcardF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn
    rw [Fintype.card_eq_nat_card]; omega
  have hodd : Odd (Fintype.card F - 1) := by
    rw [Fintype.card_eq_nat_card, hcardF]
    have hle : 1 ≤ 2 ^ lab.n := Nat.one_le_pow _ _ (by norm_num)
    have hev : Even (2 ^ lab.n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    exact Nat.Even.sub_odd hle hev odd_one
  have hZ : ¬ p ∣ Nat.card (Subgroup.center K) := by
    intro hdiv
    have hmult' : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (StatedProj (StatedSL 4 F))) = Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F)) :=
      card_hopfMultiplier_statedProj_eq_center (F := F) (d := 4) (by norm_num) hq (by norm_num)
    have hdvd := card_center_dvd_center_specialLinearGroup hQ e₀ hmult'
    rw [card_center_specialLinearGroup_eq_gcd (F := F) (d := 4) (by norm_num)] at hdvd
    have hg1 : Nat.gcd 4 (Fintype.card F - 1) = 1 := by
      have hcop : Nat.Coprime 4 (Fintype.card F - 1) := by
        have h := (Nat.coprime_two_left.mpr hodd).pow_left 2
        simpa using h
      exact Nat.coprime_iff_gcd_eq_one.mp hcop
    rw [hg1] at hdvd
    exact hp.not_dvd_one (hdiv.trans hdvd)
  have hrdvd : p ∣ Nat.card F - 1 := by rw [hcardF]; exact hpq
  obtain ⟨E, X, hX, hX2, hE, hEcard, hEX⟩ :=
    exists_elemAbelian_le_normalizer_statedProj (F := F) 2 p hp hp2 hrdvd
  have hbound : 2 ≤ CFSG.Open.twoLocalPrimeRank p K :=
    le_twoLocalPrimeRank_of_center_quotient e₀ hp hp2 hZ hX hX2 hE hEcard hEX
  have hz0 : CFSG.Open.pRank p (Subgroup.center K) = 0 :=
    pRank_eq_zero_of_not_dvd_card hp hZ
  rw [hrank, hz0]
  omega

theorem rk2_split_low_D_ge_four {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .D) (hℓ4 : 4 ≤ lab.rank) (hpq : p ∣ 2 ^ lab.n - 1) :
    lab.rank - 1 + CFSG.Open.pRank p (Subgroup.center K) ≤
      CFSG.Open.twoLocalPrimeRank p K := by
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have htag3 : lab.rank ≠ 3 := by omega
  have ht : markTag lab = .POmegaPlus := by
    simp [CFSG.StandardType.markTag, htag, if_neg htag3]
  have hrk : markRank lab = lab.rank := by
    simp [CFSG.StandardType.markRank, htag, if_neg htag3]
  have hch : markChar lab = 2 := by simp [CFSG.StandardType.markChar, htag]
  have hdg : markDeg lab = lab.n := by simp [CFSG.StandardType.markDeg, htag]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hrk, hch, hdg] at hM'
  obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  letI : Field F := hfield
  letI : Finite F := hfinite
  have hcard' : Fintype.card F = 2 ^ lab.n := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hn : 2 ≤ lab.n := by
    rcases Nat.lt_or_ge lab.n 2 with h2 | h2
    · have hn1 : lab.n = 1 := by
        have := hlab.1; omega
      rw [hn1] at hpq
      norm_num at hpq
      exact absurd hpq hp.ne_one
    · exact h2
  have hrdvd : p ∣ Nat.card F - 1 := by rw [hcard]; exact hpq
  have hv : ∃ v : Fin lab.rank ⊕ Fin lab.rank → F, quadPlus lab.rank F v ≠ 0 := by
    let i0 : Fin lab.rank := ⟨0, by omega⟩
    let v : Fin lab.rank ⊕ Fin lab.rank → F :=
      Pi.single (Sum.inl i0) (1 : F) + Pi.single (Sum.inr i0) (1 : F)
    refine ⟨v, ?_⟩
    rw [quadPlus_apply]
    have hv1 : v (Sum.inl i0) = 1 := by simp [v]
    have hv2 : v (Sum.inr i0) = 1 := by simp [v]
    have hterm : ∀ i : Fin lab.rank, v (Sum.inl i) * v (Sum.inr i) =
        if i = i0 then 1 else 0 := by
      intro i
      by_cases hi : i = i0
      · subst hi; rw [hv1, hv2, if_pos rfl, one_mul]
      · rw [if_neg hi]
        have h1 : v (Sum.inl i) = 0 := by simp [v, hi]
        rw [h1, zero_mul]
    simp only [hterm]
    rw [Finset.sum_ite_eq']
    simp
  have hbot : (StatedScalars (Fin lab.rank ⊕ Fin lab.rank) F).subgroupOf
      (StatedOmega (StatedQuadPlus lab.rank F)) = ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadPlus lab.rank F) (Q₀ := StatedQuadPlus lab.rank F) (coe_quadPlus lab.rank F) hv
  let φ₁ : StatedProj (StatedOmega (StatedQuadPlus lab.rank F)) ≃*
      StatedOmega (StatedQuadPlus lab.rank F) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot)
  let φ₂ : StatedOmega (StatedQuadPlus lab.rank F) ≃*
      orthElementaryGroup (quadPlus lab.rank F) :=
    CFSG.ClassicalGroups.Orthogonal.statedOmegaEquiv (coe_quadPlus lab.rank F)
      (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus (by omega))
  have hZ : ¬ p ∣ Nat.card (Subgroup.center K) := by
    intro hdiv
    have hdvdZ : Nat.card (Subgroup.center K) ∣
        Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
      _root_.CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_hopf hQ
        (MulEquiv.refl _)
    have hSC : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaPlus lab.rank 2 lab.n :=
      hM'.statedClassicalModel (by decide)
    have h4 : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) ∣ 4 :=
      card_griess_pomegaPlus_dvd_four hSC (Or.inl hn)
    have h24 : p ∣ 4 := hdiv.trans (hdvdZ.trans h4)
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h24))
    exact hp2 this
  obtain ⟨E, hE, hEcard, hEnorm⟩ :=
    exists_isElemAbelian_torus_quadPlus (F := F) (ℓ := lab.rank) (r := p)
      (by omega) hp hp2 hrdvd
  have hbound : lab.rank ≤ CFSG.Open.twoLocalPrimeRank p K :=
    le_twoLocalPrimeRank_of_center_quotient (e.trans (φ₁.trans φ₂)) hp hp2 hZ
      (posUnip_subgroupOf_nontrivial_isPGroup (ℓ := lab.rank) (by omega)).1
      (posUnip_subgroupOf_nontrivial_isPGroup (ℓ := lab.rank) (by omega)).2
      hE hEcard hEnorm
  have hz0 : CFSG.Open.pRank p (Subgroup.center K) = 0 :=
    pRank_eq_zero_of_not_dvd_card hp hZ
  rw [hz0]
  omega

theorem rk2_split_low_BCD {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D) (hpq : p ∣ 2 ^ lab.n - 1) :
    lab.rank - 1 + CFSG.Open.pRank p (Subgroup.center K) ≤
      CFSG.Open.twoLocalPrimeRank p K := by
  rcases htag with hB | hC | hD
  · exact rk2_split_low_BC hK hp hp2 (Or.inl hB) hpq
  · exact rk2_split_low_BC hK hp hp2 (Or.inr hC) hpq
  · have h3le : 3 ≤ lab.rank := by
      have h := (quasisimple_markedModel_of_isLabel hK).2.1
      simp only [CFSG.Assembly.LargeEvenInLambda2, hD] at h
      exact h.2
    rcases Nat.lt_or_ge lab.rank 4 with hlt | hge
    · have h3 : lab.rank = 3 := by omega
      exact rk2_split_low_D_three hK hp hp2 hD h3 hpq
    · exact rk2_split_low_D_ge_four hK hp hp2 hD hge hpq


theorem rk2_split_low_A_one {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .A) (hn : lab.n = 1) :
    (lab.rank + 1) / 2 + CFSG.Open.pRank 3 (Subgroup.center K) ≤
      CFSG.Open.twoLocalPrimeRank 3 K := by
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have hlab' := hlab
  simp only [CFSG.Assembly.LargeEvenInLambda2, htag] at hlab'
  obtain ⟨-, _, hrankone⟩ := hlab'
  have hrank2 : 2 ≤ lab.rank := by
    by_contra h
    have hr1 : lab.rank = 1 := by omega
    have := hrankone hr1
    omega
  obtain ⟨F, hF, hFin, hcardF, ⟨e₀⟩⟩ :=
    exists_model_psl_of_isLabel hM (d := lab.rank + 1) (n := lab.n)
      (by simp [CFSG.StandardType.markTag, htag])
      (by simp [CFSG.StandardType.markRank, htag])
      (by simp [CFSG.StandardType.markChar, htag])
      (by simp [CFSG.StandardType.markDeg, htag])
  letI : Field F := hF
  letI : Finite F := hFin
  letI : Fintype F := Fintype.ofFinite F
  have hF2 : Nat.card F = 2 := by rw [hcardF, hn]; norm_num
  have hcard' : Fintype.card F = 2 ^ 1 := by
    rw [← Nat.card_eq_fintype_card]; exact hF2
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL (lab.rank + 1) 2 1 := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg, htag, hn] using hM
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) :=
    not_three_dvd_center_of_psl_two_one hQ hM'
  have hz0 : CFSG.Open.pRank 3 (Subgroup.center K) = 0 :=
    pRank_eq_zero_of_not_dvd_card Nat.prime_three hZ
  rw [hz0]
  rw [Nat.add_zero]
  by_cases hrank_two : lab.rank = 2
  · have h3 : lab.rank + 1 = 3 := by omega
    have eP : K ⧸ Subgroup.center K ≃* StatedProj (StatedSL 3 F) := h3 ▸ e₀
    obtain ⟨E, X, hX, hX2, hE, hEcard, hEX⟩ :=
      exists_elemAbelian_le_normalizer_statedProj_three (F := F)
    have hbound : 1 ≤ CFSG.Open.twoLocalPrimeRank 3 K :=
      le_twoLocalPrimeRank_of_center_quotient eP Nat.prime_three (by norm_num) hZ
        hX hX2 hE hEcard hEX
    rw [hrank_two]
    simpa using hbound
  · have hrank3 : 3 ≤ lab.rank := by omega
    set d := lab.rank + 1 with hd_def
    have hd4 : 4 ≤ d := by omega
    obtain ⟨k, m, hk, hm, hkm⟩ : ∃ k m : ℕ, 2 ≤ k ∧ m < 2 ∧ d = 2 * k + m := by
      refine ⟨d / 2, d % 2, ?_, ?_, ?_⟩
      · exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)
      · exact Nat.mod_lt _ (by norm_num)
      · have h := Nat.div_add_mod d 2
        omega
    obtain ⟨E, X, hX, hX2, hE, hEcard, hEX⟩ :=
      exists_elemAbelian_le_normalizer_PSL_of_card (K := F) (n := d) (k := k) (m := m) hkm hk
    let eP : K ⧸ Subgroup.center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin d) F :=
      e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d F).symm
    have hbound : k ≤ CFSG.Open.twoLocalPrimeRank 3 K :=
      le_twoLocalPrimeRank_of_center_quotient eP Nat.prime_three (by norm_num) hZ
        hX hX2 hE hEcard hEX
    have hgoal : (lab.rank + 1) / 2 = k := by
      rw [← hd_def]
      omega
    rwa [hgoal]

theorem rk2_split_low_BC_one {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .B ∨ lab.tag = .C) (hn : lab.n = 1) :
    lab.rank - 1 + CFSG.Open.pRank 3 (Subgroup.center K) ≤
      CFSG.Open.twoLocalPrimeRank 3 K := by
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have ht : markTag lab = .PSp := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markTag, hB]
    · simp [CFSG.StandardType.markTag, hC]
  have hrk : markRank lab = lab.rank := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markRank, hB]
    · simp [CFSG.StandardType.markRank, hC]
  have hch : markChar lab = 2 := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markChar, hB]
    · simp [CFSG.StandardType.markChar, hC]
  have hdg : markDeg lab = lab.n := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markDeg, hB]
    · simp [CFSG.StandardType.markDeg, hC]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hrk, hch, hdg] at hM'
  obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  letI : Field F := hfield
  letI : Finite F := hfinite
  have hcard2 : Nat.card F = 2 := by rw [hcard, hn]; norm_num
  have hcard' : Fintype.card F = 2 ^ 1 := by
    rw [← Nat.card_eq_fintype_card]; exact hcard2
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hℓ2 : 2 ≤ lab.rank := by
    rcases htag with hB | hC
    · have h := hlab; simp only [CFSG.Assembly.LargeEvenInLambda2, hB] at h
      exact h.2.1
    · have h := hlab; simp only [CFSG.Assembly.LargeEvenInLambda2, hC] at h
      exact h.2.1
  have hℓ3 : lab.rank ≠ 2 := by
    rcases htag with hB | hC
    · have h := hlab; simp only [CFSG.Assembly.LargeEvenInLambda2, hB] at h
      intro h2
      have := h.2.2 h2
      omega
    · have h := hlab; simp only [CFSG.Assembly.LargeEvenInLambda2, hC] at h
      intro h2
      have := h.2.2 h2
      omega
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) :=
    not_three_dvd_card_center_psp_q2 hℓ2 hℓ3 hcard2 hQ e
  have hle : lab.rank - 1 ≤ localRank 3 (StatedProj (StatedSp lab.rank F)) := by
    have hm : 1 ≤ lab.rank - 1 := by omega
    have h := CFSG.RankThree.PartOne.KFU.le_localRank_three_statedSp_blocks
      (K := F) (m := lab.rank - 1) hm
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ lab.rank)] at h
  obtain ⟨X, hX2, hX0, E, hEN, hEel, hEcard⟩ :=
    CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank Nat.prime_three
      (by omega : 1 ≤ lab.rank - 1) hle
  have hE : IsElemAbelian 3 E := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hEel
  have hbound : lab.rank - 1 ≤ CFSG.Open.twoLocalPrimeRank 3 K :=
    le_twoLocalPrimeRank_of_center_quotient e Nat.prime_three (by norm_num) hZ
      hX0 hX2 hE hEcard hEN
  have hz0 : CFSG.Open.pRank 3 (Subgroup.center K) = 0 :=
    pRank_eq_zero_of_not_dvd_card Nat.prime_three hZ
  rw [hz0]
  omega


theorem not_three_dvd_center_pomegaPlus_one {X : Type} [Group X] {ℓ : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .POmegaPlus ℓ 2 1) (hℓ : 4 ≤ ℓ) :
    ¬ 3 ∣ Nat.card (CFSG.Open.griessHopfMultiplier X) := by
  intro hdiv
  by_cases h4 : ℓ = 4
  · subst h4
    have hLM : CFSG.Models.LieModel X .POmegaPlus 4 2 1 := ⟨h.1, Or.inl h⟩
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_four_two_row hLM
    have hg : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus 4 2 1 = (1, 1) := by
      simp only [CFSG.Blueprint.Multiplier.genericOrders]
      rw [if_pos (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega)))]
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus 4 2 1 = (2, 2) := by
      decide
    have hMcard : Nat.card (CFSG.Open.griessHopfMultiplier X) = 4 := by
      rw [Nat.card_congr eM.toEquiv,
        _root_.CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg, he]
      norm_num
    rw [hMcard] at hdiv
    omega
  · obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_row h
      (Or.inr (by omega))
    have hg : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus ℓ 2 1 = (1, 1) := by
      simp only [CFSG.Blueprint.Multiplier.genericOrders]
      rw [if_pos (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega)))]
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus ℓ 2 1 = (1, 1) := by
      simp [CFSG.Blueprint.Multiplier.exceptionalOrders, h4]
    have hMcard : Nat.card (CFSG.Open.griessHopfMultiplier X) = 1 := by
      rw [Nat.card_congr eM.toEquiv,
        _root_.CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg, he]
      norm_num
    rw [hMcard] at hdiv
    exact Nat.Prime.not_dvd_one Nat.prime_three hdiv


theorem rk2_split_low_E7_one {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E7) (hn : lab.n = 1) :
    6 + CFSG.Open.pRank 3 (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank 3 K := by
  obtain ⟨hQ, hl, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E7 0 2 lab.n :=
    lieModel_of_markedModel_E7 htag hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E7 ∈ CFSG.Blueprint.chevalleyExceptionalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hn1 : 1 ≤ lab.n := hl.1
  have htwo : Nat.card F = 2 := by rw [hFcard, hn, pow_one]
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 (by rw [hFcard, hn, pow_one])
  have hz : Subgroup.center K = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.center_eq_bot_of_E7
      hQ' hn1 (by rw [hFcard, hn, pow_one]) φ
  let θ : K ⧸ Subgroup.center K ≃* adjointGroup .E7 F :=
    φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E7 F)
  have h6 : 6 ≤ CFSG.Open.twoLocalPrimeRank 3 (adjointGroup Tag.E7 F) :=
    six_le_twoLocalPrimeRank_adjointGroup_E7 F htwo
  obtain ⟨X, hX2, hX0, E, hEN, hEel, hEcard⟩ :=
    CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank Nat.prime_three
      (by norm_num) h6
  have hE : IsElemAbelian 3 E := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hEel
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) := by
    rw [hz, Subgroup.card_bot]
    exact fun h => Nat.Prime.not_dvd_one Nat.prime_three h
  have hbound : 6 ≤ CFSG.Open.twoLocalPrimeRank 3 K :=
    le_twoLocalPrimeRank_of_center_quotient θ Nat.prime_three (by norm_num) hZ
      hX0 hX2 hE hEcard hEN
  have hz0 : CFSG.Open.pRank 3 (Subgroup.center K) = 0 :=
    pRank_eq_zero_of_not_dvd_card Nat.prime_three hZ
  rw [hz0]
  omega

theorem rk2_split_low_E8_one {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E8) (hn : lab.n = 1) :
    7 + CFSG.Open.pRank 3 (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank 3 K := by
  obtain ⟨hQ, hl, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E8 0 2 lab.n :=
    lieModel_of_markedModel_E8 htag hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E8 ∈ CFSG.Blueprint.chevalleyExceptionalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hn1 : 1 ≤ lab.n := hl.1
  have htwo : Nat.card F = 2 := by rw [hFcard, hn, pow_one]
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 (by rw [hFcard, hn, pow_one])
  have hz : Subgroup.center K = ⊥ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.center_eq_bot_of_E8
      hQ' hn1 (by rw [hFcard, hn, pow_one]) φ
  let θ : K ⧸ Subgroup.center K ≃* adjointGroup .E8 F :=
    φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E8 F)
  have h7 : 7 ≤ CFSG.Open.twoLocalPrimeRank 3 (adjointGroup Tag.E8 F) :=
    seven_le_twoLocalPrimeRank_adjointGroup_E8 F htwo
  obtain ⟨X, hX2, hX0, E, hEN, hEel, hEcard⟩ :=
    CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank Nat.prime_three
      (by norm_num) h7
  have hE : IsElemAbelian 3 E := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hEel
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) := by
    rw [hz, Subgroup.card_bot]
    exact fun h => Nat.Prime.not_dvd_one Nat.prime_three h
  have hbound : 7 ≤ CFSG.Open.twoLocalPrimeRank 3 K :=
    le_twoLocalPrimeRank_of_center_quotient θ Nat.prime_three (by norm_num) hZ
      hX0 hX2 hE hEcard hEN
  have hz0 : CFSG.Open.pRank 3 (Subgroup.center K) = 0 :=
    pRank_eq_zero_of_not_dvd_card Nat.prime_three hZ
  rw [hz0]
  omega


theorem rk2_split_low_D_one {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .D) (hn : lab.n = 1) (hℓ4 : 4 ≤ lab.rank) :
    lab.rank - 1 + CFSG.Open.pRank 3 (Subgroup.center K) ≤
      CFSG.Open.twoLocalPrimeRank 3 K := by
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have htag3 : lab.rank ≠ 3 := by omega
  have ht : markTag lab = .POmegaPlus := by
    simp [CFSG.StandardType.markTag, htag, if_neg htag3]
  have hrk : markRank lab = lab.rank := by
    simp [CFSG.StandardType.markRank, htag, if_neg htag3]
  have hch : markChar lab = 2 := by simp [CFSG.StandardType.markChar, htag]
  have hdg : markDeg lab = lab.n := by simp [CFSG.StandardType.markDeg, htag]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hrk, hch, hdg] at hM'
  obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  letI : Field F := hfield
  letI : Finite F := hfinite
  have hcard2 : Nat.card F = 2 := by rw [hcard, hn]; norm_num
  have hcard' : Fintype.card F = 2 ^ 1 := by
    rw [← Nat.card_eq_fintype_card]; exact hcard2
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hv : ∃ v : Fin lab.rank ⊕ Fin lab.rank → F, quadPlus lab.rank F v ≠ 0 := by
    let i0 : Fin lab.rank := ⟨0, by omega⟩
    let v : Fin lab.rank ⊕ Fin lab.rank → F :=
      Pi.single (Sum.inl i0) (1 : F) + Pi.single (Sum.inr i0) (1 : F)
    refine ⟨v, ?_⟩
    rw [quadPlus_apply]
    have hv1 : v (Sum.inl i0) = 1 := by simp [v]
    have hv2 : v (Sum.inr i0) = 1 := by simp [v]
    have hterm : ∀ i : Fin lab.rank, v (Sum.inl i) * v (Sum.inr i) =
        if i = i0 then 1 else 0 := by
      intro i
      by_cases hi : i = i0
      · subst hi; rw [hv1, hv2, if_pos rfl, one_mul]
      · rw [if_neg hi]
        have h1 : v (Sum.inl i) = 0 := by simp [v, hi]
        rw [h1, zero_mul]
    simp only [hterm]
    rw [Finset.sum_ite_eq']
    simp
  have hbot : (StatedScalars (Fin lab.rank ⊕ Fin lab.rank) F).subgroupOf
      (StatedOmega (StatedQuadPlus lab.rank F)) = ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadPlus lab.rank F) (Q₀ := StatedQuadPlus lab.rank F) (coe_quadPlus lab.rank F) hv
  let φ₁ : StatedProj (StatedOmega (StatedQuadPlus lab.rank F)) ≃*
      StatedOmega (StatedQuadPlus lab.rank F) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot)
  let φ₂ : StatedOmega (StatedQuadPlus lab.rank F) ≃*
      orthElementaryGroup (quadPlus lab.rank F) :=
    CFSG.ClassicalGroups.Orthogonal.statedOmegaEquiv (coe_quadPlus lab.rank F)
      (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus (by omega))
  have hSC : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaPlus lab.rank 2 1 := by
    simpa [hn] using hM'.statedClassicalModel (by decide)
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) := by
    intro hdiv
    have hdvdZ : Nat.card (Subgroup.center K) ∣
        Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
      _root_.CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_hopf hQ
        (MulEquiv.refl _)
    exact not_three_dvd_center_pomegaPlus_one hSC hℓ4 (hdiv.trans hdvdZ)
  obtain ⟨E, U, hE, hEcard, hU, hU2, hEU⟩ := quadPlusWitness (F := F) (m := lab.rank) (by omega)
  have hbound : lab.rank - 1 ≤ CFSG.Open.twoLocalPrimeRank 3 K :=
    le_twoLocalPrimeRank_of_center_quotient (e.trans (φ₁.trans φ₂)) Nat.prime_three
      (by norm_num) hZ hU hU2 hE hEcard hEU
  have hz0 : CFSG.Open.pRank 3 (Subgroup.center K) = 0 :=
    pRank_eq_zero_of_not_dvd_card Nat.prime_three hZ
  rw [hz0]
  omega

theorem rk2_split_low_BCD_one {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D)
    (hn : lab.n = 1) :
    lab.rank - 1 + CFSG.Open.pRank 3 (Subgroup.center K) ≤
      CFSG.Open.twoLocalPrimeRank 3 K := by
  rcases htag with hB | hC | hD
  · exact rk2_split_low_BC_one hK (Or.inl hB) hn
  · exact rk2_split_low_BC_one hK (Or.inr hC) hn
  ·
    have h3le : 3 ≤ lab.rank := by
      have h := (quasisimple_markedModel_of_isLabel hK).2.1
      simp only [CFSG.Assembly.LargeEvenInLambda2, hD] at h
      exact h.2
    rcases Nat.lt_or_ge lab.rank 4 with hlt | hge
    · have h3 : lab.rank = 3 := by omega
      obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
      obtain ⟨F, hF, hFin, hcardF, ⟨e₀⟩⟩ :=
        exists_model_psl_of_isLabel hM (d := 4) (n := lab.n)
          (by simp [CFSG.StandardType.markTag, hD, h3])
          (by simp [CFSG.StandardType.markRank, hD, h3])
          (by simp [CFSG.StandardType.markChar, hD])
          (by simp [CFSG.StandardType.markDeg, hD])
      letI : Field F := hF
      letI : Finite F := hFin
      letI : Fintype F := Fintype.ofFinite F
      have hcard2 : Nat.card F = 2 := by rw [hcardF, hn]; norm_num
      have hcard' : Fintype.card F = 2 ^ 1 := by
        rw [← Nat.card_eq_fintype_card]; exact hcard2
      haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
      have hM4 : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSL 4 2 1 := by
        simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag, CFSG.StandardType.markRank,
          CFSG.StandardType.markChar, CFSG.StandardType.markDeg, hD, h3, hn] using hM
      have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) :=
        not_three_dvd_center_of_psl_two_one hQ hM4
      obtain ⟨E, X, hX, hX2, hE, hEcard, hEX⟩ :=
        exists_elemAbelian_le_normalizer_PSL_of_card (K := F) (n := 4) (k := 2) (m := 0)
          (by norm_num) (by norm_num)
      let eP : K ⧸ Subgroup.center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) F :=
        e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 F).symm
      have hbound : 2 ≤ CFSG.Open.twoLocalPrimeRank 3 K :=
        le_twoLocalPrimeRank_of_center_quotient eP Nat.prime_three (by norm_num) hZ
          hX hX2 hE hEcard hEX
      have hz0 : CFSG.Open.pRank 3 (Subgroup.center K) = 0 :=
        pRank_eq_zero_of_not_dvd_card Nat.prime_three hZ
      rw [h3, hz0]
      omega
    · exact rk2_split_low_D_one hK hD hn hge


private def e6D5Chain : Fin 5 → Fin (Tag.rank .E6) := ![1, 2, 3, 4, 5]

private def d5Cartan : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2, 0, -1, 0, 0; 0, 2, -1, 0, 0; -1, -1, 2, -1, 0; 0, 0, -1, 2, -1; 0, 0, 0, -1, 2]

private def d5Adjugate : Matrix (Fin 5) (Fin 5) ℤ :=
  !![5, 3, 6, 4, 2; 3, 5, 6, 4, 2; 6, 6, 12, 8, 4; 4, 4, 8, 8, 4; 2, 2, 4, 4, 4]

private theorem d5Chain_cartan :
    (fun i j => Tag.cartan .E6 (e6D5Chain i) (e6D5Chain j)) = d5Cartan := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem d5Cartan_mul_adjugate :
    d5Cartan * d5Adjugate = (4 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem prod_torusElt_rootVec_d5 {F : Type} [Field F]
    (a : Fin 5 → Fˣ) (j : Fin 5) :
    (((List.ofFn fun i : Fin 5 => torusElt .E6 F (e6D5Chain i) (a i)).prod :
        (Module.End F (RootModule .E6 F))ˣ) : Module.End F (RootModule .E6 F))
      (rootVec .E6 F (Pi.single (e6D5Chain j) 1)) =
    (((List.ofFn fun i : Fin 5 =>
        a i ^ (Tag.cartan .E6 (e6D5Chain i) (e6D5Chain j))).prod : Fˣ) : F) •
      rootVec .E6 F (Pi.single (e6D5Chain j) 1) := by
  have hα : IsRoot .E6 (Pi.single (e6D5Chain j) 1) := isRoot_single .E6 _
  have h := list_prod_torusElt_rootVec (R := F) (τ := .E6) hα
    (List.ofFn fun i : Fin 5 => (e6D5Chain i, a i))
  rw [List.map_ofFn] at h
  simpa [sum_cartan_mul_pi_single] using h

private theorem d5_prod_eq_one_of_prod_eq_one {F : Type} [Field F]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Fˣ} (hζ : orderOf ζ = p) {a : Fin 5 → ℤ}
    (h : (List.ofFn fun i : Fin 5 => torusElement .E6 F (e6D5Chain i) (ζ ^ a i)).prod = 1) :
    ∀ i, (p : ℤ) ∣ a i := by
  have hchar : ∀ j : Fin 5,
      (∏ i : Fin 5, (ζ ^ a i) ^ (Tag.cartan .E6 (e6D5Chain i) (e6D5Chain j)) : Fˣ) = 1 := by
    intro j
    have hroot := prod_torusElt_rootVec_d5 (fun i => ζ ^ a i) j
    have hcoe : (((List.ofFn fun i : Fin 5 =>
        torusElement .E6 F (e6D5Chain i) (ζ ^ a i)).prod :
        adjointGroup .E6 F) : ModGL .E6 F) =
        (List.ofFn fun i : Fin 5 =>
          torusElt .E6 F (e6D5Chain i) (ζ ^ a i)).prod := by
      have hmap := List.prod_hom (l := List.ofFn fun i : Fin 5 =>
        torusElement .E6 F (e6D5Chain i) (ζ ^ a i))
        (f := Subgroup.subtype (adjointGroup .E6 F))
      rw [List.map_ofFn] at hmap
      exact hmap.symm
    have hL : ((List.ofFn fun i : Fin 5 =>
        torusElt .E6 F (e6D5Chain i) (ζ ^ a i)).prod : ModGL .E6 F) = 1 := by
      rw [← hcoe, h, OneMemClass.coe_one]
    rw [hL] at hroot
    simp only [Units.val_one, Module.End.one_apply] at hroot
    rw [rootVec_eq_single_of_isRoot (isRoot_single .E6 _)] at hroot
    have hcoord := congrArg (fun v : RootModule .E6 F =>
      v (Sum.inr ⟨Pi.single (e6D5Chain j) 1, isRoot_single .E6 _⟩)) hroot
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at hcoord
    rw [← List.prod_ofFn (f := fun i : Fin 5 =>
      (ζ ^ a i) ^ (Tag.cartan .E6 (e6D5Chain i) (e6D5Chain j)))]
    exact Units.ext hcoord.symm
  have hd : ∀ j : Fin 5, (∏ i : Fin 5, (ζ ^ a i) ^ d5Cartan i j) = 1 := by
    intro j
    rw [← hchar j]
    exact Finset.prod_congr rfl fun i _ => by rw [← d5Chain_cartan]
  have hkey : ∀ k : Fin 5, (ζ ^ a k) ^ (4 : ℕ) =
      ∏ j : Fin 5, (∏ i : Fin 5, (ζ ^ a i) ^ d5Cartan i j) ^ d5Adjugate j k := by
    intro k
    have h1 : (ζ ^ a k) ^ (4 : ℕ) =
        ∏ i : Fin 5, (ζ ^ a i) ^ ((d5Cartan * d5Adjugate) i k) := by
      rw [d5Cartan_mul_adjugate]
      simp [Matrix.smul_apply, Matrix.one_apply]
    rw [h1]
    simp only [Matrix.mul_apply, ← Finset.prod_zpow_eq_zpow_sum, zpow_mul]
    rw [Finset.prod_comm]
    simp only [Finset.prod_zpow]
  have h4 : ∀ k : Fin 5, (ζ ^ a k) ^ (4 : ℕ) = 1 := by
    intro k
    rw [hkey k]
    simp [hd]
  have hp4 : Nat.Coprime 4 p := by
    have h2 : Nat.Coprime 2 p := Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)
    have h4 : Nat.Coprime (2 ^ 2) p := h2.pow_left 2
    norm_num at h4
    exact h4
  intro i
  have hpi : (ζ ^ a i) ^ p = 1 := by
    rw [← zpow_natCast (ζ ^ a i) p, ← zpow_mul, mul_comm (a i) (p : ℤ), zpow_mul,
      show ζ ^ (p : ℤ) = 1 by rw [zpow_natCast, ← hζ, pow_orderOf_eq_one], one_zpow]
  have hgcd : (ζ ^ a i) ^ (Nat.gcd 4 p) = 1 := (pow_gcd_eq_one).2 ⟨h4 i, hpi⟩
  rw [hp4, pow_one] at hgcd
  have hdvd : (orderOf ζ : ℤ) ∣ a i := orderOf_dvd_iff_zpow_eq_one.mpr hgcd
  simpa [hζ] using hdvd

private theorem d5_card_closure {F : Type} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Fˣ} (hζ : orderOf ζ = p) :
    Nat.card (Subgroup.closure
      (Set.range fun i : Fin 5 => torusElement .E6 F (e6D5Chain i) ζ)) = p ^ 5 := by
  let h : Fin 5 → adjointGroup .E6 F := fun i => torusElement .E6 F (e6D5Chain i) ζ
  let E : Subgroup (adjointGroup .E6 F) := Subgroup.closure (Set.range h)
  have hpow : ∀ i, h i ^ p = 1 := by
    intro i
    change (CFSG.LieType.Steinberg.Adjoint.torusHom (τ := .E6) (K := F) (e6D5Chain i)) ζ ^ p = 1
    rw [← map_pow, show ζ ^ p = 1 by rw [← hζ, pow_orderOf_eq_one], map_one]
  have hcomm : ∀ i j, Commute (h i) (h j) := by
    intro i j
    exact CFSG.LieType.Steinberg.Adjoint.torus_commute (g := h i) (h := h j)
      ⟨ζ, rfl⟩ ⟨ζ, rfl⟩
  have hS : ∀ s ∈ Set.range h, ∀ t ∈ Set.range h, Commute s t := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hcomm i j
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, Commute x y := by
    intro x hx y hy
    dsimp only [E] at hx hy ⊢
    exact CFSG.RankThree.CentralCover.commute_of_mem_closure (S := Set.range h) hS hx hy
  haveI : IsMulCommutative E := ⟨⟨fun x y => Subtype.ext (hEcomm x x.2 y y.2).eq⟩⟩
  letI : CommGroup E := IsMulCommutative.instCommGroup
  have hle : Nat.card E ≤ p ^ 5 :=
    card_closure_le_pow_of_commuting hp hpow hcomm
  have hinj : Function.Injective (fun a : Fin 5 → Fin p =>
      ∏ i : Fin 5, (⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : E) ^ (a i : ℤ)) := by
    intro a b hab
    have hab' : (∏ i : Fin 5,
        (⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : E) ^ (a i : ℤ)) =
        ∏ i : Fin 5, (⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : E) ^ (b i : ℤ) := hab
    have hdiff : (∏ i : Fin 5,
        (⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : E) ^ ((a i : ℤ) - (b i : ℤ))) = 1 := by
      calc (∏ i : Fin 5,
            (⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : E) ^ ((a i : ℤ) - (b i : ℤ)))
          = ∏ i : Fin 5, ((⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : E) ^ (a i : ℤ) *
              ((⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : E) ^ (b i : ℤ))⁻¹) := by
            exact Finset.prod_congr rfl fun i _ => by rw [zpow_sub]
        _ = (∏ i : Fin 5, (⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : E) ^ (a i : ℤ)) *
              (∏ i : Fin 5, (⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : E) ^ (b i : ℤ))⁻¹ := by
            rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
        _ = 1 := by
            rw [← hab']
            exact mul_inv_cancel _
    have hR : (List.ofFn fun i : Fin 5 =>
        torusElement .E6 F (e6D5Chain i) (ζ ^ ((a i : ℤ) - (b i : ℤ)))).prod = 1 := by
      have h2 : (((∏ i : Fin 5,
          (⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : E) ^ ((a i : ℤ) - (b i : ℤ))) : E) :
            adjointGroup .E6 F) =
          (List.ofFn fun i : Fin 5 => (h i) ^ ((a i : ℤ) - (b i : ℤ))).prod := by
        rw [← List.prod_ofFn (f := fun i : Fin 5 =>
          (⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : E) ^ ((a i : ℤ) - (b i : ℤ)))]
        have hmap := map_list_prod (Subgroup.subtype E) (List.ofFn fun i : Fin 5 =>
          (⟨h i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : E) ^ ((a i : ℤ) - (b i : ℤ)))
        rw [List.map_ofFn] at hmap
        exact hmap.trans (by congr 1)
      have h3 : ∀ i : Fin 5, (h i) ^ ((a i : ℤ) - (b i : ℤ)) =
          torusElement .E6 F (e6D5Chain i) (ζ ^ ((a i : ℤ) - (b i : ℤ))) := by
        intro i
        change ((CFSG.LieType.Steinberg.Adjoint.torusHom (τ := .E6) (K := F)
          (e6D5Chain i)) ζ) ^ ((a i : ℤ) - (b i : ℤ)) = _
        rw [← map_zpow]
        rfl
      rw [hdiff, OneMemClass.coe_one] at h2
      have h4 : (List.ofFn fun i : Fin 5 => (h i) ^ ((a i : ℤ) - (b i : ℤ))) =
          List.ofFn fun i : Fin 5 =>
            torusElement .E6 F (e6D5Chain i) (ζ ^ ((a i : ℤ) - (b i : ℤ))) := by
        rw [List.ofFn_inj]
        funext i
        exact h3 i
      rw [h4] at h2
      exact h2.symm
    have hdvd := d5_prod_eq_one_of_prod_eq_one hp hp2 hζ
      (a := fun i => (a i : ℤ) - (b i : ℤ)) hR
    funext i
    have hlt : ((a i : ℤ) - (b i : ℤ)).natAbs < p := by
      have ha := (a i).isLt
      have hb := (b i).isLt
      omega
    have hdvd' : p ∣ ((a i : ℤ) - (b i : ℤ)).natAbs := Int.natCast_dvd.mp (hdvd i)
    have hd0 : ((a i : ℤ) - (b i : ℤ)).natAbs = 0 := by
      by_contra hne
      have hpos : 0 < ((a i : ℤ) - (b i : ℤ)).natAbs := Nat.pos_of_ne_zero hne
      exact absurd (Nat.le_of_dvd hpos hdvd') (by omega)
    have hzero : (a i : ℤ) - (b i : ℤ) = 0 := Int.natAbs_eq_zero.mp hd0
    apply Fin.ext
    have : (a i : ℤ) = (b i : ℤ) := by omega
    exact_mod_cast this
  have hge : p ^ 5 ≤ Nat.card E := by
    have h := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_fun, Nat.card_fin, Nat.card_fin] at h
  exact le_antisymm hle hge

theorem rk2_split_low_E6 {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .E6) (hpq : p ∣ 2 ^ lab.n - 1) :
    5 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.twoLocalPrimeRank p K := by
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 lab.n :=
    lieModel_of_markedModel_E6 htag hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E6 ∈ CFSG.Blueprint.chevalleyExceptionalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hn1 : 1 ≤ lab.n := hlab.1
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hFcard
  have hpq' : p ∣ Nat.card F - 1 := by rw [hFcard]; exact hpq
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rwa [Nat.card_units])
  let h : Fin 5 → adjointGroup .E6 F := fun i => torusElement .E6 F (e6D5Chain i) ζ
  let w : Fin 5 → adjointGroup .E6 F := fun i => weylElement .E6 F (e6D5Chain i)
  have hpow : ∀ i, h i ^ p = 1 := by
    intro i
    change (CFSG.LieType.Steinberg.Adjoint.torusHom (τ := .E6) (K := F) (e6D5Chain i)) ζ ^ p = 1
    rw [← map_pow, show ζ ^ p = 1 by rw [← hζ, pow_orderOf_eq_one], map_one]
  have hcomm : ∀ i j, Commute (h i) (h j) := by
    intro i j
    exact CFSG.LieType.Steinberg.Adjoint.torus_commute (g := h i) (h := h j)
      ⟨ζ, rfl⟩ ⟨ζ, rfl⟩
  have hind : Nat.card (Subgroup.closure (Set.range h)) = p ^ 5 :=
    d5_card_closure hp hp2 hζ
  have hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹ := by
    intro i
    have hζinv : torusElt .E6 F (e6D5Chain i) ζ⁻¹ =
        (torusElt .E6 F (e6D5Chain i) ζ)⁻¹ := by
      refine eq_inv_of_mul_eq_one_right ?_
      rw [← torusElt_mul, mul_inv_cancel, torusElt_one]
    have hbraid := weylElt_mul_torusElt_mul_inv (τ := .E6) (K := F) (e6D5Chain i) ζ
    rw [hζinv] at hbraid
    exact Subtype.ext hbraid
  have hcross : ∀ i j, i ≠ j →
      w i * h j * (w i)⁻¹ * (h j)⁻¹ ∈ Subgroup.zpowers (h i) := by
    intro i j hij
    set e : ℤ := -Tag.cartan .E6 (e6D5Chain j) (e6D5Chain i)
    have hconj : w i * h j * (w i)⁻¹ =
        h j * torusElement .E6 F (e6D5Chain i) (ζ ^ e) := by
      apply Subtype.ext
      exact weylElt_one_mul_torusElt_mul_inv (τ := .E6) (R := F)
        (e6D5Chain i) (e6D5Chain j) ζ
    have hcomm' : Commute (h j) (torusElement .E6 F (e6D5Chain i) (ζ ^ e)) := by
      exact CFSG.LieType.Steinberg.Adjoint.torus_commute
        (g := h j) (h := torusElement .E6 F (e6D5Chain i) (ζ ^ e))
        ⟨ζ, rfl⟩ ⟨ζ ^ e, rfl⟩
    have hred : w i * h j * (w i)⁻¹ * (h j)⁻¹ =
        torusElement .E6 F (e6D5Chain i) (ζ ^ e) := by
      rw [hconj, mul_assoc, (hcomm'.symm.inv_right).eq, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [hred]
    have hpow' : torusElement .E6 F (e6D5Chain i) (ζ ^ e) = (h i) ^ e := by
      change (CFSG.LieType.Steinberg.Adjoint.torusHom (τ := .E6) (K := F)
        (e6D5Chain i)) (ζ ^ e) = _
      rw [map_zpow]
      rfl
    rw [hpow']
    exact Subgroup.mem_zpowers_iff.mpr ⟨e, rfl⟩
  let α : Fin (Tag.rank .E6) → ℤ := Pi.single 0 1
  have hα : IsRoot .E6 α := isRoot_single .E6 0
  let X : Subgroup (adjointGroup .E6 F) :=
    (rootSubgroup .E6 F α).subgroupOf (adjointGroup .E6 F)
  have hXcard : Nat.card X = Nat.card F := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (rootSubgroup_le_adjointGroup α)).toEquiv, card_rootSubgroup]
  have hX1 : X ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card X = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hXcard, hFcard] at h1
    have h2 : 2 ≤ 2 ^ lab.n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn1
    omega
  have hX2 : IsPGroup 2 X := by
    refine IsPGroup.of_card (n := lab.n) ?_
    rw [hXcard, hFcard]
  have hNX : ∀ i, h i ∈ Subgroup.normalizer (X : Set (adjointGroup .E6 F)) := by
    intro i
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    dsimp only [X]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hvN : (torusElt .E6 F (e6D5Chain i) ζ) ∈
        Subgroup.normalizer (rootSubgroup .E6 F α : Set (ModGL .E6 F)) :=
      torusGroup_le_normalizer_rootSubgroup (τ := .E6) (R := F) hα
        (torusElt_mem_torusGroup (e6D5Chain i) ζ)
    rw [Subgroup.mem_normalizer_iff''] at hvN
    have hcoe : (((h i)⁻¹ * x * h i : adjointGroup .E6 F) : ModGL .E6 F) =
        (torusElt .E6 F (e6D5Chain i) ζ)⁻¹ * (x : ModGL .E6 F) *
          torusElt .E6 F (e6D5Chain i) ζ := rfl
    rw [hcoe]
    exact hvN (x : ModGL .E6 F)
  let θ : K ⧸ Subgroup.center K ≃* adjointGroup .E6 F :=
    φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E6 F)
  exact central_lift_le_twoLocalPrimeRank θ hp hp2 hpow hcomm hind hinv hcross hX1 hX2 hNX

end CFSG.LocalAnalysis.GLTheoremA
