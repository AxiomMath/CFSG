module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ExcE6
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6ScBound
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.TwE6ScBound
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center
public import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Blueprint.Multiplier CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.CentralExt.FieldFour
  CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed CFSG.LieType.Simplicity
  CFSG.LieType.Steinberg.TwistedE6
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial


private theorem factorization_three_eq_one_of_dvd_twelve {N : ℕ} (h3 : 3 ∣ N) (h12 : N ∣ 12) :
    N.factorization 3 = 1 := by
  have hN0 : N ≠ 0 := (Nat.pos_of_dvd_of_pos h12 (by norm_num)).ne'
  have h1 : 1 ≤ N.factorization 3 := (Nat.prime_three.dvd_iff_one_le_factorization hN0).1 h3
  have h2 : ¬ 2 ≤ N.factorization 3 := by
    intro h
    have h9 : 9 ∣ N := by
      simpa using (Nat.prime_three.pow_dvd_iff_le_factorization hN0).2 h
    have : 9 ∣ 12 := h9.trans h12
    norm_num at this
  omega

private theorem three_dvd_two_pow_sub_one_of_markedModel_E6 {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hQ : CFSG.IsQuasisimple K)
    (hM : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 lab.n)
    (hZ : 3 ∣ Nat.card (Subgroup.center K)) :
    3 ∣ 2 ^ lab.n - 1 := by
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
    (K ⧸ Subgroup.center K) .E6 0 2 lab.n hM
  have hg : genericOrders .E6 0 2 lab.n = (Nat.gcd 3 (2 ^ lab.n - 1), 1) := rfl
  have he : exceptionalOrders .E6 0 2 lab.n = (1, 1) := rfl
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) =
      Nat.gcd 3 (2 ^ lab.n - 1) := by
    rw [Nat.card_congr eM.toEquiv,
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg, he]
    norm_num
  haveI : Finite (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcard]
      exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
  have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ
    (MulEquiv.refl (K ⧸ Subgroup.center K))
  rw [hcard] at hdvd
  exact (Nat.dvd_gcd_iff.1 (hZ.trans hdvd)).2

private theorem three_dvd_two_pow_add_one_of_markedModel_twE6 {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hQ : CFSG.IsQuasisimple K)
    (hM : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n)
    (hZ : 3 ∣ Nat.card (Subgroup.center K)) :
    3 ∣ 2 ^ lab.n + 1 := by
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
    (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n hM
  have hg : genericOrders .twistedE6 0 2 lab.n = (Nat.gcd 3 (2 ^ lab.n + 1), 1) := rfl
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) =
      Nat.gcd 3 (2 ^ lab.n + 1) * (if lab.n = 1 then 4 else 1) := by
    rw [Nat.card_congr eM.toEquiv,
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg]
    by_cases hn : lab.n = 1
    · simp [hn, exceptionalOrders, markTag, markRank, markChar, markDeg]
    · simp [hn, exceptionalOrders, markTag, markRank, markChar, markDeg]
  have hpos : 0 < Nat.gcd 3 (2 ^ lab.n + 1) * (if lab.n = 1 then 4 else 1) :=
    Nat.mul_pos (Nat.gcd_pos_of_pos_left _ (by norm_num))
      (by by_cases hn : lab.n = 1 <;> simp [hn])
  haveI : Finite (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hpos.ne')
  have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ
    (MulEquiv.refl (K ⧸ Subgroup.center K))
  rw [hcard] at hdvd
  have hdiv : 3 ∣ Nat.gcd 3 (2 ^ lab.n + 1) * (if lab.n = 1 then 4 else 1) :=
    hZ.trans hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hdiv with h | h
  · exact (Nat.dvd_gcd_iff.1 h).2
  · by_cases hn : lab.n = 1
    · rw [if_pos hn] at h
      norm_num at h
    · rw [if_neg hn] at h
      exact absurd h (by norm_num)

theorem nonempty_derivedCentralQuotient_galoisField_twistedE6 {X : Type} [Group X] {n : ℕ}
    (hn : 1 ≤ n) (h : CFSG.Blueprint.TwistedChevalleyModel X .E6 (2 ^ n)) :
    Nonempty (X ≃* CFSG.Blueprint.DerivedCentralQuotient
      (CFSG.Blueprint.twistedFixedGroup .E6 (GaloisField 2 (2 * n)) (frobQ 2 n))) := by
  obtain ⟨F, hFld, hFin, hFcard, σ, hσ, ⟨e⟩⟩ := h
  letI : Field F := hFld
  letI : Finite F := hFin
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype (GaloisField 2 (2 * n)) := Fintype.ofFinite _
  have hLcard : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 := by
    rw [GaloisField.card 2 (2 * n) (by omega), show 2 * n = n * 2 by ring, pow_mul]
  let ι : F ≃+* GaloisField 2 (2 * n) :=
    FiniteField.ringEquivOfCardEq (by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
      exact hFcard.trans hLcard.symm)
  have hfrob : ∀ c : GaloisField 2 (2 * n), frobQ 2 n c = c ^ 2 ^ n := fun c => frobQ_apply 2 n c
  have hmap := map_baseChangeGL_graphFixedRootGroup_eq (t := .E6) (p := 2) (f := n)
    Nat.prime_two hn F hFcard σ hσ (L := GaloisField 2 (2 * n)) ι.toRingHom hfrob
    (Finite.surjective_of_injective (frobQ 2 n).injective)
  have hZL := center_twDerived_eq_bot (K := GaloisField 2 (2 * n)) (σ := frobQ 2 n)
    Nat.prime_two hn hLcard hfrob
  obtain ⟨-, -, hΓL, -, -⟩ := finite_fixed_root_group_perfect .E6 Nat.prime_two hn
    (GaloisField 2 (2 * n)) hLcard (frobQ 2 n) hfrob
  have hZF := center_twDerived_eq_bot (K := F) (σ := σ) Nat.prime_two hn hFcard hσ
  obtain ⟨-, -, hΓF, -, -⟩ := finite_fixed_root_group_perfect .E6 Nat.prime_two hn F hFcard σ hσ
  let eBC : ↥(graphFixedRootGroup .E6 F σ) ≃* ↥(graphFixedRootGroup .E6
      (GaloisField 2 (2 * n)) (frobQ 2 n)) :=
    (Subgroup.equivMapOfInjective _ (baseChangeGL ι.toRingHom)
      (baseChangeGL_injective ι.toRingHom)).trans (MulEquiv.subgroupCongr hmap)
  exact ⟨e.trans ((derivedCentralQuotientEquiv σ hZF).trans
    ((MulEquiv.subgroupCongr hΓF).trans (eBC.trans
      ((MulEquiv.subgroupCongr hΓL).symm.trans (derivedCentralQuotientEquiv (frobQ 2 n) hZL).symm))))⟩

theorem rk2E6CoverThreeFrontier : Rk2E6CoverThreeFrontier := by
  intro K _ _ lab p hK htag hp hZ
  subst hp
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hM6 : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 lab.n :=
    lieModel_of_markedModel_E6 htag hM
  have h3dvd : 3 ∣ 2 ^ lab.n - 1 := three_dvd_two_pow_sub_one_of_markedModel_E6 hQ' hM6 hZ
  have hord : rk2Ord 3 lab.n = 1 := rk2Ord_eq_one_iff.2 h3dvd
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
    (K ⧸ Subgroup.center K) .E6 0 2 lab.n hM6
  have hg : genericOrders .E6 0 2 lab.n = (Nat.gcd 3 (2 ^ lab.n - 1), 1) := rfl
  have he : exceptionalOrders .E6 0 2 lab.n = (1, 1) := rfl
  have hcardM : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) =
      Nat.gcd 3 (2 ^ lab.n - 1) := by
    rw [Nat.card_congr eM.toEquiv,
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg, he]
    norm_num
  haveI : Finite (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcardM]
      exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
  have hdvdZ : Nat.card (Subgroup.center K) ∣ Nat.gcd 3 (2 ^ lab.n - 1) := by
    have h := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ'
      (MulEquiv.refl (K ⧸ Subgroup.center K))
    rwa [hcardM] at h
  have hZcard : Nat.card (Subgroup.center K) = 3 := by
    have hgcd : Nat.gcd 3 (2 ^ lab.n - 1) = 3 := Nat.gcd_eq_left h3dvd
    have hle : Nat.card (Subgroup.center K) ≤ 3 := by
      rw [← hgcd]
      exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by norm_num)) hdvdZ
    have hge : 3 ≤ Nat.card (Subgroup.center K) := Nat.le_of_dvd Nat.card_pos hZ
    omega
  have hfacK : (Nat.card (Subgroup.center K)).factorization 3 =
      (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (K ⧸ Subgroup.center K))).factorization 3 := by
    have h1 : (Nat.card (Subgroup.center K)).factorization 3 = 1 := by
      rw [hZcard]
      exact Nat.Prime.factorization_self Nat.prime_three
    have h2 : (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (K ⧸ Subgroup.center K))).factorization 3 = 1 := by
      rw [← Nat.card_congr
        (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
          (K ⧸ Subgroup.center K)).toEquiv, hcardM, Nat.gcd_eq_left h3dvd]
      exact Nat.Prime.factorization_self Nat.prime_three
    exact h1.trans h2.symm
  obtain ⟨F, hFld, hFin, hFcard, ⟨eAdj⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup Tag.E6
      (untwistedModel_of_lieModel_E6 hM6).2.2
  letI : Field F := hFld
  letI : Finite F := hFin
  have h3F : 3 ∣ Nat.card F - 1 := by rw [hFcard]; exact h3dvd
  haveI hGfin : Finite ↥(e6Data_valid.minGroup F) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' e6Data_valid
  haveI hGperf : Group.IsPerfect ↥(e6Data_valid.minGroup F) := CFSG.LieType.CurtisTits.isPerfect_e6 F
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect K := hQ'.1
  let κ : K →* (K ⧸ Subgroup.center K) := QuotientGroup.mk' (Subgroup.center K)
  have hκ : Function.Surjective κ := QuotientGroup.mk'_surjective _
  have hκcen : κ.ker ≤ Subgroup.center K := by
    rw [show κ.ker = Subgroup.center K from QuotientGroup.ker_mk' (Subgroup.center K)]
  have hfacK' : (Nat.card κ.ker).factorization 3 =
      (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (K ⧸ Subgroup.center K))).factorization 3 := by
    rw [show κ.ker = Subgroup.center K from QuotientGroup.ker_mk' (Subgroup.center K), hfacK]
  let γ : ↥(e6Data_valid.minGroup F) →* (K ⧸ Subgroup.center K) :=
    eAdj.symm.toMonoidHom.comp (e6Isogeny F)
  have hγ : Function.Surjective γ :=
    eAdj.symm.surjective.comp (e6Isogeny_surjective F)
  have hγker : γ.ker = (e6Isogeny F).ker :=
    MonoidHom.ker_comp_of_injective (e6Isogeny F) eAdj.symm.toMonoidHom eAdj.symm.injective
  have hγcen : γ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup F) := by
    rw [hγker, e6Isogeny_ker_eq_center]
  have hfacG : (Nat.card γ.ker).factorization 3 =
      (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (K ⧸ Subgroup.center K))).factorization 3 := by
    have h1 : (Nat.card γ.ker).factorization 3 = 1 := by
      rw [hγker, e6Isogeny_ker_eq_center, (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 (k := F)).1, hFcard,
        Nat.gcd_eq_left h3dvd]
      exact Nat.Prime.factorization_self Nat.prime_three
    have h2 : (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (K ⧸ Subgroup.center K))).factorization 3 = 1 := by
      rw [← Nat.card_congr
        (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
          (K ⧸ Subgroup.center K)).toEquiv, hcardM, Nat.gcd_eq_left h3dvd]
      exact Nat.Prime.factorization_self Nat.prime_three
    exact h1.trans h2.symm
  have hcomp := pRank_le_of_hopfCover (p := 3) Nat.prime_three κ hκ hκcen hfacK'
    γ hγ hγcen hfacG
  calc CFSG.Open.pRank 3 (⊤ : Subgroup K)
      = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(e6Data_valid.minGroup F)) := hcomp
    _ ≤ 6 := pRank_three_e6Sc_le_six h3F
    _ = rk2Mult lab (rk2Ord 3 lab.n) := by
        rw [hord]
        simp [rk2Mult, htag, rk2Cnt]

theorem rk2TwE6CoverThreeFrontier : Rk2TwE6CoverThreeFrontier := by
  intro K _ _ lab p hK htag hp hZ
  subst hp
  obtain ⟨hQ, hlab, hM⟩ := rk2_model_of_isLabel hK
  have hn : 1 ≤ lab.n := hlab.1
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hMt : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg, htag] using hM
  have h3dvd : 3 ∣ 2 ^ lab.n + 1 :=
    three_dvd_two_pow_add_one_of_markedModel_twE6 hQ' hMt hZ
  have hord : rk2Ord 3 lab.n = 2 :=
    (rk2Ord_eq_two_iff Nat.prime_three (by norm_num)).2 h3dvd
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
    (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n hMt
  have hg : genericOrders .twistedE6 0 2 lab.n = (Nat.gcd 3 (2 ^ lab.n + 1), 1) := rfl
  have hcardM : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) =
      Nat.gcd 3 (2 ^ lab.n + 1) * (if lab.n = 1 then 4 else 1) := by
    rw [Nat.card_congr eM.toEquiv,
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg]
    by_cases hn1 : lab.n = 1
    · simp [hn1, exceptionalOrders, markTag, markRank, markChar, markDeg]
    · simp [hn1, exceptionalOrders, markTag, markRank, markChar, markDeg]
  have hpos : 0 < Nat.gcd 3 (2 ^ lab.n + 1) * (if lab.n = 1 then 4 else 1) :=
    Nat.mul_pos (Nat.gcd_pos_of_pos_left _ (by norm_num))
      (by by_cases hn1 : lab.n = 1 <;> simp [hn1])
  haveI : Finite (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardM]; exact hpos.ne')
  have hdvdZ : Nat.card (Subgroup.center K) ∣
      Nat.gcd 3 (2 ^ lab.n + 1) * (if lab.n = 1 then 4 else 1) := by
    have h := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ'
      (MulEquiv.refl (K ⧸ Subgroup.center K))
    rwa [hcardM] at h
  have hsmall : (if lab.n = 1 then 4 else 1) = 4 ∨ (if lab.n = 1 then 4 else 1) = 1 := by
    by_cases hn1 : lab.n = 1 <;> simp [hn1]
  have h12 : Nat.card (Subgroup.center K) ∣ 12 := by
    have h := hdvdZ
    rw [Nat.gcd_eq_left h3dvd] at h
    rcases hsmall with h4 | h4
    · rw [h4] at h
      simpa using h
    · rw [h4] at h
      exact h.trans (by norm_num)
  have hfacK : (Nat.card (Subgroup.center K)).factorization 3 =
      (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (K ⧸ Subgroup.center K))).factorization 3 := by
    have h1 : (Nat.card (Subgroup.center K)).factorization 3 = 1 :=
      factorization_three_eq_one_of_dvd_twelve hZ h12
    have h2 : (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (K ⧸ Subgroup.center K))).factorization 3 = 1 := by
      rw [← Nat.card_congr
        (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
          (K ⧸ Subgroup.center K)).toEquiv, hcardM, Nat.gcd_eq_left h3dvd]
      rcases hsmall with h4 | h4
      · rw [h4]
        exact factorization_three_eq_one_of_dvd_twelve (by norm_num) (by norm_num)
      · rw [h4]
        exact factorization_three_eq_one_of_dvd_twelve (by norm_num) (by norm_num)
    exact h1.trans h2.symm
  obtain ⟨eStd⟩ := nonempty_derivedCentralQuotient_galoisField_twistedE6 hn
    (twistedChevalleyModel_of_lieModel hMt).2.2
  let L : Type := GaloisField 2 (2 * lab.n)
  let Fr : L →+* L := frobQ 2 lab.n
  have hLcard : Nat.card L = (2 ^ lab.n) ^ 2 := by
    rw [GaloisField.card 2 (2 * lab.n) (by omega),
      show 2 * lab.n = lab.n * 2 by ring, pow_mul]
  have hFr : ∀ c : L, Fr c = c ^ 2 ^ lab.n := fun c => frobQ_apply 2 lab.n c
  have hθ : ∀ c : L, Fr (Fr c) = c := frobQ_frobQ 2 lab.n hn
  have h4L : 4 ≤ Nat.card L := four_le_card_galoisField 2 lab.n hn
  haveI hModGLfin : Finite (ModGL TwistTag.E6.tag L) := finite_modGL
  haveI hΓfin : Finite ↥(graphFixedRootGroup .E6 L Fr) := Subtype.finite
  haveI hGperf : Group.IsPerfect (↥(fixedGroup L Fr)) :=
    fixedGroup_isPerfect_of_four_le_card Fr hθ h4L
  haveI hGfin : Finite (↥(fixedGroup L Fr)) := Subtype.finite
  have hΓstd : ⁅twistedFixedGroup .E6 L Fr, twistedFixedGroup .E6 L Fr⁆ =
      graphFixedRootGroup .E6 L Fr :=
    (finite_fixed_root_group_perfect .E6 Nat.prime_two hn L hLcard Fr hFr).2.2.1
  have hZbot : Subgroup.center ↥(twDerived Fr) = ⊥ :=
    center_twDerived_eq_bot (K := L) (σ := Fr) Nat.prime_two hn hLcard hFr
  let κ : K →* (K ⧸ Subgroup.center K) := QuotientGroup.mk' (Subgroup.center K)
  have hκ : Function.Surjective κ := QuotientGroup.mk'_surjective _
  have hκcen : κ.ker ≤ Subgroup.center K := by
    rw [show κ.ker = Subgroup.center K from QuotientGroup.ker_mk' (Subgroup.center K)]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect K := hQ'.1
  have hfacK' : (Nat.card κ.ker).factorization 3 =
      (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (K ⧸ Subgroup.center K))).factorization 3 := by
    rw [show κ.ker = Subgroup.center K from QuotientGroup.ker_mk' (Subgroup.center K), hfacK]
  let eModel : ↥(graphFixedRootGroup .E6 L Fr) ≃* (K ⧸ Subgroup.center K) :=
    ((derivedCentralQuotientEquiv Fr hZbot).trans (MulEquiv.subgroupCongr hΓstd)).symm.trans
      eStd.symm
  let γ₁ : ↥(fixedGroup L Fr) →* ↥(graphFixedRootGroup .E6 L Fr) :=
    (MulEquiv.subgroupCongr hΓstd).toMonoidHom.comp (twistedIsogeny Fr hθ h4L)
  let γ : ↥(fixedGroup L Fr) →* (K ⧸ Subgroup.center K) :=
    eModel.toMonoidHom.comp γ₁
  have hγ₁ker : γ₁.ker = (twistedIsogeny Fr hθ h4L).ker :=
    MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr hΓstd).injective
  have hγ₁ : Function.Surjective γ₁ :=
    (MulEquiv.subgroupCongr hΓstd).surjective.comp (twistedIsogeny_surjective Fr hθ h4L)
  have hγ : Function.Surjective γ := eModel.surjective.comp hγ₁
  have hγker : γ.ker = (twistedIsogeny Fr hθ h4L).ker := by
    rw [show γ = eModel.toMonoidHom.comp γ₁ from rfl,
      MonoidHom.ker_comp_of_injective _ _ eModel.injective, hγ₁ker]
  have hγcen : γ.ker ≤ Subgroup.center ↥(fixedGroup L Fr) := by
    rw [hγker, ker_twistedIsogeny_eq_center (k := L) (θ := Fr) hθ h4L]
  have hfacG : (Nat.card γ.ker).factorization 3 =
      (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (K ⧸ Subgroup.center K))).factorization 3 := by
    have h1 : (Nat.card γ.ker).factorization 3 = 1 := by
      rw [hγker, ker_twistedIsogeny_eq_center (k := L) (θ := Fr) hθ h4L,
        (card_center_fixedGroup (k := L) (θ := Fr) (q := 2 ^ lab.n) hLcard hFr).1,
        Nat.gcd_eq_left h3dvd]
      exact Nat.Prime.factorization_self Nat.prime_three
    have h2 : (Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (K ⧸ Subgroup.center K))).factorization 3 = 1 := by
      rw [← Nat.card_congr
        (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
          (K ⧸ Subgroup.center K)).toEquiv, hcardM, Nat.gcd_eq_left h3dvd]
      rcases hsmall with h4 | h4
      · rw [h4]
        exact factorization_three_eq_one_of_dvd_twelve (by norm_num) (by norm_num)
      · rw [h4]
        exact factorization_three_eq_one_of_dvd_twelve (by norm_num) (by norm_num)
    exact h1.trans h2.symm
  have hcomp := pRank_le_of_hopfCover (p := 3) Nat.prime_three κ hκ hκcen hfacK'
    γ hγ hγcen hfacG
  calc CFSG.Open.pRank 3 (⊤ : Subgroup K)
      = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(fixedGroup L Fr)) := hcomp
    _ ≤ 6 := pRank_three_twistedE6Sc_le_six hn h3dvd
    _ = rk2Mult lab (rk2Ord 3 lab.n) := by
        rw [hord]
        simp [rk2Mult, htag, rk2Cnt]

theorem rk2E6Frontier : Rk2E6Frontier :=
  ⟨rk2E6CoverThreeFrontier, rk2TwE6CoverThreeFrontier⟩

theorem rk2_pRank_le_E6_all (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E6 ∨ lab.tag = .twE6) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) :=
  rk2_pRank_le_E6_of_frontier rk2E6Frontier K lab p hK htag hp hp2

end CFSG.LocalAnalysis.GLTheoremA

end
