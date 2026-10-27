module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFactsCore
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1116Alt
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1116Chev2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop126b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13d
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1112b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GaschutzTransfer
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaFour
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.CountingFpf
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Fi22Five

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration (typeSign
  dvd_typeSign_of_hasFixedPointFreeOrder statedOmega_quadPlus_three_mulEquiv_alt8
  statedOmega_quadMinus_two_mulEquiv_alt5)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (tors torsBound tors_of_not_dvd
  center_torsion_le)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

theorem prime_dvd_card_of_isPGroup {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] [Finite Y]
    {H : Subgroup Y} (hH : IsPGroup p H) (hne : H ≠ ⊥) : p ∣ Nat.card H := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.card_eq_one.mp (by simpa using hk))
  rw [hk]
  exact dvd_pow_self p hk0

theorem center_eq_bot_of_not_sq_dvd {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] [Finite Y]
    (hperf : commutator Y = ⊤) (hO : GLAPPrimeCore p Y = ⊥)
    (hsq : ¬ p ^ 2 ∣ Nat.card (Y ⧸ Subgroup.center Y)) : Subgroup.center Y = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hpg := isPGroup_center_of_glaPPrimeCore_eq_bot hp hO
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p (prime_dvd_card_of_isPGroup hp hpg hne)
  have hz1 : (z : Y) ≠ 1 := by
    intro h
    have h1 : z = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hzp : (z : Y) ^ p = 1 := by
    have h1 : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    exact congrArg Subtype.val h1
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p Y))
  refine CFSG.LocalAnalysis.RankThreeTheoremC.not_isMulCommutative_sylow_of_isPerfect ⟨hperf⟩ S
    z.2 hz1 hzp ?_
  set R : Subgroup (Y ⧸ Subgroup.center Y) :=
    (S : Subgroup Y).map (QuotientGroup.mk' (Subgroup.center Y)) with hR
  have hRp : IsPGroup p R := S.isPGroup'.map _
  obtain ⟨j, hj⟩ := hRp.exists_card_eq
  have hj1 : j ≤ 1 := by
    by_contra h
    apply hsq
    have h2 : p ^ 2 ∣ Nat.card R := hj ▸ pow_dvd_pow p (by omega)
    exact h2.trans (Subgroup.card_subgroup_dvd_card R)
  have hdvdp : Nat.card R ∣ p := by
    rw [hj]
    calc p ^ j ∣ p ^ 1 := pow_dvd_pow p hj1
      _ = p := pow_one p
  have hRc : IsCyclic R := isCyclic_of_card_dvd_prime hdvdp
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  exact (CFSG.Timmesfeld.RankOne.commute_of_mem_comap_of_isCyclic le_rfl hRc
    (Subgroup.le_comap_map _ _ a.2) (Subgroup.le_comap_map _ _ b.2)).eq

theorem five_le_of_isAltType {n : ℕ} {Y : Type*} [Group Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hA : IsAltType n (Y ⧸ Subgroup.center Y)) : 5 ≤ n := by
  obtain ⟨hcomm, hsimp⟩ := hq
  obtain ⟨e⟩ := hA
  by_contra hlt
  haveI : Group.IsPerfect Y := Group.isPerfect_def.mpr hcomm
  haveI : Nontrivial (Y ⧸ Subgroup.center Y) := hsimp.toNontrivial
  haveI : Group.IsSolvable (alternatingGroup (Fin n)) :=
    alternatingGroup.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  haveI : Group.IsSolvable (Y ⧸ Subgroup.center Y) :=
    solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
  exact Group.IsPerfect.not_isSolvable _ this

theorem card_center_dvd_of_isAltType {n : ℕ} {Y : Type} [Group Y]
    [Finite Y] (hq : CFSG.Open.IsQuasisimple Y) (hA : IsAltType n (Y ⧸ Subgroup.center Y)) :
    Nat.card (Subgroup.center Y) ∣ (if n = 6 ∨ n = 7 then 6 else 2) := by
  have hn5 := five_le_of_isAltType hq hA
  obtain ⟨hcomm, -⟩ := hq
  obtain ⟨e⟩ := hA
  haveI : Group.IsPerfect Y := Group.isPerfect_def.mpr hcomm
  haveI : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)⟩
  let π : Y →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center Y := by
    ext x
    simp [π, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  obtain ⟨-, h, -, -, -, -, eK, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier π hπ hker.le
  have hcardK : Nat.card (Subgroup.center Y) ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin n))) := by
    rw [← hker, ← Nat.card_congr eK.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  obtain ⟨-, hcard⟩ := CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput n hn5
  rwa [hcard] at hcardK

theorem center_eq_bot_or_of_isAltType {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hO : GLAPPrimeCore p Y = ⊥) (hA : IsAltType n (Y ⧸ Subgroup.center Y)) :
    Subgroup.center Y = ⊥ ∨ (p = 3 ∧ (n = 6 ∨ n = 7)) := by
  have hdvd := card_center_dvd_of_isAltType hq hA
  by_cases hpd : p ∣ Nat.card (Subgroup.center Y)
  · right
    have hp' := hpd.trans hdvd
    split_ifs at hp' with h67
    · refine ⟨?_, h67⟩
      have h6 : p ∣ 2 * 3 := hp'
      rcases (Nat.Prime.dvd_mul hp).mp h6 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp') hp2
  · left
    have hO' : CFSG.pPrimeCore p Y = ⊥ := hO
    exact (CFSG.pPrimeCore_eq_bot_iff.mp hO') (Subgroup.center Y) inferInstance
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd)

theorem inputSchurAlt'_holds : Lemma123.InputSchurAlt' :=
  fun _ _ hp hp2 _ _ _ hq hO hA => center_eq_bot_or_of_isAltType hp hp2 hq hO hA

theorem inputSchurAltComp_holds :
    Prop1116Design.InputSchurAltComp := by
  intro G _ _ p hp hp2 X L hL n hA
  exact center_eq_bot_or_of_isAltType hp hp2
    (CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hL)
    (glaPPrimeCore_quotient_eq_bot hp) hA

theorem inputAltCentre_holds : Prop126b.InputAltCentre := by
  intro X _ _ n hn8 hq hO hA
  rcases center_eq_bot_or_of_isAltType Nat.prime_three (by norm_num) hq hO hA with hZ | ⟨-, h67⟩
  · obtain ⟨e⟩ := hA
    exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e⟩
  · omega

theorem not_sq_dvd_sixty_or_168 {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : N = 60 ∨ N = 168) :
    ¬ p ^ 2 ∣ N := by
  intro h
  have hN0 : 0 < N := by omega
  have hle : p ^ 2 ≤ N := Nat.le_of_dvd hN0 h
  have hp13 : p < 13 := by
    by_contra h13
    have : 13 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hp2' := hp.two_le
  rcases hN with rfl | rfl <;> interval_cases p <;> simp_all +decide

theorem inputSchurFiveSeven_holds : Prop1116Design.InputSchurFiveSeven := by
  intro G _ _ p hp hp2 X L hL hcases
  have hq := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hL
  refine center_eq_bot_of_not_sq_dvd hp hq.1 (glaPPrimeCore_quotient_eq_bot hp) ?_
  apply not_sq_dvd_sixty_or_168 hp hp2
  rcases hcases with hA5 | h7
  · obtain ⟨f⟩ := hA5
    exact Or.inl ((Nat.card_congr f.toEquiv).trans Prop1116Design.card_alt_five)
  · exact Or.inr (Prop1116Design.card_statedProj_two_seven h7)

theorem nonempty_statedProj_zmod_two {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (Matrix.GeneralLinearGroup ι (ZMod 2))) : Nonempty (StatedProj H ≃* H) := by
  have h : (StatedScalars ι (ZMod 2)).subgroupOf H = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot ι, Subgroup.bot_subgroupOf]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot⟩

theorem lieModel_omegaPlus {Q : Type} [Group Q] {m : ℕ} (hm : 4 ≤ m)
    (g : Q ≃* ↥(StatedOmega (StatedQuadPlus m (ZMod 2)))) :
    CFSG.Models.LieModel Q .POmegaPlus m 2 1 := by
  have hadm : StatedLieAdmissible .POmegaPlus m 2 1 := ⟨Nat.prime_two, le_rfl, hm⟩
  obtain ⟨f⟩ := nonempty_statedProj_zmod_two (StatedOmega (StatedQuadPlus m (ZMod 2)))
  exact ⟨hadm, Or.inl ⟨hadm, ZMod 2, inferInstance, inferInstance, by simp, ⟨g.trans f.symm⟩⟩⟩

theorem lieModel_omegaMinus {Q : Type} [Group Q] {m : ℕ} (hm : 4 ≤ m)
    (g : Q ≃* ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1))) :
    CFSG.Models.LieModel Q .POmegaMinus m 2 1 := by
  have hadm : StatedLieAdmissible .POmegaMinus m 2 1 := ⟨Nat.prime_two, le_rfl, hm⟩
  obtain ⟨f⟩ := nonempty_statedProj_zmod_two (StatedOmega (StatedQuadMinus m (ZMod 2) 1 1))
  exact ⟨hadm, Or.inl ⟨hadm, ZMod 2, inferInstance, inferInstance, by simp, 1, 1, by decide,
    ⟨g.trans f.symm⟩⟩⟩

theorem tors_eq_one_of_dvd_four {r x : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hx : x ∣ 4) :
    tors r x = 1 := by
  apply tors_of_not_dvd
  intro h
  have h4 : r ∣ 2 ^ 2 := h.trans (by simpa using hx)
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h4))

theorem torsBound_omega_two {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (m : ℕ) : torsBound r t m 2 1 = 1 := by
  have hg : (genericOrders t m 2 1).1 ∣ 4 ∧ (genericOrders t m 2 1).2 ∣ 4 := by
    rcases ht with rfl | rfl <;> simp only [genericOrders] <;> (try split_ifs) <;>
      exact ⟨by first | exact Nat.gcd_dvd_left _ _ | norm_num, by norm_num⟩
  have he : (exceptionalOrders t m 2 1).1 ∣ 4 ∧ (exceptionalOrders t m 2 1).2 ∣ 4 := by
    rcases ht with rfl | rfl <;> unfold exceptionalOrders <;> split <;> simp_all
  simp only [torsBound, tors_eq_one_of_dvd_four hr hr2 hg.1, tors_eq_one_of_dvd_four hr hr2 hg.2,
    tors_eq_one_of_dvd_four hr hr2 he.1, tors_eq_one_of_dvd_four hr hr2 he.2]

theorem center_eq_bot_of_lieModel_omega (hGA : GriessAllModelsStatement) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    (hO : GLAPPrimeCore p X = ⊥) {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    {m : ℕ} (hm : CFSG.Models.LieModel (X ⧸ Subgroup.center X) t m 2 1) :
    Subgroup.center X = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle := center_torsion_le hGA hq (MulEquiv.refl _) hm hp
  rw [torsBound_omega_two hp hp2 ht m] at hle
  by_contra hne
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p
    (prime_dvd_card_of_isPGroup hp (isPGroup_center_of_glaPPrimeCore_eq_bot hp hO) hne)
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hzp : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have h2 : 1 < Nat.card {w : Subgroup.center X // w ^ p = 1} := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact ⟨⟨⟨1, one_pow p⟩, ⟨z, hzp⟩, fun h => hz1 (congrArg Subtype.val h).symm⟩⟩
  omega

theorem not_sq_five_dvd_card_omegaMinus_six :
    ¬ 5 ^ 2 ∣ Nat.card ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) := by
  intro h
  have h1 := h.trans (Subgroup.card_subgroup_dvd_card (StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)))
  rw [CatalogInputs.card_GL_zmod_two_eq (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) 6 (by simp)] at h1
  norm_num [Fin.prod_univ_six] at h1

theorem inputPiCenter_of_griess (hGA : GriessAllModelsStatement) :
    InputPiCenter := by
  intro X _ _ p hp hp2 hPi hnot7
  obtain ⟨hq, hO, hcase⟩ := hPi
  rcases hcase with ⟨k, ⟨e⟩⟩ | ⟨n, ε, hn1, hOm, hfp⟩ | ⟨hp3, ⟨e⟩⟩
  ·
    rcases center_eq_bot_or_of_isAltType hp hp2 hq hO ⟨e⟩ with hZ | ⟨rfl, h67⟩
    · exact hZ
    · omega
  ·
    cases ε with
    | true =>
      obtain ⟨g⟩ : Nonempty ((X ⧸ Subgroup.center X) ≃*
          ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2)))) := hOm
      rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | hn3
      ·
        have hd := dvd_typeSign_of_hasFixedPointFreeOrder hp hp2 le_rfl hfp
        have h1 : typeSign true 1 = 1 := by norm_num [typeSign]
        rw [h1] at hd
        exact absurd (Nat.eq_one_of_dvd_one hd) hp.one_lt.ne'
      ·
        rcases center_eq_bot_or_of_isAltType hp hp2 hq hO
            ⟨g.trans statedOmega_quadPlus_three_mulEquiv_alt8⟩ with hZ | ⟨-, h67⟩
        · exact hZ
        · omega
      · exact center_eq_bot_of_lieModel_omega hGA hp hp2 hq hO (Or.inl rfl)
          (lieModel_omegaPlus (by omega) g)
    | false =>
      obtain ⟨g⟩ : Nonempty ((X ⧸ Subgroup.center X) ≃*
          ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1))) := hOm
      rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | hn3
      ·
        rcases center_eq_bot_or_of_isAltType hp hp2 hq hO
            ⟨g.trans statedOmega_quadMinus_two_mulEquiv_alt5⟩ with hZ | ⟨-, h67⟩
        · exact hZ
        · omega
      ·
        have hd := dvd_typeSign_of_hasFixedPointFreeOrder hp hp2 (by norm_num) hfp
        have h5 : typeSign false 2 = 5 := by norm_num [typeSign]
        rw [h5] at hd
        have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd
        subst hp5
        refine center_eq_bot_of_not_sq_dvd hp hq.1 hO ?_
        rw [Nat.card_congr g.toEquiv]
        exact not_sq_five_dvd_card_omegaMinus_six
      · exact center_eq_bot_of_lieModel_omega hGA hp hp2 hq hO (Or.inr rfl)
          (lieModel_omegaMinus (by omega) g)
  ·
    subst hp3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hdvd := card_center_dvd_of_isAltType hq ⟨e⟩
    rw [if_pos (Or.inr rfl)] at hdvd
    obtain ⟨k, hk⟩ := (isPGroup_center_of_glaPPrimeCore_eq_bot hp hO).exists_card_eq
    have hk1 : k ≤ 1 := by
      by_contra h
      have h9 : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 (by omega)).trans (hk ▸ hdvd)
      norm_num at h9
    interval_cases k
    · exact Subgroup.card_eq_one.mp (by simpa using hk)
    · exact absurd ⟨hq.1, by simpa using hk, ⟨e⟩⟩ hnot7

theorem inputPiCenter_holds :
    InputPiCenter :=
  inputPiCenter_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

theorem input7_L34_holds : Input7_L34 := by
  intro X _ _ hq hL _ A _
  calc CFSG.Open.pRank 3 A ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) :=
        CFSG.SectionRank.pRank_mono (by norm_num) le_top
    _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (X ⧸ Subgroup.center X))) :=
        CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) (quotientCenterAut' X)
          (quotientCenterAut'_injective hq.1)
    _ ≤ 2 := pRank_mulAut_le_two_of_isLThreeFour hL

theorem inputAutL34Order9_holds : Lemma1112b.InputAutL34Order9 := by
  intro X _ hL E hE
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite X := by
    obtain ⟨K, _, _, -, ⟨f⟩⟩ := hL
    exact Finite.of_equiv _ f.symm.toEquiv
  obtain ⟨k, hk⟩ := (Lemma1112b.isPGroup_of_isElemAbelian hE).exists_card_eq
  have hk2 : k ≤ 2 :=
    (CFSG.SectionRank.le_pRank (by norm_num) le_top hE hk).trans
      (pRank_mulAut_le_two_of_isLThreeFour hL)
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

theorem inputSchurFi22_holds :
    Lemma123.InputSchurFi22 := by
  intro Y _ _ hq hO hs
  obtain ⟨e⟩ := CatalogInputs.fi22_nonempty_mulEquiv_native hs
  haveI : Group.IsPerfect Y := Group.isPerfect_def.mpr hq.1
  have hker : (QuotientGroup.mk' (Subgroup.center Y)).ker = Subgroup.center Y :=
    QuotientGroup.ker_mk' _
  have h := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.sporadicKernelTrivial_fi22_five
    Y (Y ⧸ Subgroup.center Y) (QuotientGroup.mk' (Subgroup.center Y)) ⟨e⟩
    (QuotientGroup.mk'_surjective _) hker.le
    (by rw [hker]; exact isPGroup_center_of_glaPPrimeCore_eq_bot Nat.prime_five hO)
  rwa [hker] at h

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts
