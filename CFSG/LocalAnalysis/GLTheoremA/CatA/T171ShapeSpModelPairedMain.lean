module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpModelPaired
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockAnModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Ind
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmCases
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthBlockAnalysis
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthBlockProofFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonalLie
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockAnMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial
open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.PartOne.KCUnitary
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped MatrixGroups commutatorElement

theorem spPaired_linearData {r n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) {x : StatedSp r K} {h : K[X]}
    (hh : h ∈ primaryFactors (spEnd x))
    (hP : SpPairedBlock 2 n p x ⟨h, hh⟩) (hp : p.Prime) (hp2 : p ≠ 2)
    (D : Subgroup (StatedSp r K))
    (hD : D = ⁅spSupported x
      ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]),
      spSupported x ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X])⁆)
    (hDF : D ≤ spSupported x ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]))
    (hpJ : p ∣ Nat.card (D.map (proj r K))) :
    ∃ (a : ℕ) (E : Type) (_ : Field E) (_ : Finite E)
      (eF : ↥(spSupported x ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X])) ≃*
        GL (Fin a) E) (eD : ↥D ≃* StatedSL a E),
      2 ≤ a ∧ Nat.card E = 2 ^ (n * (h : K[X]).natDegree) ∧
      (∀ d : ↥D, (eD d : GL (Fin a) E) = eF ⟨d.1, hDF d.2⟩) ∧
      (∀ M ∈ StatedSL a E, ∃ d : ↥D, (eF ⟨d.1, hDF d.2⟩ : GL (Fin a) E) = M) ∧
      CFSG.IsQuasisimple ↥D := by
  classical
  set F : Subgroup (StatedSp r K) :=
    spSupported x ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) with hF
  set E := AdjoinRoot (h : K[X]) with hEdef
  set W := primaryComponent (spEnd x) (h : K[X]) with hWdef
  obtain ⟨φ, hφ, hform⟩ := hP.factor
  haveI : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hdeg : 1 ≤ (h : K[X]).natDegree := Irreducible.natDegree_pos
    (irreducible_of_mem_primaryFactors hh)
  have hEcard : Nat.card E = 2 ^ (n * (h : K[X]).natDegree) := by
    rw [hP.card_field, pow_mul]
  have hE4 : 4 ≤ Nat.card E := by
    have hdvd : p ∣ Nat.card E - 1 := by
      rw [hEcard, pow_mul]
      exact hP.dvd
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      omega
    have hpos : 0 < Nat.card E - 1 := Nat.sub_pos_of_lt (Finite.one_lt_card)
    have := Nat.le_of_dvd hpos hdvd
    omega
  haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hm : 2 ≤ Module.finrank E W := by
    by_contra hlt
    have hlt' : Module.finrank E W ≤ 1 := by omega
    have hcomm : ∀ a b : ↥F, Commute a b := by
      intro a b
      apply φ.injective
      rw [map_mul, map_mul]
      apply Units.ext
      exact (End_commute_of_finrank_le_one hlt' _ _).eq
    have hbot : ⁅F, F⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩).eq).symm
    have h1 : Nat.card ((⊥ : Subgroup (StatedProj (StatedSp r K)))) = 1 := Subgroup.card_bot
    rw [hD, hbot, Subgroup.map_bot, h1] at hpJ
    exact hp.ne_one (Nat.dvd_one.mp hpJ)
  let b : Module.Basis (Fin (Module.finrank E W)) E W := Module.finBasis E W
  let T : GL (Fin (Module.finrank E W)) E ≃* blockGL (spEnd x) (h : K[X]) :=
    Matrix.GeneralLinearGroup.toLin' b
  let eF : ↥F ≃* GL (Fin (Module.finrank E W)) E := φ.trans T.symm
  have hdetT : ∀ M : GL (Fin (Module.finrank E W)) E,
      LinearMap.det ((T M : LinearMap.GeneralLinearGroup E W) : W →ₗ[E] W) =
        (M : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E).det :=
    fun M => CFSG.RankThree.CentralLift.det_toLin'_basis b M
  have hperf : Group.IsPerfect (blockGLDet (spEnd x) (h : K[X])).ker :=
    (isQuasisimple_ker_det hm
      (Or.inr (CFSG.RankThree.PartOne.KCSpIsotypic.exists_finset_card_four_of_card hE4))).1
  have hDcomm : kerImage F φ (blockGLDet (spEnd x) (h : K[X])) = ⁅F, F⁆ :=
    kerImage_eq_commutator F φ _ hperf
  have hεD : ∀ g : ↥F, (g : StatedSp r K) ∈ D ↔
      eF g ∈ LargeEvenSLGroup (Fin (Module.finrank E W)) E := by
    intro g
    rw [hD, ← hDcomm, mem_kerImage, largeEvenSLGroup_eq_statedSL, StatedAPI.mem_statedSL_iff]
    have e1 : ((T (eF g) : LinearMap.GeneralLinearGroup E W)) = φ g := by
      simp [eF]
    constructor
    · rintro ⟨hg, hdet⟩
      have hdet' := congrArg Units.val hdet
      rw [← hdetT, e1]
      simpa [blockGLDet] using hdet'
    · intro hdet
      refine ⟨g.2, ?_⟩
      apply Units.ext
      rw [← hdetT, e1] at hdet
      simpa [blockGLDet] using hdet
  have hsurj : ∀ M ∈ LargeEvenSLGroup (Fin (Module.finrank E W)) E, ∃ g : ↥F, eF g = M :=
    fun M _ => ⟨φ.symm (T M), by simp [eF]⟩
  let eFD : ↥D →* GL (Fin (Module.finrank E W)) E :=
    eF.toMonoidHom.comp (Subgroup.inclusion hDF)
  let eDhom : ↥D →* ↥(StatedSL (Module.finrank E W) E) :=
    { toFun := fun g => ⟨eFD g, by
        rw [← largeEvenSLGroup_eq_statedSL]
        exact (hεD ⟨g.1, hDF g.2⟩).mp g.2⟩
      map_one' := by
        apply Subtype.ext
        exact map_one eFD
      map_mul' := fun a b => by
        apply Subtype.ext
        exact map_mul eFD a b }
  have heDhom_inj : Function.Injective eDhom := by
    intro g g' hgg
    have h2 : eF ⟨g.1, hDF g.2⟩ = eF ⟨g'.1, hDF g'.2⟩ := by
      simpa [eDhom, eFD] using congrArg (fun x : ↥(StatedSL (Module.finrank E W) E) =>
        (x : GL (Fin (Module.finrank E W)) E)) hgg
    have h3 := eF.injective h2
    apply Subtype.ext
    exact congrArg (fun x : ↥F => (x : StatedSp r K)) h3
  have heDhom_surj : Function.Surjective eDhom := by
    intro M
    have hM' : (M : GL (Fin (Module.finrank E W)) E) ∈
        LargeEvenSLGroup (Fin (Module.finrank E W)) E := by
      rw [largeEvenSLGroup_eq_statedSL]
      exact M.2
    obtain ⟨g, hg⟩ := hsurj M.1 hM'
    have hgD : g.1 ∈ D := (hεD g).mpr (by
      rw [largeEvenSLGroup_eq_statedSL, hg]
      exact M.2)
    refine ⟨⟨g.1, hgD⟩, ?_⟩
    have hgg : ((Subgroup.inclusion hDF) ⟨g.1, hgD⟩ : ↥F) = g := Subtype.ext rfl
    exact Subtype.ext (show (eF ((Subgroup.inclusion hDF) ⟨g.1, hgD⟩) :
      GL (Fin (Module.finrank E W)) E) = ↑M from by
        rw [hgg]; exact hg)
  let eD : ↥D ≃* StatedSL (Module.finrank E W) E :=
    MulEquiv.ofBijective eDhom ⟨heDhom_inj, heDhom_surj⟩
  have heD_eq : ∀ g : ↥D, (eD g : GL (Fin (Module.finrank E W)) E) = eF ⟨g.1, hDF g.2⟩ :=
    fun g => rfl
  have hq : CFSG.IsQuasisimple ↥D := by
    have hqSL : CFSG.IsQuasisimple ↥(blockGLDet (spEnd x) (h : K[X])).ker :=
      isQuasisimple_ker_det hm
        (Or.inr (CFSG.RankThree.PartOne.KCSpIsotypic.exists_finset_card_four_of_card hE4))
    obtain ⟨eKI⟩ := nonempty_kerImage_mulEquiv F φ (blockGLDet (spEnd x) (h : K[X]))
    have hq2 : CFSG.IsQuasisimple ↥(kerImage F φ (blockGLDet (spEnd x) (h : K[X]))) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eKI.symm hqSL
    rw [hDcomm, ← hD] at hq2
    exact hq2
  refine ⟨Module.finrank E W, E, inferInstance, inferInstance, eF, eD, hm, hEcard, heD_eq,
    ?_, hq⟩
  intro M hM
  have hM' : M ∈ LargeEvenSLGroup (Fin (Module.finrank E W)) E := by
    rw [largeEvenSLGroup_eq_statedSL]
    exact hM
  obtain ⟨g, hg⟩ := hsurj M hM'
  have hgD : g.1 ∈ D := (hεD g).mpr (by
    rw [largeEvenSLGroup_eq_statedSL, hg]
    exact hM)
  refine ⟨⟨g.1, hgD⟩, ?_⟩
  have hgg : (⟨g.1, hDF hgD⟩ : ↥F) = g := Subtype.ext rfl
  rw [hgg]
  exact hg


theorem spPaired_pSimple_mulEquiv_largeEven_mk {r p a : ℕ} {K E : Type} [Field K] [Finite K]
    [Field E] [Finite E] (hp : p.Prime) (hr : 1 ≤ r)
    {x : StatedSp r K} {D : Subgroup (StatedSp r K)}
    {J : Subgroup (StatedProj (StatedSp r K))}
    (hq : CFSG.IsQuasisimple ↥D) (hpJ : p ∣ Nat.card J)
    (eD : ↥D ≃* StatedSL a E) (eJ : ↥D ≃* ↥J) :
    ∃ e : PSimple p J ≃* LargeEvenProj (StatedSL a E),
      ∀ d : ↥D, e (CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p J (eJ d)) =
        LargeEvenProjMk (StatedSL a E) (eD d) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect ↥D := hq.1
  have hdvd : p ∣ Nat.card ↥D := by
    rw [Nat.card_congr eJ.toEquiv]
    exact hpJ
  have hq' : CFSG.Open.IsQuasisimple ↥D :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥D).2.2.1.mp hq
  obtain ⟨eP, heP⟩ := exists_pSimpleEquivCenterQuot_mk (Ω := StatedSp r K) hp hq' hdvd
  have hker : eJ.toMonoidHom.ker ≤ Subgroup.center ↥D := by
    rw [(MonoidHom.ker_eq_bot_iff eJ.toMonoidHom).mpr eJ.injective]
    exact bot_le
  have hcore : GLAPPrimeCore p ↥J =
      (GLAPPrimeCore p ↥D).map eJ.toMonoidHom :=
    CFSG.HardMathSupport.Solomon.Coordinator.pPrimeCore_eq_map_of_central p
      eJ.toMonoidHom eJ.surjective hker
  let ψ : PQuot p D ≃* PQuot p J :=
    QuotientGroup.congr (GLAPPrimeCore p ↥D) (GLAPPrimeCore p ↥J) eJ hcore.symm
  let eJp : PSimple p D ≃* PSimple p J :=
    QuotientGroup.congr (Subgroup.center (PQuot p D)) (Subgroup.center (PQuot p J)) ψ
      (Subgroup.map_center_eq ψ)
  have heJp : ∀ d : ↥D, eJp (CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p D d) =
      CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p J (eJ d) := by
    intro d
    rfl
  let e2 : (↥D ⧸ Subgroup.center ↥D) ≃*
      (↥(StatedSL a E) ⧸ Subgroup.center ↥(StatedSL a E)) :=
    QuotientGroup.congr (Subgroup.center ↥D) (Subgroup.center ↥(StatedSL a E)) eD
      (Subgroup.map_center_eq eD)
  let e3 : (↥(StatedSL a E) ⧸ Subgroup.center ↥(StatedSL a E)) ≃*
      LargeEvenProj (StatedSL a E) :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.Quasithin.H13.S126P31.center_statedSL_eq a E)
  let e : PSimple p J ≃* LargeEvenProj (StatedSL a E) :=
    eJp.symm.trans (eP.symm.trans (e2.trans e3))
  refine ⟨e, ?_⟩
  intro d
  have h1 : eJp.symm (CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p J (eJ d)) =
      CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p D d :=
    eJp.symm_apply_eq.mpr (heJp d).symm
  have h2 : eP.symm (CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p D d) =
      QuotientGroup.mk d := by
    apply eP.injective
    rw [MulEquiv.apply_symm_apply]
    exact (heP d).symm
  have h3 : e2 (QuotientGroup.mk d) = QuotientGroup.mk (eD d) := rfl
  have h4 : e3 (QuotientGroup.mk (eD d)) = LargeEvenProjMk (StatedSL a E) (eD d) := rfl
  show e (CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p J (eJ d)) =
    LargeEvenProjMk (StatedSL a E) (eD d)
  simp only [e, MulEquiv.trans_apply, h1, h2, h3, h4]


theorem spPaired_conj_eq {r : ℕ} {K : Type} [Field K] {y yO : StatedSp r K}
    {F D : Subgroup (StatedSp r K)} (hDF : D ≤ F)
    (hyO : yO ∈ F) (hz : ∀ g ∈ F, Commute (yO⁻¹ * y) g) :
    ∀ d ∈ D, y⁻¹ * d * y = yO⁻¹ * d * yO := by
  intro d hd
  set z := yO⁻¹ * y with hzdef
  have hw : yO⁻¹ * d * yO ∈ F :=
    mul_mem (mul_mem (inv_mem hyO) (hDF hd)) hyO
  have hzc : z * (yO⁻¹ * d * yO) = (yO⁻¹ * d * yO) * z := hz _ hw
  have hy : y = yO * z := by rw [hzdef]; group
  calc y⁻¹ * d * y = (yO * z)⁻¹ * d * (yO * z) := by rw [hy]
    _ = z⁻¹ * (yO⁻¹ * d * yO) * z := by group
    _ = yO⁻¹ * d * yO := by
        calc z⁻¹ * (yO⁻¹ * d * yO) * z = z⁻¹ * ((yO⁻¹ * d * yO) * z) := by group
          _ = z⁻¹ * (z * (yO⁻¹ * d * yO)) := by rw [hzc]
          _ = yO⁻¹ * d * yO := by group

theorem spPaired_eD_conj {r a : ℕ} {K E : Type} [Field K] [Field E]
    {F D : Subgroup (StatedSp r K)} (hDF : D ≤ F)
    (eF : ↥F ≃* GL (Fin a) E) (eD : ↥D ≃* StatedSL a E)
    (heD_eq : ∀ d : ↥D, (eD d : GL (Fin a) E) = eF ⟨d.1, hDF d.2⟩)
    (yO : ↥F) (d : ↥D)
    (hyOd : (yO : StatedSp r K)⁻¹ * d.1 * (yO : StatedSp r K) ∈ D) :
    (eD ⟨(yO : StatedSp r K)⁻¹ * d.1 * (yO : StatedSp r K), hyOd⟩ :
        GL (Fin a) E) = (eF yO)⁻¹ * (eD d : GL (Fin a) E) * eF yO := by
  rw [heD_eq ⟨_, hyOd⟩, heD_eq d]
  have h : (⟨(yO : StatedSp r K)⁻¹ * d.1 * (yO : StatedSp r K), hDF hyOd⟩ : ↥F) =
      yO⁻¹ * ⟨d.1, hDF d.2⟩ * yO := Subtype.ext rfl
  rw [h, map_mul, map_mul, map_inv]

theorem spPaired_eJ_conj {r p : ℕ} {K : Type} [Field K] [Finite K] {y yO : StatedSp r K}
    {F D : Subgroup (StatedSp r K)} (hDF : D ≤ F) (hyO : yO ∈ F)
    (hz : ∀ g ∈ F, Commute (yO⁻¹ * y) g)
    {J : Subgroup (StatedProj (StatedSp r K))} (eJ : ↥D ≃* ↥J)
    (heJ : ∀ d : ↥D, (eJ d : StatedProj (StatedSp r K)) = proj r K d)
    (d : ↥D) (hyOd : (yO : StatedSp r K)⁻¹ * d.1 * (yO : StatedSp r K) ∈ D) :
    (eJ ⟨(yO : StatedSp r K)⁻¹ * d.1 * (yO : StatedSp r K), hyOd⟩ :
        StatedProj (StatedSp r K)) = (proj r K y)⁻¹ * (eJ d) * proj r K y := by
  calc (eJ ⟨(yO : StatedSp r K)⁻¹ * d.1 * (yO : StatedSp r K), hyOd⟩ :
        StatedProj (StatedSp r K)) = proj r K ((yO : StatedSp r K)⁻¹ * d.1 * (yO : StatedSp r K)) :=
      heJ _
    _ = proj r K (y⁻¹ * d.1 * y) := by rw [spPaired_conj_eq hDF hyO hz d.1 d.2]
    _ = (proj r K y)⁻¹ * (proj r K d.1) * proj r K y := by rw [map_mul, map_mul, map_inv]
    _ = (proj r K y)⁻¹ * (eJ d) * proj r K y := by rw [heJ d]


theorem spPaired_exists_sl_scalar {E : Type} [Field E] [Finite E]
    (heven : Even (Nat.card E)) (B : GL (Fin 2) E) :
    ∃ mu : Eˣ, (Matrix.GeneralLinearGroup.scalar (Fin 2) mu)⁻¹ * B ∈ StatedSL 2 E := by
  have hcard : Nat.card Eˣ = Nat.card E - 1 := Nat.card_units E
  have hodd : Odd (Nat.card Eˣ) := by
    rw [hcard]
    obtain ⟨k, hk⟩ := heven
    have hpos : 0 < Nat.card E := Nat.card_pos
    refine ⟨k - 1, by omega⟩
  have hcop : Nat.Coprime (Nat.card Eˣ) 2 := Nat.coprime_two_right.mpr hodd
  obtain ⟨mu, hmu⟩ := (powCoprime hcop).surjective (Matrix.GeneralLinearGroup.det B)
  refine ⟨mu, ?_⟩
  have hdet : Matrix.GeneralLinearGroup.det
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) mu)⁻¹ * B) = 1 := by
    rw [map_mul, map_inv, Matrix.GeneralLinearGroup.det_scalar]
    simp only [Fintype.card_fin]
    rw [← hmu]
    exact inv_mul_cancel (mu ^ 2)
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
  have hval : ((Matrix.GeneralLinearGroup.scalar (Fin 2) mu)⁻¹ * B :
      GL (Fin 2) E) = ((Matrix.GeneralLinearGroup.scalar (Fin 2) mu)⁻¹ * B) := rfl
  rw [show (↑((Matrix.GeneralLinearGroup.scalar (Fin 2) mu)⁻¹ * B) :
      Matrix (Fin 2) (Fin 2) E).det = ((Matrix.GeneralLinearGroup.det
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) mu)⁻¹ * B) : Eˣ) : E) from rfl, hdet]
  exact Units.val_one


theorem spPairedBlockModelDvd_holds : SpPairedBlockModelDvd := by
  intro m n p K _ _ hK hm hp hp2 x y hxp hyp hxy hx1 h hh h1 hne hP J hJeq hN hpJ
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F : Subgroup (StatedSp m K) :=
    spSupported x ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) with hF
  set D : Subgroup (StatedSp m K) := ⁅F, F⁆ with hD
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hK
      have hc := Finite.one_lt_card (α := K)
      omega
    · exact h0
  haveI hchar : CharP K 2 := by
    letI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [Fintype.card_eq_nat_card, hK])
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hpK : (p : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h0).symm
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero m := ⟨by omega⟩
  have hproj : Function.Injective (proj m K) :=
    CFSG.LocalAnalysis.GLTheoremA.K155XSp.l154s_proj_injective (r := m) (K := K) h2
  have hm1 : 1 ≤ m := by omega
  have hxne : proj m K x ≠ 1 := fun hx' =>
    hx1 ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
      (r := m) (K := K)).1 (by rw [hx', map_one]))
  have ha : orderOf (proj m K x) = p :=
    orderOf_eq_prime (by rw [← map_pow, hxp, map_one]) hxne
  have hxp' : orderOf x = p := orderOf_eq_prime hxp hx1
  have hF' : F = spSupported x ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) := hF
  have hD' : D = ⁅spSupported x ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]),
      spSupported x ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X])⁆ := by
    rw [hD, hF]
  have hDF : D ≤ spSupported x ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) := by
    rw [hD']
    exact Subgroup.commutator_le_self _
  have hblocks : SpPrimaryBlocks 2 n p x (proj m K x) :=
    (symplectic_cross_prime_primary_centralizer_blocks (ℓ := 2) (f := n) (p := p) (r := m)
      (K := K) Nat.prime_two hn1 hK hp hp2 hp2 hm1 (proj m K x) ha).2 x rfl hxp'
  let O : ↥(reciprocalOrbits (spEnd x)) :=
    ⟨{h, reciprocalPolynomial (h : K[X])}, ⟨h, hh, rfl⟩⟩
  obtain ⟨yO, hyO, hyOp, hz⟩ := spPaired_exists_blockComponent hyp hxy hblocks O
  have hpJ' : p ∣ Nat.card (D.map (proj m K)) := by rwa [← hJeq]
  obtain ⟨a, E, hEfield, hEfin, eF, eD, ha2, hcard, heD_eq, hsurj, hq⟩ :=
    spPaired_linearData hK hn1 hh hP hp hp2 D hD' hDF hpJ'
  letI : Field E := hEfield
  letI : Finite E := hEfin
  let eJ : ↥D ≃* ↥J :=
    (Subgroup.equivMapOfInjective D (proj m K) hproj).trans (MulEquiv.subgroupCongr hJeq.symm)
  have heJ : ∀ d : ↥D, (eJ d : StatedProj (StatedSp m K)) = proj m K d := fun d => rfl
  obtain ⟨e, he⟩ := spPaired_pSimple_mulEquiv_largeEven_mk (a := a) (E := E) (x := x) hp hm1 hq
    (by rwa [hJeq]) eD eJ
  let B : GL (Fin a) E := (eF ⟨yO, hyO⟩)⁻¹
  have hBpow : B ^ p = 1 := by
    have h1 : (⟨yO, hyO⟩ : ↥F) ^ p = 1 := Subtype.ext hyOp
    have h2 : (eF ⟨yO, hyO⟩) ^ p = 1 := by rw [← map_pow, h1, map_one]
    change ((eF ⟨yO, hyO⟩)⁻¹) ^ p = 1
    rw [inv_pow, h2, inv_one]
  have hBn : B ∈ Subgroup.normalizer (StatedSL a E : Set (GL (Fin a) E)) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  have hDnorm : (D.subgroupOf F).Normal := by
    rw [hD]
    infer_instance
  have hyOd : ∀ d : ↥D, (yO : StatedSp m K)⁻¹ * d.1 * (yO : StatedSp m K) ∈ D := by
    intro d
    have hdF : (⟨d.1, hDF d.2⟩ : ↥F) ∈ D.subgroupOf F := (Subgroup.mem_subgroupOf).mpr d.2
    have hmem := hDnorm.conj_mem (⟨d.1, hDF d.2⟩ : ↥F) hdF
      (⟨(yO : StatedSp m K)⁻¹, inv_mem hyO⟩ : ↥F)
    have hmem' : (((⟨(yO : StatedSp m K)⁻¹, inv_mem hyO⟩ : ↥F) *
        ⟨d.1, hDF d.2⟩ *
          (⟨(yO : StatedSp m K)⁻¹, inv_mem hyO⟩ : ↥F)⁻¹ : ↥F) : StatedSp m K) ∈ D :=
      (Subgroup.mem_subgroupOf).mp hmem
    simpa using hmem'
  have hk2 : 2 ≤ n * (h : K[X]).natDegree := by
    have hk1 : 1 ≤ n * (h : K[X]).natDegree := by
      have hd := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors hh)
      nlinarith
    rcases Nat.lt_or_ge (n * (h : K[X]).natDegree) 2 with hlt | hge
    · exfalso
      have hk1' : n * (h : K[X]).natDegree = 1 := by omega
      have hdvd : p ∣ 2 ^ (n * (h : K[X]).natDegree) - 1 := by
        rw [pow_mul]
        exact hP.dvd
      rw [hk1'] at hdvd
      norm_num at hdvd
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      omega
    · exact hge
  by_cases hsmall : a = 2 ∧ Nat.card E = 4
  ·
    obtain ⟨ha2', hsmallE⟩ := hsmall
    subst ha2'
    have hEven : Even (Nat.card E) := by rw [hsmallE]; norm_num
    obtain ⟨mu, hmu⟩ := spPaired_exists_sl_scalar (E := E) hEven (eF ⟨yO, hyO⟩)
    let C : GL (Fin 2) E := (Matrix.GeneralLinearGroup.scalar (Fin 2) mu)⁻¹ * eF ⟨yO, hyO⟩
    obtain ⟨d₁, hd₁⟩ := hsurj C hmu
    have hconjD : ∀ d : ↥D, (⟨(yO : StatedSp m K)⁻¹ * d.1 * (yO : StatedSp m K),
        hyOd d⟩ : ↥D) = d₁⁻¹ * d * d₁ := by
      intro d
      apply Subtype.ext
      have hF : (⟨(yO : StatedSp m K)⁻¹ * d.1 * (yO : StatedSp m K),
            hDF (hyOd d)⟩ : ↥F) =
          (⟨((d₁⁻¹ * d * d₁ : ↥D) : StatedSp m K),
            hDF (d₁⁻¹ * d * d₁).2⟩ : ↥F) := by
        apply eF.injective
        have h1 : (⟨(yO : StatedSp m K)⁻¹ * d.1 * (yO : StatedSp m K),
            hDF (hyOd d)⟩ : ↥F) =
            ⟨yO, hyO⟩⁻¹ * ⟨d.1, hDF d.2⟩ * ⟨yO, hyO⟩ := Subtype.ext rfl
        have h3 : (⟨((d₁⁻¹ * d * d₁ : ↥D) : StatedSp m K),
            hDF (d₁⁻¹ * d * d₁).2⟩ : ↥F) =
            ⟨d₁.1, hDF d₁.2⟩⁻¹ * ⟨d.1, hDF d.2⟩ * ⟨d₁.1, hDF d₁.2⟩ := Subtype.ext rfl
        rw [h1, h3, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
        have hd₁' : eF ⟨d₁.1, hDF d₁.2⟩ = C := hd₁
        rw [hd₁']
        have hB : eF ⟨yO, hyO⟩ = Matrix.GeneralLinearGroup.scalar (Fin 2) mu * C := by
          show eF ⟨yO, hyO⟩ = Matrix.GeneralLinearGroup.scalar (Fin 2) mu *
            ((Matrix.GeneralLinearGroup.scalar (Fin 2) mu)⁻¹ * eF ⟨yO, hyO⟩)
          group
        rw [hB, mul_inv_rev]
        have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin 2) mu)
            (eF ⟨d.1, hDF d.2⟩) := Matrix.GeneralLinearGroup.scalar_commute _ _
        calc C⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) mu)⁻¹ *
              eF ⟨d.1, hDF d.2⟩ * (Matrix.GeneralLinearGroup.scalar (Fin 2) mu * C)
            = C⁻¹ * ((Matrix.GeneralLinearGroup.scalar (Fin 2) mu)⁻¹ *
                eF ⟨d.1, hDF d.2⟩) *
                (Matrix.GeneralLinearGroup.scalar (Fin 2) mu * C) := by group
          _ = C⁻¹ * (eF ⟨d.1, hDF d.2⟩ *
                (Matrix.GeneralLinearGroup.scalar (Fin 2) mu)⁻¹) *
                (Matrix.GeneralLinearGroup.scalar (Fin 2) mu * C) := by
              rw [hcomm.inv_left.eq]
          _ = C⁻¹ * eF ⟨d.1, hDF d.2⟩ * C := by group
      exact congrArg (fun z : ↥F => (z : StatedSp m K)) hF
    have hconjJ : ∀ z : ↥J, (proj m K y)⁻¹ * (z : StatedProj (StatedSp m K)) * (proj m K y) =
        (proj m K d₁)⁻¹ * (z : StatedProj (StatedSp m K)) * (proj m K d₁) := by
      intro z
      obtain ⟨d, rfl⟩ := eJ.surjective z
      rw [heJ d]
      have hval : (yO : StatedSp m K)⁻¹ * d.1 * (yO : StatedSp m K) =
          ((d₁⁻¹ * d * d₁ : ↥D) : StatedSp m K) :=
        congrArg (fun w : ↥D => (w : StatedSp m K)) (hconjD d)
      calc (proj m K y)⁻¹ * (proj m K d.1) * (proj m K y)
          = proj m K (y⁻¹ * d.1 * y) := by rw [map_mul, map_mul, map_inv]
        _ = proj m K (yO⁻¹ * d.1 * yO) := by
              rw [spPaired_conj_eq hDF hyO hz d.1 d.2]
        _ = proj m K ((d₁⁻¹ * d * d₁ : ↥D) : StatedSp m K) := by
              rw [hval]
        _ = (proj m K d₁)⁻¹ * (proj m K d.1) * (proj m K d₁) := by
              rw [show ((d₁⁻¹ * d * d₁ : ↥D) : StatedSp m K) =
                (d₁ : StatedSp m K)⁻¹ * (d : StatedSp m K) * (d₁ : StatedSp m K) from rfl,
                map_mul, map_mul, map_inv]
    have hmemJ' : (proj m K d₁)⁻¹ ∈ J := by
      rw [hJeq]
      exact Subgroup.inv_mem _ (Subgroup.mem_map_of_mem (proj m K) d₁.2)
    have hmemJ : (proj m K d₁)⁻¹ ∈
        Subgroup.normalizer (J : Set (StatedProj (StatedSp m K))) :=
      Subgroup.le_normalizer hmemJ'
    refine Or.inr ⟨CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p J
      ⟨(proj m K d₁)⁻¹, hmemJ'⟩, ?_⟩
    have hmain : CFSG.LocalAnalysis.GLTheoremA.chevAut p J
        ⟨(proj m K y)⁻¹, Subgroup.inv_mem _ hN⟩ =
        MulAut.conj (CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p J
          ⟨(proj m K d₁)⁻¹, hmemJ'⟩) :=
      chevAut_eq_conj_chevQuotHom (Subgroup.inv_mem _ hN) hmemJ' hconjJ
    rw [show MI.indAut p J (proj m K y) hN =
      CFSG.LocalAnalysis.GLTheoremA.chevAut p J
        ⟨(proj m K y)⁻¹, Subgroup.inv_mem _ hN⟩ from rfl]
    exact hmain.symm
  ·
    have hnotSmall : a = 2 → 3 ≤ n * (h : K[X]).natDegree := by
      intro ha2'
      have hne : Nat.card E ≠ 4 := fun h4 => hsmall ⟨ha2', h4⟩
      have hkne : n * (h : K[X]).natDegree ≠ 2 := by
        intro hk
        apply hne
        rw [hcard, hk]
        norm_num
      omega
    letI : Fintype E := Fintype.ofFinite E
    haveI hcharE : CharP E 2 := charP_of_card_eq_prime_pow (p := 2)
      (f := n * (h : K[X]).natDegree) (by rw [Fintype.card_eq_nat_card, hcard])
    have h2E : (2 : E) = 0 := CharP.cast_eq_zero E 2
    have hBmem : ∀ mm : ↥(StatedSL a E),
        B * (mm : GL (Fin a) E) * B⁻¹ ∈ StatedSL a E :=
      fun mm => (Subgroup.mem_normalizer_iff.mp hBn (mm : GL (Fin a) E)).mp mm.2
    have hequiv : ∀ mm : ↥(StatedSL a E),
        MulAut.congr e (MI.indAut p J (proj m K y) hN)
            (LargeEvenProjMk (StatedSL a E) mm) =
          LargeEvenProjMk (StatedSL a E) ⟨B * (mm : GL (Fin a) E) * B⁻¹, hBmem mm⟩ := by
      intro mm
      set d : ↥D := eD.symm mm with hd
      have hmm : LargeEvenProjMk (StatedSL a E) mm =
          e (CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p J (eJ d)) := by
        rw [he d, MulEquiv.apply_symm_apply]
      have hind : MI.indAut p J (proj m K y) hN
          (CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p J (eJ d)) =
          CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p J
            (eJ ⟨(yO : StatedSp m K)⁻¹ * d.1 * (yO : StatedSp m K), hyOd d⟩) := by
        have hmem : (proj m K y)⁻¹ ∈
            Subgroup.normalizer (J : Set (StatedProj (StatedSp m K))) :=
          Subgroup.inv_mem _ hN
        have hJ : J.normalizerMonoidHom ⟨(proj m K y)⁻¹, hmem⟩ (eJ d) =
            eJ ⟨(yO : StatedSp m K)⁻¹ * d.1 * (yO : StatedSp m K), hyOd d⟩ := by
          apply Subtype.ext
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
          show (proj m K y)⁻¹ * (eJ d : StatedProj (StatedSp m K)) * (proj m K y) = _
          exact (spPaired_eJ_conj (p := p) hDF hyO hz eJ heJ d (hyOd d)).symm
        rw [show MI.indAut p J (proj m K y) hN =
          CFSG.LocalAnalysis.GLTheoremA.chevAut p J ⟨(proj m K y)⁻¹, hmem⟩ from rfl]
        rw [CFSG.LocalAnalysis.GLTheoremA.chevAut_chevQuotHom, hJ]
      rw [show MulAut.congr e (MI.indAut p J (proj m K y) hN)
            (LargeEvenProjMk (StatedSL a E) mm) =
          e (MI.indAut p J (proj m K y) hN (e.symm (LargeEvenProjMk (StatedSL a E) mm))) from rfl,
        hmm, MulEquiv.symm_apply_apply, hind, he ⟨_, hyOd d⟩]
      congr 1
      apply Subtype.ext
      rw [spPaired_eD_conj hDF eF eD heD_eq ⟨yO, hyO⟩ d (hyOd d), hd,
        MulEquiv.apply_symm_apply]
      simp [B]
    have hmodel : LinBlockModel p J (proj m K y) hN :=
      { a := a
        E := E
        fieldE := hEfield
        finiteE := hEfin
        charE := h2E
        two_le := ha2
        k := n * (h : K[X]).natDegree
        cardE := hcard
        notSmall := hnotSmall
        h3 := fun _ => hk2
        h4 := fun _ => hk2
        B := B
        hBn := hBn
        Bpow := hBpow
        e := e
        equiv := hequiv }
    exact Or.inl ⟨hmodel⟩


theorem spPairedBlockModel_holds : SpPairedBlockModel :=
  spPairedBlockModel_of_dvd spPairedBlockModelDvd_holds

theorem spPairedBlockAnalysis_holds : SpPairedBlockAnalysis :=
  spPairedBlockAnalysis_of_model spPairedBlockModel_holds

theorem sympComponentBlockAnalysis_of_selfDualAnalysis
    (hself : SpSelfDualBlockAnalysis) : SympComponentBlockAnalysis :=
  sympComponentBlockAnalysis_of spPairedBlockAnalysis_holds hself

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
