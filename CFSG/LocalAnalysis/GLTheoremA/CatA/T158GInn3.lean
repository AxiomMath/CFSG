module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158GInn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158CoreField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09TD4G2A
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagPi
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofEvenDesc
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.KFacts.K71TrialityFix
public import CFSG.RankThree.PartOne.KF.F122D4
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxD4Three
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Basic
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Field
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4FieldFrob
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedD4
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4GraphFieldNF
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.D4Aux.Model
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQ
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthAux.Field
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158InnHolds2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic
public import CFSG.RankThree.PartOne.CTP.StdSub
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158G

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Assembly (LargeEvenLabel)
open CFSG.StandardType (markTag markRank markChar markDeg)

theorem t158g_eq_bot_of_perfect_of_solvable {H : Type*} [Group H] [Group.IsSolvable H] (P : Subgroup H)
    (hP : ⁅P, P⁆ = P) : P = ⊥ := by
  obtain ⟨n, hn⟩ := (isSolvable_def H).1 inferInstance
  have key : ∀ k : ℕ, P ≤ derivedSeries H k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      rw [derivedSeries_succ, ← hP]
      exact Subgroup.commutator_mono ih ih
  exact le_bot_iff.1 (hn ▸ key n)

theorem t158g_eq_bot_of_perfect_of_le_solvable {H : Type*} [Group H] {P Q : Subgroup H}
    [Group.IsSolvable ↥Q] (hPQ : P ≤ Q) (hP : ⁅P, P⁆ = P) : P = ⊥ := by
  haveI : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hPQ) (Subgroup.inclusion_injective hPQ)
  haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  have htop := t158g_eq_bot_of_perfect_of_solvable (⊤ : Subgroup ↥P) (by
    have := Group.IsPerfect.commutator_eq_top (G := ↥P)
    rwa [commutator_def] at this)
  rw [eq_bot_iff]
  intro x hx
  have h1 : (⟨x, hx⟩ : ↥P) ∈ (⊥ : Subgroup ↥P) := htop ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at h1 ⊢
  exact congrArg Subtype.val h1

theorem t158g_eight_eq (q : TauCeti.PrimePower) (h : q.card = 8) : q.p = 2 ∧ q.exponent = 3 := by
  have hdvd : q.p ∣ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p q.exponent_pos.ne'
  rw [h] at hdvd
  have h2 : q.p ∣ 2 := q.prime_p.dvd_of_dvd_pow (n := 3) (by norm_num; exact hdvd)
  have hp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h2
  refine ⟨hp, ?_⟩
  have h8 : q.p ^ q.exponent = 8 := (TauCeti.PrimePower.card_def q).symm.trans h
  rw [hp, show (8 : ℕ) = 2 ^ 3 by norm_num] at h8
  exact Nat.pow_right_injective le_rfl h8

theorem t158g_eq_twA_two_three {lab : LargeEvenLabel} (ht : markTag lab = .PSU)
    (hr : markRank lab = 3) (hc : markChar lab = 2) (hf : markDeg lab = 3) :
    lab = ⟨.twA, 2, 3⟩ := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp only [markTag, markRank, markChar, markDeg] at ht hr hc hf <;>
    (try split_ifs at ht hr hc hf) <;> simp_all

section U38


open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.LieType.Chevalley in
theorem t158gU38Core_holds : T158GU38Core := by
  intro Ω _ _ S b L hSn hq hcore hU hb3 hF hL
  classical
  have hSc : GLAPComponent 3 S S := glaPComponent_self_p hq hcore
  have hqP : CFSG.Open.IsQuasisimple (PQuot 3 S) := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hSc
  have hN : ∀ y : Ω, y ∈ Subgroup.normalizer (S : Set Ω) := fun y => by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top y
  obtain ⟨q, hv, hq8, ⟨e8⟩⟩ := CatB.lieIndex_isU3eight hU
  obtain ⟨hp2, he3⟩ := t158g_eight_eq q hq8
  have hm := CFSG.Models.lieModel_twistedA 2 q hv e8
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 2 q
  have hfe : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
  rw [hc, hfe, hp2, he3] at hm
  have hb : CFSG.Blueprint.LieModel (PQuot 3 S ⧸ Subgroup.center (PQuot 3 S)) .PSU (2 + 1) 2 3 :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [CFSG.Blueprint.classicalTags]) hm
  obtain ⟨hperf, lab, hlab, hraw⟩ := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hqP.1 hb
  obtain ⟨-, _, -, -, -, -, -, ht, hr, hc', hf'⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hlab' : lab = ⟨.twA, 2, 3⟩ := t158g_eq_twA_two_three ht hr hc' hf'
  have MU : CFSG.Assembly.LargeEvenMarking (PQuot 3 S) fun lab _ _ _ _ _ => lab = ⟨.twA, 2, 3⟩ :=
    ⟨hperf, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, hlab'⟩) hraw⟩
  set β := MI.indAut 3 S b (hN b) with hβdef
  have hmk' : CFSG.Assembly.LargeEvenMarking (PQuot 3 S) fun lab _ _ I F θ => lab = ⟨.twA, 2, 3⟩ ∧
      GLAPrimeField 3 lab I F (GLAInduces θ (indRel 3 S b)) := by
    refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_
      (FP.fieldOn_marking_transport Nat.prime_three (by norm_num) hF MU)
    rintro lab' R' _ I' F' θ' ⟨h1, h2⟩
    exact ⟨h1, h2 (by rw [h1]; exact Or.inl (by decide))⟩
  obtain ⟨-, lab, -, hraw⟩ := hmk'
  obtain ⟨R, _, I, F, -, -, θ, hlab3, -⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst hlab3
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeUnitary] at hraw
  obtain ⟨K, hKf, hKfin, hKcard, -, -, θ, -, -, f, hf, u, hu, hord, hind⟩ := hraw
  letI := hKf
  letI := hKfin
  have e1 : u * f * u⁻¹ = MulAut.congr θ (MI.indAut 3 S b (hN b)) := (MI.induces_indRel_iff (hN b) θ).1 hind
  have hKcard' : Nat.card K = 2 ^ (2 * 3) := by rw [hKcard]; norm_num
  let h : UnitaryFieldData 2 3 K := ⟨Nat.prime_two, by norm_num, hKcard'⟩
  have hd1 : 1 ≤ 2 + 1 := by norm_num
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  let ψ := CFSG.StandardType.InndiagSU.projEquiv h hd1
  have huD : MulAut.congr ψ u ∈ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    CFSG.StandardType.InndiagSU.congr_mem_primeFormD h hd1 hKcard hu
  obtain ⟨σ, hσf⟩ := CFSG.StandardType.RecipeFieldSU.congr_field_eq h hd1 hf
  set fσ := primeFormFieldHom h hC σ with hfσ
  have hn : 3 ≤ 3 := le_rfl
  have hne : ¬(3 = 3 ∧ 2 ^ 3 = 2) := by norm_num
  have hΘσ : ∀ τ : K ≃+* K, primeFormFieldFactor h hC hn hne (primeFormFieldHom h hC τ) = τ := by
    intro τ
    have := primeFormFieldFactor_apply h hC hn hne 1 τ
    rwa [map_one, one_mul] at this
  have hfinj : Function.Injective (primeFormFieldHom h hC) := fun a b hab => by
    rw [← hΘσ a, ← hΘσ b, hab]
  have hσ : orderOf σ = 3 := by
    rw [← orderOf_injective _ hfinj σ, ← hfσ, ← hσf, MulEquiv.orderOf_eq]
    exact hord
  set u' := MulAut.congr ψ u with hu'
  let Φ : PSimple 3 S ≃* primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    (θ.trans ψ).trans (u'⁻¹ : MulAut _)
  have hcongrΦ : ∀ α : MulAut (PSimple 3 S),
      MulAut.congr Φ α = u'⁻¹ * MulAut.congr ψ (MulAut.congr θ α) * u' := by
    intro α
    ext y
    rfl
  have hΦβ : MulAut.congr Φ β = fσ := by
    rw [hcongrΦ, hβdef, ← e1, map_mul, map_mul, map_inv, ← hu', hσf]
    group
  set h₀ := fixSubfield_unitaryFieldData h Nat.prime_three (by decide) hσ with hh₀
  set j := primeSubfieldPSU h Nat.prime_three (by decide) hσ 3 with hj
  have hCJ : ⁅fixSubgroup fσ, fixSubgroup fσ⁆ ≤ j.range :=
    CFSG.HardMathSupport.Dickson.Sec6.I923.commutator_fixed_le_range h hσ
  have h72 : Nat.card (primeFormP h₀ ((1 : GL (Fin 3) (fixSubfield σ)) :
      Matrix (Fin 3) (Fin 3) (fixSubfield σ))) = 72 :=
    card_primeFormP_three_two h₀ (by norm_num)
  haveI : Finite (primeFormP h₀ ((1 : GL (Fin 3) (fixSubfield σ)) :
      Matrix (Fin 3) (Fin 3) (fixSubfield σ))) :=
    Nat.finite_of_card_ne_zero (by rw [h72]; norm_num)
  haveI hsolv₀ : Group.IsSolvable (primeFormP h₀ ((1 : GL (Fin 3) (fixSubfield σ)) :
      Matrix (Fin 3) (Fin 3) (fixSubfield σ))) := isSolvable_of_card_primeFactors_le_two (by
    rw [h72, show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
    decide)
  haveI hsolvJ : Group.IsSolvable ↥j.range :=
    Group.isSolvable_of_surjective (f := j.rangeRestrict) j.rangeRestrict_surjective
  have hap : IsPGroup 3 (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_eq_one hb3
  have hJc := glaPComponent_chevTransfer Nat.prime_three (hN b) hap hL
  have hJperf : ⁅chevTransfer 3 S L, chevTransfer 3 S L⁆ = chevTransfer 3 S L := glaPComponent_perfect hJc
  have hJfix : chevTransfer 3 S L ≤ fixSubgroup β := by
    have h1 := hJc.1
    have h2 : fixSubgroup (chevAut 3 S ⟨b, hN b⟩) = fixSubgroup β := by
      rw [hβdef, T158Core.t158Core_indAut_eq_inv (hN b),
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq]
    rw [h2] at h1
    exact h1
  have hfixΦ : (fixSubgroup β).map (Φ : PSimple 3 S →* _) = fixSubgroup fσ := by
    rw [← hΦβ, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr]
  set T : Subgroup (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    (chevTransfer 3 S L).map (Φ : PSimple 3 S →* _) with hTdef
  have hTperf : ⁅T, T⁆ = T := by rw [hTdef, ← Subgroup.map_commutator, hJperf]
  have hTj : T ≤ j.range := by
    have hTfix : T ≤ fixSubgroup fσ := hfixΦ ▸ Subgroup.map_mono hJfix
    rw [← hTperf]
    exact (Subgroup.commutator_mono hTfix hTfix).trans hCJ
  have hTbot : T = ⊥ := t158g_eq_bot_of_perfect_of_le_solvable hTj hTperf
  have hJbot : chevTransfer 3 S L = ⊥ := by
    rw [hTdef, Subgroup.map_eq_bot_iff_of_injective _ Φ.injective] at hTbot
    exact hTbot
  exact glaPComponent_ne_bot' hJc hJbot

end U38

theorem t158g_twA_of_markTag {lab : LargeEvenLabel}
    (hP : markTag lab = .PSU ∧ markRank lab = 3 ∧ markChar lab = 2) : lab.tag = .twA := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨h1, h2, h3⟩ := hP
  cases t
  case twA => rfl
  case D | twD =>
    simp only [markTag, markRank] at h1 h2
    split_ifs at h1 h2 <;> first | omega | exact absurd h1 (by decide)
  all_goals simp [markTag, markRank, markChar] at h1 h2 h3 ⊢

theorem t158g_A2_of_markTag {lab : LargeEvenLabel}
    (hP : markTag lab = .PSL ∧ markRank lab = 3 ∧ markChar lab = 2) : lab.tag = .A ∧ lab.rank = 2 := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨h1, h2, h3⟩ := hP
  cases t
  case A =>
    simp only [markRank] at h2
    refine ⟨rfl, ?_⟩
    dsimp only at h2 ⊢
    omega
  case D | twD =>
    simp only [markTag, markRank] at h1 h2
    split_ifs at h1 h2 <;> first | omega | exact absurd h1 (by decide)
  all_goals simp [markTag, markRank, markChar] at h1 h2 h3 ⊢

theorem t158g_mem_of_mem_ggInndiag {R : Type} [Group R] {I : Set (MulAut R)}
    (hmul : ∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I) (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I)
    (hinn : ∀ r : R, MulAut.conj r ∈ I) {φ : MulAut R}
    (h : φ ∈ CFSG.StandardType.ggInndiag R I) : φ ∈ I := by
  let Isub : Subgroup (MulAut R) :=
    { carrier := I
      mul_mem' := fun {φ ψ} hφ hψ => hmul φ hφ ψ hψ
      one_mem' := by simpa using hinn 1
      inv_mem' := fun {φ} hφ => hinv φ hφ }
  have : CFSG.StandardType.ggInndiag R I ≤ Isub := by
    refine sup_le ?_ ?_
    · rintro _ ⟨r, rfl⟩
      exact hinn r
    · exact (Subgroup.closure_le Isub).2 fun φ hφ => hφ
  exact this h

section A2


theorem t158g_innDiagOn_of_innAutDerived_A2 {Γ : Type} [Group Γ] {J : Subgroup Γ} {a : Γ}
    (haJ : a ∈ Subgroup.normalizer (J : Set Γ)) (hq : CFSG.Open.IsQuasisimple (PQuot 3 J))
    {t : CFSG.Open.StatedLieTag} {m : ℕ} (ht : t = .PSL ∨ (t = .PSU ∧ 2 ≤ m))
    (hLM : CFSG.Blueprint.LieModel (PSimple 3 J) t 3 2 m)
    (h : MI.indAut 3 J a haJ ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived (PSimple 3 J)) :
    InnDiagOn 3 (Subgroup.zpowers a) J := by
  refine ⟨Subgroup.zpowers_le.2 haJ, ?_⟩
  obtain ⟨hX, lab, hlab, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hLM
  obtain ⟨R₀, _, I₀, F₀, -, -, -, hP⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have hcomm : MI.CAll lab
      (CFSG.StandardType.LargeEvenSimpleGuard CFSG.StandardType.GGInndiagCommEq) := by
    rcases ht with rfl | ⟨rfl, hm⟩
    · obtain ⟨htag, hrank⟩ := t158g_A2_of_markTag ⟨hP.1, hP.2.1, hP.2.2.1⟩
      have hnd : ¬ MI.DerivedLab lab := by
        rintro (h | h) <;> rw [htag] at h <;> exact absurd h (by decide)
      exact (MI.canonAll_iff_legacyAll hlab hnd _).2
        (CFSG.StandardType.largeEvenLabelAll_inndiagComm_linear (Or.inl ⟨htag, by omega⟩))
    · have htag := t158g_twA_of_markTag ⟨hP.1, hP.2.1, hP.2.2.1⟩
      have hnd : ¬ MI.DerivedLab lab := by
        rintro (h | h) <;> rw [htag] at h <;> exact absurd h (by decide)
      exact (MI.canonAll_iff_legacyAll hlab hnd _).2
        (CFSG.StandardType.largeEvenLabelAll_inndiagComm_unitary hlab (Or.inl htag))
  have hbody := MI.canonRawInn' Nat.prime_three (by norm_num) hlab
  refine ⟨hX, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_
    ((hbody.and hcomm) _ hraw)⟩
  rintro R _ I F ⟨⟨hs, hna, θ, -⟩, hb, hc⟩
  refine ⟨hs, hna, θ, fun a' ha' => ?_⟩
  obtain ⟨hmul, hinv, hinn, -⟩ := hb hs hna
  have hEq : CFSG.StandardType.ggInndiag R I = CFSG.StandardType.ggInndiagComm R := hc hs hna
  have ha'N : a' ∈ Subgroup.normalizer (J : Set Γ) := Subgroup.zpowers_le.2 haJ ha'
  refine ⟨MulAut.congr θ (MI.indAut 3 J a' ha'N), ?_, (MI.induces_indRel_iff ha'N θ).2 rfl⟩
  apply t158g_mem_of_mem_ggInndiag hmul hinv hinn
  rw [hEq, CFSG.StandardType.ggInndiagComm_eq_innAutDerived,
    CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
  have e' : MI.indAut 3 J (a ^ k) ha'N = (MI.indAut 3 J a haJ) ^ k := by
    unfold MI.indAut
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by simp [zpow_neg, inv_zpow])
  rw [e']
  exact Subgroup.zpow_mem _ h k

end A2

section TD4

open CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley (Tag TwistTag adjointGroup)
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived mem_innAutDerived_congr
  congr_mem_inner_iff)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

theorem t158g_mul_conj_eq {G : Type*} [Group G] (β : MulAut G) (g : G) :
    β * MulAut.conj g = MulAut.conj (β g) * β := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem t158g_fix_of_conj_mul_pow {R : Type*} [Group R] (hZ : Subgroup.center R = ⊥) {β x : MulAut R} {s : R}
    {j : ℕ} (hxeq : x = MulAut.conj s * β ^ j) (hβx : β * x = x * β) : s ∈ fixSubgroup β := by
  rw [mem_fixSubgroup]
  rw [hxeq] at hβx
  have h2 : MulAut.conj (β s) * β ^ (j + 1) = MulAut.conj s * β ^ (j + 1) := by
    calc MulAut.conj (β s) * β ^ (j + 1) = (β * MulAut.conj s) * β ^ j := by
          rw [t158g_mul_conj_eq β s]
          group
      _ = β * (MulAut.conj s * β ^ j) := by group
      _ = (MulAut.conj s * β ^ j) * β := hβx
      _ = MulAut.conj s * β ^ (j + 1) := by group
  exact CFSG.mulAutConj_injective_of_center_eq_bot hZ (mul_right_cancel h2)

theorem t158g_td4_index {Γ : Type} [Group Γ] {p : ℕ} {S : Subgroup Γ} (h : IsTD4 p S) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      Nonempty (PSimple p S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) := by
  unfold IsTD4 at h
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex h
  cases d with
  | trialityD4 q => exact ⟨q, hv, ⟨e⟩⟩
  | _ => exact hP.elim

theorem t158g_odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [pow_succ]
  exact ⟨2 ^ j - 1, by omega⟩

theorem t158g_twoPart_ordG2 {n : ℕ} (hn : 1 ≤ n) : twoPart (CFSG.Open.ordG2 (2 ^ n)) = 2 ^ (6 * n) := by
  have h6 : Odd (2 ^ (6 * n) - 1) := t158g_odd_two_pow_sub_one (by omega)
  have h2 : Odd (2 ^ (2 * n) - 1) := t158g_odd_two_pow_sub_one (by omega)
  have e : CFSG.Open.ordG2 (2 ^ n) = 2 ^ (6 * n) * ((2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1)) := by
    rw [CFSG.Open.ordG2, ← pow_mul, ← pow_mul, mul_comm n 6, mul_comm n 2, mul_assoc]
  rw [e, FQ.twoPart_two_pow_mul_odd (h6.mul h2)]

theorem t158g_isQuasisimple_of_mulEquiv {G P : Type} [Group G] [Group P] (e : G ≃* P)
    (hs : IsSimpleGroup P) (hperf : Group.IsPerfect P) :
    CFSG.Open.IsQuasisimple G ∧ Subgroup.center G = ⊥ := by
  haveI : IsSimpleGroup G := (MulEquiv.isSimpleGroup_congr e).2 hs
  haveI : Group.IsPerfect G := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI : Nontrivial P := hs.toNontrivial
  obtain ⟨a, b, hab⟩ := Sec8.Item8KFacts2Proof.exists_ne_comm_of_isPerfect hperf
  have hna : ∃ a b : G, a * b ≠ b * a :=
    ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hZ : Subgroup.center G = ⊥ := T156.center_eq_bot_of_simple_noncomm hna
  exact ⟨⟨Group.IsPerfect.commutator_eq_top,
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup⟩, hZ⟩

theorem t158g_lieModel_of_mulEquiv_projImage_slPi {G : Type} [Group G] {π : Bool} {f : ℕ} {F : Type} [Field F]
    [Finite F] (hK : Sec4.PiField π 2 f F) (hf : 2 ≤ f)
    (e : G ≃* ↥(CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ f) F))) :
    ∃ t : CFSG.Open.StatedLieTag, (t = .PSL ∨ (t = .PSU ∧ 2 ≤ f)) ∧
      CFSG.Blueprint.LieModel G t 3 2 f := by
  cases π
  · have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 2 f := by
      refine ⟨Nat.prime_two, by omega, le_rfl, ?_⟩
      intro h
      simp only [Prod.mk.injEq] at h
      have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega
    exact ⟨.PSU, Or.inr ⟨rfl, hf⟩, Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hadm, F, inferInstance,
      inferInstance, by simpa [Sec4.piCard] using hK.card,
      ⟨e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (Sec4.slPi false 3 (2 ^ f) F)).symm⟩⟩⟩
  · have hadm : CFSG.Open.StatedLieAdmissible .PSL 3 2 f := by
      refine ⟨Nat.prime_two, by omega, by norm_num, ?_, ?_⟩
      · intro h
        simp only [Prod.mk.injEq] at h
        omega
      · intro h
        simp only [Prod.mk.injEq] at h
        omega
    exact ⟨.PSL, Or.inl rfl, Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hadm, F, inferInstance,
      inferInstance, by simpa [Sec4.piCard] using hK.card,
      ⟨e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (Sec4.slPi true 3 (2 ^ f) F)).symm⟩⟩⟩

theorem t158g_exists_mulEquiv_projImage_slPi {Y : Type} [Group Y] {β : MulAut Y} {π : Bool} {f : ℕ}
    {F : Type} [Field F] [Finite F] (hK : Sec4.PiField π 2 f F) (hq2 : 2 < 2 ^ f)
    (φ : ↥(fixSubgroup β) ≃* CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ f) F))
    {J : Subgroup Y} (hJC : J ≤ fixSubgroup β) (hJH : J = ⁅fixSubgroup β, fixSubgroup β⁆) :
    ∃ eJ : ↥J ≃* ↥(CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ f) F)),
      ∀ y : ↥J, ((eJ y : ↥(CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ f) F))) :
          Matrix.ProjGenLinGroup (Fin 3) F) =
        (φ ⟨(y : Y), hJC y.2⟩ : Matrix.ProjGenLinGroup (Fin 3) F) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F :=
    fun h => by subst h; exact hK.unitary
  have hSP : CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ f) F) ≤
      CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ f) F) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  have hcomm := Sec13.commutator_projImage_glPi hK hq2
  let g : ↥J →* ↥(CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ f) F)) :=
    φ.toMonoidHom.comp (Subgroup.inclusion hJC)
  have hmem : ∀ y : ↥J, g y ∈
      (CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ f) F)).subgroupOf
        (CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ f) F)) := by
    intro y
    have hycomm : Subgroup.inclusion hJC y ∈ commutator ↥(fixSubgroup β) := by
      rw [← CFSG.StandardType.ggCommutator_subgroupOf (fixSubgroup β)]
      exact hJH ▸ y.2
    have himg : g y ∈ (commutator ↥(fixSubgroup β)).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem _ hycomm
    rw [CFSG.StandardType.ggMap_commutator_of_surjective φ.toMonoidHom φ.surjective, hcomm] at himg
    exact himg
  let fJ : ↥J →* ↥((CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ f) F)).subgroupOf
      (CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ f) F))) := g.codRestrict _ hmem
  have hf_inj : Function.Injective fJ := by
    intro a b hab
    have h1 : g a = g b := congrArg Subtype.val hab
    have h2 : (Subgroup.inclusion hJC a : ↥(fixSubgroup β)) = Subgroup.inclusion hJC b :=
      φ.injective h1
    exact Subtype.ext (congrArg (fun z : ↥(fixSubgroup β) => (z : Y)) h2)
  have hf_surj : Function.Surjective fJ := by
    intro w
    have hw : (w : ↥(CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ f) F))) ∈
        (commutator ↥(fixSubgroup β)).map φ.toMonoidHom := by
      rw [CFSG.StandardType.ggMap_commutator_of_surjective φ.toMonoidHom φ.surjective, hcomm]
      exact w.2
    obtain ⟨z, hz, hwz⟩ := hw
    have hzJ : (z : Y) ∈ J := by
      rw [hJH]
      exact ((CFSG.StandardType.ggCommutatorEquiv (fixSubgroup β)).symm ⟨z, hz⟩).2
    refine ⟨⟨(z : Y), hzJ⟩, ?_⟩
    apply Subtype.ext
    show g ⟨(z : Y), hzJ⟩ = (w : ↥(CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ f) F)))
    have h1 : (Subgroup.inclusion hJC ⟨(z : Y), hzJ⟩ : ↥(fixSubgroup β)) = z := Subtype.ext rfl
    rw [show g ⟨(z : Y), hzJ⟩ = φ (Subgroup.inclusion hJC ⟨(z : Y), hzJ⟩) from rfl, h1]
    exact hwz
  refine ⟨(MulEquiv.ofBijective fJ ⟨hf_inj, hf_surj⟩).trans (Subgroup.subgroupOfEquivOfLe hSP), ?_⟩
  intro y
  rfl

theorem t158g_mem_innAutDerived_of_conj {π : Bool} {f : ℕ} {F : Type} [Field F] [Finite F]
    (hK : Sec4.PiField π 2 f F) (hq2 : 2 < 2 ^ f) {Y : Type} [Group Y]
    (e : Y ≃* CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ f) F))
    {A : GL (Fin 3) F} (hA : A ∈ Sec4.glPi π 3 (2 ^ f) F) {α : MulAut Y}
    (hconj : ∀ y : Y,
      ((e (α y) : CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ f) F)) :
          Matrix.ProjGenLinGroup (Fin 3) F) =
        Matrix.ProjGenLinGroup.mk A * (e y : Matrix.ProjGenLinGroup (Fin 3) F) *
          (Matrix.ProjGenLinGroup.mk A)⁻¹) :
    α ∈ innAutDerived Y := by
  have hβ : MulAut.congr e α ∈ Sec14.inndiagPi π (2 ^ f) F := by
    refine ⟨A, hA, fun m => ?_⟩
    obtain ⟨y, rfl⟩ := e.surjective m
    simpa [MulAut.congr_apply] using hconj y
  cases π
  · rw [CFSG.HardMathSupport.Solomon.Coordinator.inndiagPi_false_eq_innAutDerived hK.unitary hq2] at hβ
    exact (mem_innAutDerived_congr e).1 hβ
  · rw [CFSG.HardMathSupport.Solomon.Coordinator.inndiagPi_true_eq_innAutDerived] at hβ
    exact (mem_innAutDerived_congr e).1 hβ

theorem t158g_mem_innAutDerived_of_isoPGL {Y : Type} [Group Y] {β : MulAut Y} {π : Bool} {f : ℕ}
    {F : Type} [Field F] [Finite F] (hK : Sec4.PiField π 2 f F) (hq2 : 2 < 2 ^ f)
    (φ : ↥(fixSubgroup β) ≃* CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ f) F))
    {J : Subgroup Y} (hJC : J ≤ fixSubgroup β) (hJH : J = ⁅fixSubgroup β, fixSubgroup β⁆)
    {x : MulAut Y} (hxstab : x ∈ CFSG.GroupActions.subgroupStabAut J)
    {s : Y} (hs : s ∈ fixSubgroup β) {j : ℕ} (hxeq : x = MulAut.conj s * β ^ j) :
    centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J ⟨x, hxstab⟩) ∈
      innAutDerived (↥J ⧸ Subgroup.center ↥J) := by
  classical
  obtain ⟨eJ, eJ_apply⟩ := t158g_exists_mulEquiv_projImage_slPi hK hq2 φ hJC hJH
  let α : MulAut ↥J := CFSG.GroupActions.subgroupStabRestrict J ⟨x, hxstab⟩
  have hαy : ∀ y : ↥J, ((α y : ↥J) : Y) = s * (y : Y) * s⁻¹ := by
    intro y
    have hpow : ∀ n : ℕ, (β ^ n) (y : Y) = y := by
      intro n
      have hy : β (y : Y) = y := (mem_fixSubgroup).1 (hJC y.2)
      induction n with
      | zero => rw [pow_zero, MulAut.one_apply]
      | succ n ih => rw [pow_succ, MulAut.mul_apply, hy, ih]
    show ((CFSG.GroupActions.subgroupStabRestrict J ⟨x, hxstab⟩ y : ↥J) : Y) = _
    rw [CFSG.GroupActions.subgroupStabRestrict_apply]
    change x (y : Y) = _
    rw [hxeq, MulAut.mul_apply, hpow j, MulAut.conj_apply]
  have hαeq : ∀ y : ↥J, (⟨(α y : ↥J), hJC (α y).2⟩ : ↥(fixSubgroup β)) =
      ⟨s, hs⟩ * ⟨(y : Y), hJC y.2⟩ * ⟨s, hs⟩⁻¹ := by
    intro y
    apply Subtype.ext
    exact hαy y
  let sH : ↥(fixSubgroup β) := ⟨s, hs⟩
  obtain ⟨A, hA, hAeq⟩ := (φ sH).2
  have hconjJ : ∀ y : ↥J,
      ((eJ (α y) : ↥(CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ f) F))) :
          Matrix.ProjGenLinGroup (Fin 3) F) =
        Matrix.ProjGenLinGroup.mk A * ((eJ y : ↥(CFSG.PGLModel.projImage
          (Sec4.slPi π 3 (2 ^ f) F))) : Matrix.ProjGenLinGroup (Fin 3) F) *
          (Matrix.ProjGenLinGroup.mk A)⁻¹ := by
    intro y
    rw [eJ_apply, eJ_apply]
    calc (φ ⟨(α y : ↥J), hJC (α y).2⟩ : Matrix.ProjGenLinGroup (Fin 3) F)
        = φ (sH * ⟨(y : Y), hJC y.2⟩ * sH⁻¹) := by rw [hαeq y]
      _ = φ sH * φ ⟨(y : Y), hJC y.2⟩ * (φ sH)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
          rfl
      _ = Matrix.ProjGenLinGroup.mk A * φ ⟨(y : Y), hJC y.2⟩ *
            (Matrix.ProjGenLinGroup.mk A)⁻¹ := by
          rw [hAeq]
          rfl
  have hαmem : α ∈ innAutDerived ↥J := t158g_mem_innAutDerived_of_conj hK hq2 eJ hA hconjJ
  exact CFSG.ComponentClassification.PerfectCentralQuotient.centerQuotientHom_mem_innAutDerived hαmem

theorem t158g_exists_centerQuot_equiv {Ω : Type} [Group Ω] [Finite Ω] {S L : Subgroup Ω} {b c : Ω}
    (hbN : b ∈ Subgroup.normalizer (S : Set Ω)) (hcN : c ∈ Subgroup.normalizer (S : Set Ω))
    (hb3 : b ^ 3 = 1) (hL : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L)
    (hcL : c ∈ Subgroup.normalizer (L : Set Ω))
    (hTq : CFSG.Open.IsQuasisimple ↥(chevTransfer 3 S L)) :
    ∃ (hstab : MI.indAut 3 S c hcN ∈ CFSG.GroupActions.subgroupStabAut (chevTransfer 3 S L))
      (ι : PSimple 3 L ≃* (↥(chevTransfer 3 S L) ⧸ Subgroup.center ↥(chevTransfer 3 S L))),
      MulAut.congr ι.symm (centerQuotientHom ↥(chevTransfer 3 S L)
        (CFSG.GroupActions.subgroupStabRestrict (chevTransfer 3 S L) ⟨_, hstab⟩)) =
        MI.indAut 3 L c hcL := by
  have hJK : L ≤ S := hL.1.trans inf_le_left
  have hgS : c⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hcN
  have hgJ : c⁻¹ ∈ Subgroup.normalizer (L : Set Ω) := Subgroup.inv_mem _ hcL
  have hstab : MI.indAut 3 S c hcN ∈ CFSG.GroupActions.subgroupStabAut (chevTransfer 3 S L) :=
    T158Core.t158Core_chevAut_mem_stab hJK hgS hgJ
  have hT1 := glaPComponent_chevTransfer Nat.prime_three hbN (isPGroup_zpowers_of_pow_eq_one hb3) hL
  let π : ↥L →* ↥(chevTransfer 3 S L) :=
    ((chevQuotHom 3 S).comp (Subgroup.inclusion hJK)).codRestrict (chevTransfer 3 S L)
      (fun j => ⟨Subgroup.inclusion hJK j, Subgroup.mem_subgroupOf.2 j.2, rfl⟩)
  have hπval : ∀ j : ↥L, ((π j : ↥(chevTransfer 3 S L)) : PSimple 3 S) =
      chevQuotHom 3 S (Subgroup.inclusion hJK j) := fun j => rfl
  have hπ : Function.Surjective π := by
    rintro ⟨t, k, hk, rfl⟩
    exact ⟨⟨k, Subgroup.mem_subgroupOf.1 hk⟩, rfl⟩
  obtain ⟨ι, hι⟩ := CFSG.LocalAnalysis.GLTheoremA.I141F.u9_exists_pSimple_equiv_centerQuot
    Nat.prime_three (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL) hTq
    (isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hT1)) π hπ
  refine ⟨hstab, ι, ?_⟩
  ext s
  obtain ⟨j, rfl⟩ := chevQuotHom_surjective 3 L s
  set j' : ↥L := L.normalizerMonoidHom ⟨c⁻¹, hgJ⟩ j with hj'
  have h1 : ι (chevQuotHom 3 L j) = QuotientGroup.mk (π j) := hι j
  have h5 : ι (chevQuotHom 3 L j') = QuotientGroup.mk (π j') := hι j'
  have h2 : CFSG.GroupActions.subgroupStabRestrict (chevTransfer 3 S L) ⟨_, hstab⟩ (π j) = π j' := by
    apply Subtype.ext
    rw [CFSG.GroupActions.subgroupStabRestrict_apply, hπval j, hπval j']
    change chevAut 3 S ⟨c⁻¹, hgS⟩ (chevQuotHom 3 S (Subgroup.inclusion hJK j)) = _
    rw [chevAut_chevQuotHom]
    congr 1
  have h3 : MI.indAut 3 L c hcL (chevQuotHom 3 L j) = chevQuotHom 3 L j' :=
    chevAut_chevQuotHom 3 L ⟨c⁻¹, hgJ⟩ j
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_symm, h1,
    h3, MulEquiv.symm_apply_eq, h5, ← h2]
  exact CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk _ (π j)

theorem t158g_indAut_mem_innAutDerived_of_restrict {Ω : Type} [Group Ω] [Finite Ω] {S L : Subgroup Ω}
    {b c : Ω} (hbN : b ∈ Subgroup.normalizer (S : Set Ω)) (hcN : c ∈ Subgroup.normalizer (S : Set Ω))
    (hb3 : b ^ 3 = 1) (hL : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L)
    (hcL : c ∈ Subgroup.normalizer (L : Set Ω))
    (hTq : CFSG.Open.IsQuasisimple ↥(chevTransfer 3 S L))
    (hmem : ∀ hstab : MI.indAut 3 S c hcN ∈ CFSG.GroupActions.subgroupStabAut (chevTransfer 3 S L),
      centerQuotientHom ↥(chevTransfer 3 S L)
          (CFSG.GroupActions.subgroupStabRestrict (chevTransfer 3 S L) ⟨_, hstab⟩) ∈
        innAutDerived (↥(chevTransfer 3 S L) ⧸ Subgroup.center ↥(chevTransfer 3 S L))) :
    MI.indAut 3 L c hcL ∈ innAutDerived (PSimple 3 L) := by
  obtain ⟨hstab, ι, hν⟩ := t158g_exists_centerQuot_equiv hbN hcN hb3 hL hcL hTq
  rw [← hν]
  exact (mem_innAutDerived_congr ι.symm).2 (hmem hstab)

section Model


theorem t158g_td4_pgl_finish {Ω : Type} [Group Ω] [Finite Ω] {S L : Subgroup Ω} {b c : Ω}
    (hbN : b ∈ Subgroup.normalizer (S : Set Ω)) (hcN : c ∈ Subgroup.normalizer (S : Set Ω))
    (hb3 : b ^ 3 = 1) (hL : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L)
    (hcL : c ∈ Subgroup.normalizer (L : Set Ω))
    {s : PSimple 3 S} (hs : s ∈ fixSubgroup (MI.indAut 3 S b hbN)) {j : ℕ}
    (hxeq : MI.indAut 3 S c hcN = MulAut.conj s * MI.indAut 3 S b hbN ^ j)
    {π : Bool} {f : ℕ} {F : Type} [Field F] [Finite F] (hK : Sec4.PiField π 2 f F) (hf : 2 ≤ f)
    (φ : ↥(fixSubgroup (MI.indAut 3 S b hbN)) ≃* CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ f) F)) :
    InnDiagOn 3 (Subgroup.zpowers c) L := by
  classical
  set β := MI.indAut 3 S b hbN with hβdef
  have hq2 : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  have hap : IsPGroup 3 (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_eq_one hb3
  have hJc := glaPComponent_chevTransfer Nat.prime_three hbN hap hL
  have hfixβ : fixSubgroup (chevAut 3 S ⟨b, hbN⟩) = fixSubgroup β := by
    rw [hβdef, T158Core.t158Core_indAut_eq_inv hbN,
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq]
  rw [hfixβ] at hJc
  have hCC : (⁅fixSubgroup β, fixSubgroup β⁆ : Subgroup (PSimple 3 S)) ≤ fixSubgroup β :=
    Subgroup.commutator_le.mpr fun a ha b hb => (fixSubgroup β).mul_mem
      ((fixSubgroup β).mul_mem ((fixSubgroup β).mul_mem ha hb) ((fixSubgroup β).inv_mem ha))
      ((fixSubgroup β).inv_mem hb)
  have hsP := Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
  have hpP := Sec13.isPerfect_projImage_slPi hK hq2
  obtain ⟨eCC, -⟩ := t158g_exists_mulEquiv_projImage_slPi hK hq2 φ hCC rfl
  have hsCC : IsSimpleGroup ↥(⁅fixSubgroup β, fixSubgroup β⁆ : Subgroup (PSimple 3 S)) :=
    (MulEquiv.isSimpleGroup_congr eCC).2 hsP
  have hJH : chevTransfer 3 S L = ⁅fixSubgroup β, fixSubgroup β⁆ :=
    T158Core.t158Core_eq_commutator_of_glaPComponent hJc hsCC (glaPComponent_ne_bot' hJc)
  obtain ⟨eJ, -⟩ := t158g_exists_mulEquiv_projImage_slPi hK hq2 φ hJc.1 hJH
  obtain ⟨hTq, hZ⟩ := t158g_isQuasisimple_of_mulEquiv eJ hsP hpP
  have hmem := t158g_indAut_mem_innAutDerived_of_restrict hbN hcN hb3 hL hcL hTq
    (fun hstab => t158g_mem_innAutDerived_of_isoPGL hK hq2 φ hJc.1 hJH hstab hs hxeq)
  obtain ⟨e1⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hbN hap hL
  obtain ⟨e2⟩ := I141F.centerQuot_equiv_pSimple Nat.prime_three hJc hTq
  let eL : PSimple 3 L ≃* ↥(CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ f) F)) :=
    e1.trans (e2.symm.trans (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eJ))
  obtain ⟨t, ht, hLM⟩ := t158g_lieModel_of_mulEquiv_projImage_slPi hK hf eL
  exact t158g_innDiagOn_of_innAutDerived_A2 hcL (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL) ht hLM
    hmem

theorem t158gTD4Core_holds : T158GTD4Core := by
  intro Ω _ _ S b c L hSn hq hcore hT hchev hb3 hc3 hbc hnon hG2 _ hL _ hcL
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hSc : GLAPComponent 3 S S := glaPComponent_self_p hq hcore
  have hqP : CFSG.Open.IsQuasisimple (PQuot 3 S) := isQuasisimple_pQuot_of_glaPComponent hp hSc
  have hN : ∀ y : Ω, y ∈ Subgroup.normalizer (S : Set Ω) := fun y => by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top y
  have hcen : Subgroup.center (PSimple 3 S) = ⊥ := Y10F.center_centerQuot_eq_bot hqP
  set β := MI.indAut 3 S b (hN b) with hβdef
  set x := MI.indAut 3 S c (hN c) with hxdef
  have hβ3 : β ^ 3 = 1 := T156.indAut_pow_eq_one (hN b) hb3
  have hx3 : x ^ 3 = 1 := T156.indAut_pow_eq_one (hN c) hc3
  have hβx : β * x = x * β := by
    have h3 : MI.indAut 3 S (b * c) (Subgroup.mul_mem _ (hN b) (hN c)) =
        MI.indAut 3 S (c * b) (Subgroup.mul_mem _ (hN c) (hN b)) := T156.indAut_congr hbc _ _
    rw [T156.indAut_mul (hN b) (hN c), T156.indAut_mul (hN c) (hN b)] at h3
    exact h3.symm
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 S) := fun h =>
    hnon.2 (MI.inner_innDiag_any hSc hchev hnon.1 ((MI.indAut_mem_inner_iff_any hqP hnon.1).1 h))
  have hfixβ : fixSubgroup (chevAut 3 S ⟨b, hN b⟩) = fixSubgroup β := by
    rw [hβdef, T158Core.t158Core_indAut_eq_inv (hN b),
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq]
  obtain ⟨q, hv, ⟨eS⟩⟩ := t158g_td4_index hT
  have hq2 : q.p = 2 := td4g2_p_two hv eS hchev
  obtain ⟨K, hKf, hKfin, σ, hK, hσ, ⟨Θ, hker⟩, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  letI := hKf
  letI := hKfin
  have hn : 1 ≤ q.exponent := q.exponent_pos
  rw [hq2] at hK hσ
  let e : PSimple 3 S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := eS.trans eC
  let Θ' : MulAut (PSimple 3 S) →* (K ≃+* K) := Θ.comp (MulAut.congr e).toMonoidHom
  have hker' : ∀ α : MulAut (PSimple 3 S),
      Θ' α = 1 ↔ α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 S) := by
    intro α
    rw [← congr_mem_inner_iff e α]
    change Θ (MulAut.congr e α) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hker]
    rfl
  haveI : IsCyclic (K ≃+* K) := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun f : K ≃+* K => (f : K → K)) (fun f g h => RingEquiv.ext (congrFun h))
  have hΘβ1 : Θ' β ≠ 1 := fun h => hβout ((hker' β).1 h)
  obtain ⟨j, -, hj⟩ := T158Core.t158Core_pow_of_cyclic (a := Θ' β) (b := Θ' x)
    (by rw [← map_pow, hβ3, map_one]) hΘβ1 (by rw [← map_pow, hx3, map_one])
  obtain ⟨s, hs⟩ : x * (β ^ j)⁻¹ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 S) :=
    (hker' _).1 (by rw [map_mul, map_inv, map_pow, ← hj, mul_inv_cancel])
  have hxeq : x = MulAut.conj s * β ^ j := by
    rw [hs]
    group
  have hsfix : s ∈ fixSubgroup β := t158g_fix_of_conj_mul_pow hcen hxeq hβx
  set φ := MulAut.congr e β with hφdef
  have hφ3 : φ ^ 3 = 1 := by rw [hφdef, ← map_pow, hβ3, map_one]
  have hφout : ¬ KFacts.IsInnerAut φ := fun h => hβout ((congr_mem_inner_iff e β).1 h)
  let eF : ↥(fixSubgroup β) ≃* ↥(fixSubgroup φ) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupCongrEquiv e β
  have hfixφ : fixSubgroup φ = Sec4.autFix φ := Subgroup.ext fun _ => Iff.rfl
  rcases Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hn hK hσ hφ3 hφout with
    ⟨ψ, hψ⟩ | he₂
  ·
    exfalso
    apply hG2
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := q.exponent * 3)
      (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
    obtain ⟨eG⟩ := KFacts.nonempty_fixedPoints_fieldActor_mulEquiv_g2 σ (ringChar.eq K 2)
    obtain ⟨γ, hγ, hφγ⟩ : ∃ γ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        fixSubgroup γ = (fieldActor (t := TwistTag.D4) σ σ).toMonoidHom.eqLocus (MonoidHom.id _) ∧
          φ = MulAut.congr ψ γ := by
      rcases hψ with h | h
      · exact ⟨fieldActor σ σ, rfl, h.trans (MulEquiv.ext fun _ => rfl)⟩
      · refine ⟨(fieldActor σ σ)⁻¹, Subgroup.ext fun y => ?_, h.trans (MulEquiv.ext fun _ => rfl)⟩
        show (fieldActor (t := TwistTag.D4) σ σ)⁻¹ y = y ↔ fieldActor σ σ y = y
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
        exact eq_comm
    have hk := CFSG.RankThree.PartOne.card_fixSubfield_cube_row Nat.prime_two hn hK σ hσ
    have hcard : Nat.card ↥(fixSubgroup β) = CFSG.Open.ordG2 (2 ^ q.exponent) := by
      have h1 : fixSubgroup φ = fixSubgroup (MulAut.congr ψ γ) := by rw [hφγ]
      rw [Nat.card_congr eF.toEquiv, h1,
        Nat.card_congr (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupCongrEquiv ψ γ).symm.toEquiv,
        hγ, Nat.card_congr eG.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk]
    have h12 : (Nat.card (PSimple 3 S)).factorization 2 = 12 * q.exponent := by
      have h := (td4g2_order hv eS).2
      rwa [hq2] at h
    have hfn : FP.fixNum β = Nat.card ↥(fixSubgroup β) := by
      rw [FP.fixNum_eq_card_fixSub, hβdef, FR.fixSub_indAut (hN b), hfixβ]
    rw [FP.centCard2_eq_twoPart_fixNum (hN b) (FP.odd_card_center_pQuot hp hp2 S),
      FP.card2_eq_twoPart_card_pSimple hp hp2 S, ← hβdef, hfn, hcard, t158g_twoPart_ordG2 hn]
    unfold twoPart
    rw [h12, show 12 * q.exponent = 6 * q.exponent + 6 * q.exponent by ring, pow_add, Nat.sqrt_eq]
  ·
    obtain ⟨e₂⟩ := he₂
    let eA : ↥(fixSubgroup β) ≃* ↥(Sec4.autFix (MulAut.conj (Sec8.d4TrialityY0Elt K σ) * fieldActor σ σ)) :=
      eF.trans ((MulEquiv.subgroupCongr hfixφ).trans e₂)
    rcases Nat.even_or_odd q.exponent with hne | hno
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := Sec8.kF82D4SecondCentY0Even_holds q.exponent hne hn K σ hK hσ
      have hf2 : 2 ≤ q.exponent := by
        obtain ⟨k, hk⟩ := hne
        omega
      exact t158g_td4_pgl_finish (hN b) (hN c) hb3 hL hcL hsfix hxeq (π := true) ⟨Nat.prime_two, hn, hF⟩ hf2
        (eA.trans e₃)
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := Sec8.kF82D4SecondCentY0_holds q.exponent hno K σ hK hσ
      have hPi : Sec4.PiField false 2 q.exponent F := ⟨Nat.prime_two, hn, hF⟩
      by_cases h1 : q.exponent = 1
      ·
        exfalso
        haveI : Group.IsSolvable ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ q.exponent) F)) :=
          Sec13.isSolvable_projImage_glPi_two hPi (by simp [h1])
        haveI : Group.IsSolvable ↥(fixSubgroup β) :=
          Group.isSolvable_of_isSolvable_injective (f := (eA.trans e₃).toMonoidHom) (eA.trans e₃).injective
        have hJc := glaPComponent_chevTransfer hp (hN b) (isPGroup_zpowers_of_pow_eq_one hb3) hL
        rw [hfixβ] at hJc
        exact glaPComponent_ne_bot' hJc
          (t158g_eq_bot_of_perfect_of_le_solvable hJc.1 (glaPComponent_perfect hJc))
      · have hf3 : 2 ≤ q.exponent := by
          obtain ⟨k, hk⟩ := hno
          omega
        exact t158g_td4_pgl_finish (hN b) (hN c) hb3 hL hcL hsfix hxeq hPi hf3 (eA.trans e₃)

end Model

end TD4

section D4

open CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley (Tag TwistTag adjointGroup)
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor fixSubfield exactNormalAut entrywiseAdjointAut
  fixedFieldImage entrywiseFixedGroup)
open CFSG.HardMathSupport.Lang.D4Three (d4Graph)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived mem_innAutDerived_congr
  congr_mem_inner_iff)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open scoped commutatorElement

theorem t158g_d4_index {X : Type} [Group X] (h : catalogIs X isD4any) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.p = 2 ∧
      Nonempty (X ≃* TauCeti.ValidLieTypeIndex.Group ⟨.D 4 q, hv⟩) := by
  unfold isD4any at h
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex h
  cases d with
  | D r q =>
    rcases r with _ | _ | _ | _ | _ | r
    all_goals try exact hP.elim
    exact ⟨q, hv, hP, ⟨e⟩⟩
  | _ => exact hP.elim

theorem t158g_four_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem t158g_fixSubgroup_sq_eq {G : Type*} [Group G] {α : MulAut G} (h : (α ^ 2) ^ 2 = α) :
    fixSubgroup α = fixSubgroup (α ^ 2) := by
  ext x
  rw [mem_fixSubgroup, mem_fixSubgroup]
  constructor
  · intro hx
    rw [pow_two, MulAut.mul_apply, hx, hx]
  · intro hx
    rw [← h, pow_two (α ^ 2), MulAut.mul_apply, hx, hx]

theorem t158g_twoPart_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : twoPart (a * b) = twoPart a * twoPart b := by
  unfold twoPart
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply, pow_add]

theorem t158g_odd_of_twoPart_mul_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : twoPart (a * b) = twoPart a) :
    Odd b := by
  rw [t158g_twoPart_mul ha hb] at h
  have hpos : 0 < twoPart a := by
    unfold twoPart
    positivity
  have h1 : twoPart b = 1 := by
    have h' : twoPart a * twoPart b = twoPart a * 1 := by rw [mul_one]; exact h
    exact Nat.eq_of_mul_eq_mul_left hpos h'
  unfold twoPart at h1
  have h0 : b.factorization 2 = 0 := by
    have h2 : (2 : ℕ) ^ b.factorization 2 = 2 ^ 0 := by rw [h1, pow_zero]
    exact Nat.pow_right_injective le_rfl h2
  rw [Nat.factorization_eq_zero_iff] at h0
  rcases h0 with h0 | h0 | h0
  · exact absurd Nat.prime_two h0
  · exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h0)
  · exact absurd h0 hb

theorem t158g_twoPart_inf_of_odd_index {P : Type} [Group P] [Finite P] {C J D : Subgroup P}
    (hJC : J ≤ C) (hJn : ∀ f ∈ C, ∀ t ∈ J, f * t * f⁻¹ ∈ J)
    (hodd : twoPart (Nat.card C) = twoPart (Nat.card J)) (hDC : D ≤ C) :
    twoPart (Nat.card ↥(J ⊓ D)) = twoPart (Nat.card D) := by
  classical
  haveI hJn' : (J.subgroupOf C).Normal :=
    ⟨fun t ht f => Subgroup.mem_subgroupOf.2 (hJn f f.2 t (Subgroup.mem_subgroupOf.1 ht))⟩
  have h1 : (J.subgroupOf C).relIndex (D.subgroupOf C) ∣ (J.subgroupOf C).index :=
    Subgroup.relIndex_dvd_index_of_normal _ _
  rw [Subgroup.relIndex_subgroupOf hDC] at h1
  have h2 : Nat.card ↥(J.subgroupOf C) * (J.subgroupOf C).index = Nat.card ↥C := Subgroup.card_mul_index _
  have h3 : Nat.card ↥(J.subgroupOf C) = Nat.card ↥J := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv
  rw [h3] at h2
  have hJ0 : Nat.card ↥J ≠ 0 := Nat.card_pos.ne'
  have hr0 : (J.subgroupOf C).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrodd : Odd (J.subgroupOf C).index := by
    refine t158g_odd_of_twoPart_mul_eq hJ0 hr0 ?_
    rw [h2]
    exact hodd
  have hsodd : Odd (J.relIndex D) := hrodd.of_dvd_nat h1
  have h4 : J.relIndex D * Nat.card ↥(J ⊓ D) = Nat.card ↥D := Subgroup.relIndex_mul_card J D
  rw [← h4, FP.twoPart_mul_odd hsodd Nat.card_pos.ne']

theorem t158g_twoPart_mixed {P : Type} [Group P] [Finite P] {βa βg : MulAut P} {Ja Jg : Subgroup P} {n : ℕ}
    (hn : 1 ≤ n) (ha1 : Ja = fixSubgroup βa) (ha2 : twoPart (Nat.card Ja) = 2 ^ (4 * n))
    (ha3 : twoPart (Nat.card ↥(Ja ⊓ fixSubgroup βg)) ^ 3 = twoPart (Nat.card Ja))
    (hg0 : Jg ≤ fixSubgroup βg) (hg1 : ∀ f ∈ fixSubgroup βg, ∀ t ∈ Jg, f * t * f⁻¹ ∈ Jg)
    (hg2 : twoPart (Nat.card ↥(fixSubgroup βg)) = twoPart (Nat.card Jg))
    (hg3 : twoPart (Nat.card Jg) = 2 ^ (6 * n) ∨ twoPart (Nat.card Jg) = 2 ^ (3 * n))
    (hg4 : twoPart (Nat.card ↥(Jg ⊓ fixSubgroup βa)) ^ 3 = twoPart (Nat.card Jg)) : False := by
  set D : Subgroup P := fixSubgroup βa ⊓ fixSubgroup βg with hDdef
  have hD1 : Ja ⊓ fixSubgroup βg = D := by rw [ha1]
  have hD2 : Jg ⊓ fixSubgroup βa = Jg ⊓ D := by
    ext x
    simp only [Subgroup.mem_inf, hDdef]
    exact ⟨fun h => ⟨h.1, h.2, hg0 h.1⟩, fun h => ⟨h.1, h.2.1⟩⟩
  have h2 := t158g_twoPart_inf_of_odd_index hg0 hg1 hg2 (inf_le_right : D ≤ fixSubgroup βg)
  rw [hD1] at ha3
  rw [hD2, h2] at hg4
  have h4 : (2 : ℕ) ^ (4 * n) = twoPart (Nat.card Jg) := by rw [← ha2, ← ha3, hg4]
  rcases hg3 with h | h
  · rw [h] at h4
    have := Nat.pow_right_injective le_rfl h4
    omega
  · rw [h] at h4
    have := Nat.pow_right_injective le_rfl h4
    omega

theorem t158g_modThree {π : Bool} {n : ℕ} (h : cond π (Even n) (Odd n)) : Sec4.ModThree π (2 ^ n) := by
  cases π
  · obtain ⟨m, rfl⟩ := h
    simp only [Sec4.ModThree, Bool.cond_false]
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  · obtain ⟨m, rfl⟩ := h
    simp only [Sec4.ModThree, Bool.cond_true]
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num

theorem t158g_pow_three_of_conj_mul_pow {R : Type*} [Group R] (hZ : Subgroup.center R = ⊥) {β x : MulAut R}
    {s : R} {j : ℕ} (hxeq : x = MulAut.conj s * β ^ j) (hs : β s = s) (hβ3 : β ^ 3 = 1) (hx3 : x ^ 3 = 1) :
    s ^ 3 = 1 := by
  have hc : Commute (MulAut.conj s) (β ^ j) :=
    (show Commute (MulAut.conj s) β from t158g_conj_comm hs).pow_right j
  have h1 : x ^ 3 = MulAut.conj (s ^ 3) := by
    rw [hxeq, hc.mul_pow, ← pow_mul, mul_comm j 3, pow_mul, hβ3, one_pow, mul_one, map_pow]
  rw [hx3] at h1
  exact t158g_eq_one_of_conj_eq_one hZ h1.symm

theorem t158g_isQuasisimple_of_simple {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) : CFSG.Open.IsQuasisimple G ∧ Subgroup.center G = ⊥ := by
  haveI := hs
  have hZ : Subgroup.center G = ⊥ := T156.center_eq_bot_of_simple_noncomm hna
  have hperf : commutator G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      apply hab
      have h1 : ⁅a, b⁆ ∈ commutator G := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at h1
      exact (commutatorElement_eq_one_iff_mul_comm).1 h1
    · exact h
  exact ⟨⟨hperf, ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup⟩, hZ⟩

theorem t158g_conj_mem_commutator {G : Type*} [Group G] {C : Subgroup G} {f t : G} (hf : f ∈ C)
    (ht : t ∈ (⁅C, C⁆ : Subgroup G)) : f * t * f⁻¹ ∈ (⁅C, C⁆ : Subgroup G) := by
  have hC : C.map (MulAut.conj f).toMonoidHom = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact C.mul_mem (C.mul_mem hf hy) (C.inv_mem hf)
    · intro hx
      refine ⟨f⁻¹ * x * f, C.mul_mem (C.mul_mem (C.inv_mem hf) hx) hf, ?_⟩
      show f * (f⁻¹ * x * f) * f⁻¹ = x
      group
  have h := Subgroup.mem_map_of_mem (MulAut.conj f).toMonoidHom ht
  rw [Subgroup.map_commutator, hC] at h
  exact h

theorem t158g_conj_pow_transport {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {β β' : MulAut X} {s : Y}
    {j : ℕ} (h : MulAut.congr e β' = MulAut.conj s * MulAut.congr e β ^ j) :
    β' = MulAut.conj (e.symm s) * β ^ j := by
  apply (MulAut.congr e).injective
  rw [map_mul, map_pow, h, MI.congr_conj, MulEquiv.apply_symm_apply]

theorem t158g_noncomm_of_glaPComponent {G : Type} [Group G] [Finite G] {X J : Subgroup G}
    (hJ : GLAPComponent 3 X J) : ∃ a b : ↥J, a * b ≠ b * a := by
  obtain ⟨-, a, b, hab⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hJ
  obtain ⟨a', rfl⟩ := chevQuotHom_surjective 3 J a
  obtain ⟨b', rfl⟩ := chevQuotHom_surjective 3 J b
  exact ⟨a', b', fun h => hab (by rw [← map_mul, ← map_mul, h])⟩

theorem t158g_fixNum_card_transfer {Ω : Type} [Group Ω] [Finite Ω] {S L : Subgroup Ω} {b c : Ω}
    (hbN : b ∈ Subgroup.normalizer (S : Set Ω)) (hcN : c ∈ Subgroup.normalizer (S : Set Ω))
    (hb3 : b ^ 3 = 1) (hL : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L)
    (hcL : c ∈ Subgroup.normalizer (L : Set Ω))
    (hTq : CFSG.Open.IsQuasisimple ↥(chevTransfer 3 S L))
    (hZ : Subgroup.center ↥(chevTransfer 3 S L) = ⊥) :
    FP.fixNum (MI.indAut 3 L c hcL) =
        Nat.card ↥(chevTransfer 3 S L ⊓ fixSubgroup (MI.indAut 3 S c hcN)) ∧
      Nat.card (PSimple 3 L) = Nat.card ↥(chevTransfer 3 S L) := by
  classical
  obtain ⟨hstab, ι, hν⟩ := t158g_exists_centerQuot_equiv hbN hcN hb3 hL hcL hTq
  set J := chevTransfer 3 S L with hJ
  set ρ := CFSG.GroupActions.subgroupStabRestrict J ⟨_, hstab⟩ with hρ
  let eQ : (↥J ⧸ Subgroup.center ↥J) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hmk : ∀ z : ↥J, eQ (QuotientGroup.mk z) = z := fun z => rfl
  have hQ : MulAut.congr eQ (centerQuotientHom ↥J ρ) = ρ := by
    refine MulEquiv.ext fun x => ?_
    have hx : x = eQ (QuotientGroup.mk x) := (hmk x).symm
    rw [hx, T158Core.t158Core_congr_apply_apply]
    have h1 : centerQuotientHom ↥J ρ (QuotientGroup.mk x) = QuotientGroup.mk (ρ x) :=
      CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk ρ x
    rw [h1, hmk, hmk]
  have hfix1 : FP.fixNum (centerQuotientHom ↥J ρ) = FP.fixNum ρ := by
    have h := FP.fixNum_congr eQ (centerQuotientHom ↥J ρ)
    rw [hQ] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · rw [← hν, FP.fixNum_congr, hfix1]
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : ↥J) : PSimple 3 S), (x : ↥J).2, ?_⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have h1 : ((CFSG.GroupActions.subgroupStabRestrict J ⟨_, hstab⟩ (x : ↥J) : ↥J) : PSimple 3 S) =
          ((x : ↥J) : PSimple 3 S) := congrArg Subtype.val x.2
      rw [CFSG.GroupActions.subgroupStabRestrict_apply] at h1
      exact mem_fixSubgroup.2 h1
    · apply Subtype.ext
      show ((CFSG.GroupActions.subgroupStabRestrict J ⟨_, hstab⟩ ⟨y, y.2.1⟩ : ↥J) : PSimple 3 S) = y
      rw [CFSG.GroupActions.subgroupStabRestrict_apply]
      exact mem_fixSubgroup.1 y.2.2
  · rw [Nat.card_congr ι.toEquiv, Nat.card_congr eQ.toEquiv]

section D4Model


theorem t158g_d4_model {X : Type} [Group X] (h : catalogIs X isD4any) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 1 ≤ n ∧ Nat.card F = 2 ^ n ∧
      Nonempty (X ≃* adjointGroup Tag.D4 F) := by
  obtain ⟨q, hv, hq2, ⟨eS⟩⟩ := t158g_d4_index h
  let F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)
  haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hFcard : Nat.card F = 2 ^ q.exponent := by
    change Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) = 2 ^ q.exponent
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.LieTypeIndex.characteristic_D, TauCeti.LieTypeIndex.fieldExponent_D, hq2]
  exact ⟨q.exponent, F, inferInstance, inferInstance, q.exponent_pos, hFcard,
    ⟨eS.trans ((CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv).trans
      (CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F).some)⟩⟩

theorem t158g_d4_fix_entrywise_equiv {K : Type} [Field K] [Finite K] (hK : ringChar K = 2) (T : K ≃+* K) :
    Nonempty (↥(fixSubgroup (entrywiseAdjointAut Tag.D4 T)) ≃* adjointGroup Tag.D4 (fixSubfield T)) := by
  have heq := CFSG.LieType.Chevalley.entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two
    (τ := Tag.D4) (Or.inr (Or.inr (Or.inl rfl))) hK T
  have hle : fixedFieldImage Tag.D4 T ≤ adjointGroup Tag.D4 K := fun g hg =>
    (show g ∈ entrywiseFixedGroup Tag.D4 T from heq ▸ hg).1
  have hfix : fixSubgroup (entrywiseAdjointAut Tag.D4 T) =
      (fixedFieldImage Tag.D4 T).subgroupOf (adjointGroup Tag.D4 K) := by
    rw [← heq]
    ext g
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨g.2, congrArg Subtype.val h⟩
    · intro h
      exact Subtype.ext h.2
  rw [hfix]
  exact ⟨(Subgroup.subgroupOfEquivOfLe hle).trans (CFSG.LieType.Chevalley.fixedFieldImageEquiv T).symm⟩

theorem t158g_d4_field_fix {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    {α : MulAut (adjointGroup Tag.D4 F)} (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 F)
    (a : Fin Tag.D4.rank → Fˣ) {σ : F ≃+* F} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 F a σ 0 * d4Graph F 0)) :
    ∃ (d : ℕ) (k : Type) (_ : Field k) (_ : Finite k), 1 ≤ d ∧ d * 3 = n ∧ Nat.card k = 2 ^ d ∧
      Nonempty (↥(fixSubgroup α) ≃* adjointGroup Tag.D4 k) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hF
  have hr2 : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨d, T, hd0, hdf, hT, hT3, hσT⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_frobenius_of_cube Nat.prime_two hn F hF σ hσ3 hσ1
  rw [CFSG.HardMathSupport.Lang.E6Descent.d4Graph_zero, mul_one] at hα
  have hK4 : 4 ≤ Nat.card F := by
    rw [hF]
    exact t158g_four_le_two_pow (by omega)
  have hKd : Nat.card F = (2 ^ d) ^ 3 := by rw [hF, ← pow_mul, hdf]
  have hfix : Nat.card (fixSubfield T) = 2 ^ d :=
    CFSG.RankThree.PartOne.card_fixSubfield_cube_row Nat.prime_two hd0 hKd T hT
  haveI : Finite (fixSubfield T) := Subtype.finite
  obtain ⟨eT⟩ := t158g_d4_fix_entrywise_equiv hr2 T
  have key : ∀ (β : MulAut (adjointGroup Tag.D4 F)) (g' : adjointGroup Tag.D4 F)
      (a' : Fin Tag.D4.rank → Fˣ), β = MulAut.conj g' * exactNormalAut Tag.D4 F a' T 0 → β ^ 3 = 1 →
      Nonempty (↥(fixSubgroup β) ≃* adjointGroup Tag.D4 (fixSubfield T)) := by
    intro β g' a' hβ hβ3
    obtain ⟨ψ, hψ⟩ := CFSG.HardMathSupport.Lang.E6Descent.exists_conj_eq_entrywiseAdjointAut_D4 hF hK4 hd0 hdf
      T hT g' a' β hβ hβ3
    exact ⟨((CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupConjEquiv ψ β).trans
      (MulEquiv.subgroupCongr (by rw [hψ]))).trans eT⟩
  refine ⟨d, fixSubfield T, inferInstance, inferInstance, hd0, hdf, hfix, ?_⟩
  rcases hσT with hσ | hσ
  · rw [hσ] at hα
    exact key α g a hα hα3
  · obtain ⟨g', a', hα2⟩ := CFSG.HardMathSupport.Lang.E6Descent.sq_conj_mul_exactNormalAut g a σ
    have hσ2 : σ ^ 2 = T := by
      rw [hσ, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hT3, one_mul]
    rw [hσ2, ← hα] at hα2
    have hα23 : (α ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hα3, one_pow]
    have hα22 : (α ^ 2) ^ 2 = α := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hα3, one_mul]
    obtain ⟨e2⟩ := key (α ^ 2) g' a' hα2 hα23
    exact ⟨(MulEquiv.subgroupCongr (t158g_fixSubgroup_sq_eq hα22)).trans e2⟩

theorem t158g_d4_graphField_fix {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    {α : MulAut (adjointGroup Tag.D4 F)} (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 F)
    (a : Fin Tag.D4.rank → Fˣ) {σ : F ≃+* F} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 F a σ 0 * d4Graph F ε)) :
    ∃ (q₀ : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q₀).Valid),
      Nonempty (↥(fixSubgroup α) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q₀, hv⟩) ∧
        IsSimpleGroup ↥(fixSubgroup α) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hF
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨e, T, he, hef, hT, hσT⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_frobenius_eq_or_inv_of_orderOf_three Nat.prime_two hn F hF σ hord
  have hK4 : 4 ≤ Nat.card F := by
    rw [hF]
    exact t158g_four_le_two_pow (by omega)
  have hKe : Nat.card F = (2 ^ e) ^ 3 := by rw [hF, ← pow_mul, hef]
  let q₀ : TauCeti.PrimePower := ⟨2, e, Nat.prime_two, he⟩
  have hq₀card : q₀.card = 2 ^ e := TauCeti.PrimePower.card_def q₀
  have hv : (TauCeti.LieTypeIndex.trialityD4 q₀).Valid := TauCeti.LieTypeIndex.valid_trialityD4 q₀
  obtain ⟨eC⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_catEquiv_graphFixedRootGroup_trialityD4 hv
    (by rw [hq₀card]; exact hKe) T (fun c => by rw [hq₀card]; exact hT c)
  obtain ⟨-, hGs, -⟩ := KD264Lie.twistedFixedGroup_eq_graphFixedRootGroup_of_frobenius Nat.prime_two he hKe T 1
    (Or.inl rfl) (fun c => by rw [hT, pow_one])
  have key : ∀ j : ℤ, (j % 3 = 1 ∨ j % 3 = 2) →
      Nonempty (↥(fixSubgroup (CFSG.HardMathSupport.Lang.E6Descent.twistedEntrywiseAut TwistTag.D4 j T)) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 F T.toRingHom)) := by
    intro j hj
    obtain ⟨eT⟩ := KD264Lie.exists_fixedSubgroup_twistedEntrywiseAut_D4_equiv_graphFixed Nat.prime_two he hKe
      T hT j hj
    exact ⟨eT⟩
  suffices hfin : Nonempty (↥(fixSubgroup α) ≃* ↥(graphFixedRootGroup TwistTag.D4 F T.toRingHom)) by
    obtain ⟨eA⟩ := hfin
    exact ⟨q₀, hv, ⟨eA.trans eC.symm⟩, (MulEquiv.isSimpleGroup_congr eA).2 hGs⟩
  rcases hσT with hσ | hσ
  · rw [hσ] at hα
    obtain ⟨ψ, hψ⟩ := CFSG.HardMathSupport.Lang.E6Descent.exists_conj_eq_twistedEntrywiseAut_of_normalForm F hF
      hK4 he hef T hT α hα3 g a ε hα
    obtain ⟨eT⟩ := key ε (by rcases hε with rfl | rfl <;> norm_num)
    exact ⟨((CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupConjEquiv ψ α).trans
      (MulEquiv.subgroupCongr (by rw [hψ]; rfl))).trans eT⟩
  · rw [hσ] at hα
    obtain ⟨ψ, hψ⟩ := CFSG.HardMathSupport.Lang.E6Descent.exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm F
      hF hK4 he hef T T⁻¹ hT (mul_inv_cancel T) α hα3 g a ε hα
    obtain ⟨eT⟩ := key (-(ε : ℤ)) (by rcases hε with rfl | rfl <;> norm_num)
    have hfinv : fixSubgroup α = fixSubgroup α⁻¹ :=
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq α).symm
    exact ⟨((MulEquiv.subgroupCongr hfinv).trans
      ((CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupConjEquiv ψ α⁻¹).trans
        (MulEquiv.subgroupCongr (by rw [hψ]; rfl)))).trans eT⟩

theorem t158g_td4_outer_cases {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hφ3 : φ ^ 3 = 1)
    (hφout : ¬ KFacts.IsInnerAut φ) :
    (∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ n ∧
        Nonempty (↥(fixSubgroup φ) ≃* adjointGroup Tag.G2 k)) ∨
      (∃ (π : Bool) (F' : Type) (_ : Field F') (_ : Finite F'), Sec4.PiField π 2 n F' ∧
        cond π (Even n) (Odd n) ∧
        Nonempty (↥(fixSubgroup φ) ≃* CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F'))) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have hfixφ : fixSubgroup φ = Sec4.autFix φ := Subgroup.ext fun _ => Iff.rfl
  rcases Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hn hK hσ hφ3 hφout with
    ⟨ψ, hψ⟩ | he₂
  · left
    obtain ⟨eG⟩ := KFacts.nonempty_fixedPoints_fieldActor_mulEquiv_g2 σ (ringChar.eq K 2)
    obtain ⟨γ, hγ, hφγ⟩ : ∃ γ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        fixSubgroup γ = (fieldActor (t := TwistTag.D4) σ σ).toMonoidHom.eqLocus (MonoidHom.id _) ∧
          φ = MulAut.congr ψ γ := by
      rcases hψ with h | h
      · exact ⟨fieldActor σ σ, rfl, h.trans (MulEquiv.ext fun _ => rfl)⟩
      · refine ⟨(fieldActor σ σ)⁻¹, Subgroup.ext fun y => ?_, h.trans (MulEquiv.ext fun _ => rfl)⟩
        show (fieldActor (t := TwistTag.D4) σ σ)⁻¹ y = y ↔ fieldActor σ σ y = y
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
        exact eq_comm
    have hk := CFSG.RankThree.PartOne.card_fixSubfield_cube_row Nat.prime_two hn hK σ hσ
    haveI : Finite (fixSubfield σ) := Subtype.finite
    refine ⟨fixSubfield σ, inferInstance, inferInstance, hk, ⟨?_⟩⟩
    have h1 : fixSubgroup φ = fixSubgroup (MulAut.congr ψ γ) := by rw [hφγ]
    exact (MulEquiv.subgroupCongr h1).trans
      ((CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupCongrEquiv ψ γ).symm.trans
        ((MulEquiv.subgroupCongr hγ).trans eG))
  · right
    obtain ⟨e₂⟩ := he₂
    rcases Nat.even_or_odd n with hne | hno
    · obtain ⟨F', _, _, hF', ⟨e₃⟩⟩ := Sec8.kF82D4SecondCentY0Even_holds n hne hn K σ hK hσ
      exact ⟨true, F', inferInstance, inferInstance, ⟨Nat.prime_two, hn, hF'⟩, hne,
        ⟨(MulEquiv.subgroupCongr hfixφ).trans (e₂.trans e₃)⟩⟩
    · obtain ⟨F', _, _, hF', ⟨e₃⟩⟩ := Sec8.kF82D4SecondCentY0_holds n hno K σ hK hσ
      exact ⟨false, F', inferInstance, inferInstance, ⟨Nat.prime_two, hn, hF'⟩, hno,
        ⟨(MulEquiv.subgroupCongr hfixφ).trans (e₂.trans e₃)⟩⟩

theorem t158g_d4_graph_fix {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    {α : MulAut (adjointGroup Tag.D4 F)} (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 F)
    (a : Fin Tag.D4.rank → Fˣ) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 F a 1 0 * d4Graph F ε)) :
    (∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ n ∧
        Nonempty (↥(fixSubgroup α) ≃* adjointGroup Tag.G2 k)) ∨
      (∃ (π : Bool) (F' : Type) (_ : Field F') (_ : Finite F'), Sec4.PiField π 2 n F' ∧
        cond π (Even n) (Odd n) ∧
        Nonempty (↥(fixSubgroup α) ≃* CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F'))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨eφ⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.exists_dual_fixEquiv hn F hF α hα3 g a hε hα
  rcases t158g_td4_outer_cases hn hK₃ hFr hφ3 hφout with ⟨k, _, _, hk, ⟨eG⟩⟩ | ⟨π, F', _, _, hPi, hc, ⟨eP⟩⟩
  · exact Or.inl ⟨k, inferInstance, inferInstance, hk, ⟨eφ.trans eG⟩⟩
  · exact Or.inr ⟨π, F', inferInstance, inferInstance, hPi, hc, ⟨eφ.trans eP⟩⟩

theorem t158g_twoPart_card_adjointD4 {k : Type} [Field k] [Finite k] {d : ℕ} (hd : 1 ≤ d) (hk : Nat.card k = 2 ^ d) :
    twoPart (Nat.card ↥(adjointGroup Tag.D4 k)) = 2 ^ (12 * d) := by
  have hL := CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux.lieModel_adjointD4 Nat.prime_two hd k hk
  have h := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput _ .POmegaPlus 4 2 d
    (CFSG.Blueprint.LieModel.admissible hL) hL).2.2
  unfold twoPart
  rw [h]
  rfl

theorem t158g_twoPart_card_adjointG2 {k : Type} [Field k] [Finite k] {n : ℕ} (hn : 1 ≤ n) (hk : Nat.card k = 2 ^ n) :
    twoPart (Nat.card ↥(adjointGroup Tag.G2 k)) = 2 ^ (6 * n) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk]
  exact t158g_twoPart_ordG2 hn

theorem t158g_card_projImage {π : Bool} {n : ℕ} {F : Type} [Field F] [Finite F] (hK : Sec4.PiField π 2 n F)
    (hc : cond π (Even n) (Odd n)) :
    Nat.card ↥(CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F)) =
        Nat.card ↥(CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ n) F)) * 3 ∧
      twoPart (Nat.card ↥(CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ n) F))) = 2 ^ (3 * n) := by
  have h1 := CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.card_projImage_glPi_three hK
  have h2 := Sec13.card_projImage_slPi_mul_three hK (t158g_modThree hc)
  have heq : Nat.card ↥(CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F)) =
      Nat.card ↥(CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ n) F)) * 3 := by rw [h1, h2]
  refine ⟨heq, ?_⟩
  have hn : 1 ≤ n := hK.one_le
  have hodd : Odd (((2 ^ n) ^ 2 - 1) * cond π ((2 ^ n) ^ 3 - 1) ((2 ^ n) ^ 3 + 1)) := by
    refine Odd.mul ?_ ?_
    · rw [← pow_mul]
      exact t158g_odd_two_pow_sub_one (by omega)
    · cases π
      · have hE : Even ((2 ^ n) ^ 3) :=
          Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by norm_num⟩
        exact hE.add_one
      · rw [Bool.cond_true, ← pow_mul]
        exact t158g_odd_two_pow_sub_one (by omega)
  have hG : twoPart (Nat.card ↥(CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F))) = 2 ^ (3 * n) := by
    have h2n : ((2 : ℕ) ^ n) ^ 3 = 2 ^ (3 * n) := by rw [← pow_mul, mul_comm]
    have key := FQ.twoPart_two_pow_mul_odd (N := 3 * n) hodd
    rw [← h2n] at key
    rw [h1, mul_assoc, key, h2n]
  have hS0 : Nat.card ↥(CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ n) F)) ≠ 0 := by
    haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
      Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 3) F →* _) (QuotientGroup.mk'_surjective _)
    exact Nat.card_pos.ne'
  rw [heq, mul_comm, FP.twoPart_mul_odd (by decide) hS0] at hG
  exact hG

theorem t158g_innDiagOn_of_conj_mem_transfer {Ω : Type} [Group Ω] [Finite Ω] {S L : Subgroup Ω} {b c : Ω}
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hSc : GLAPComponent 3 S S)
    (hbN : b ∈ Subgroup.normalizer (S : Set Ω)) (hcN : c ∈ Subgroup.normalizer (S : Set Ω))
    (hL : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L)
    (hchevL : IsChevSimple 2 (PSimple 3 L)) (hcL : c ∈ Subgroup.normalizer (L : Set Ω))
    {s : PSimple 3 S} (hs : s ∈ chevTransfer 3 S L) {j : ℕ}
    (hxeq : MI.indAut 3 S c hcN = MulAut.conj s * MI.indAut 3 S b hbN ^ j) :
    InnDiagOn 3 (Subgroup.zpowers c) L := by
  have hLS : L ≤ S := hL.1.trans inf_le_left
  have hLC : L ≤ Subgroup.centralizer ({b} : Set Ω) := hL.1.trans inf_le_right
  obtain ⟨l₀, hl₀L, hl₀⟩ := Subgroup.mem_map.1 hs
  have hl₀N : (l₀ : Ω) ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.le_normalizer l₀.2
  have hbjN : b ^ (-(j : ℤ)) ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.zpow_mem _ hbN _
  have hcl : c * (l₀ : Ω) ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.mul_mem _ hcN hl₀N
  have hwN : c * (l₀ : Ω) * b ^ (-(j : ℤ)) ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.mul_mem _ hcl hbjN
  have h1 : MI.indAut 3 S (c * (l₀ : Ω) * b ^ (-(j : ℤ))) hwN = 1 := by
    rw [T156.indAut_mul hcl hbjN, T156.indAut_mul hcN hl₀N, T156.indAut_zpow hbN, t158g_indAut_of_mem l₀, hxeq, hl₀]
    rw [map_inv]
    group
  have hcomm := t158g_comm_of_indAut_eq_one Nat.prime_three hcore hSc hwN h1
  have hin : InducesInnerMod 3 L c := by
    refine ⟨(l₀ : Ω)⁻¹, L.inv_mem (Subgroup.mem_subgroupOf.1 hl₀L), fun y hy => ?_⟩
    have hby : b ^ (-(j : ℤ)) * y = y * b ^ (-(j : ℤ)) := by
      have hyb : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.1 (hLC hy)
      exact ((Commute.zpow_right (show Commute y b from hyb) (-(j : ℤ))).eq).symm
    have h2 : (c * (l₀ : Ω)) * y = y * (c * (l₀ : Ω)) := by
      have h0 := hcomm y (hLS hy)
      have h0' : c * (l₀ : Ω) * (b ^ (-(j : ℤ)) * y) = y * (c * (l₀ : Ω)) * b ^ (-(j : ℤ)) := by
        rw [← mul_assoc, h0]
        group
      rw [hby, ← mul_assoc] at h0'
      exact mul_right_cancel h0'
    have h3 : c⁻¹ * y * c = (l₀ : Ω) * y * (l₀ : Ω)⁻¹ := by
      calc c⁻¹ * y * c = c⁻¹ * (y * (c * l₀)) * (l₀ : Ω)⁻¹ := by group
        _ = c⁻¹ * ((c * l₀) * y) * (l₀ : Ω)⁻¹ := by rw [← h2]
        _ = (l₀ : Ω) * y * (l₀ : Ω)⁻¹ := by group
    rw [h3, inv_inv, inv_mul_cancel]
    exact Subgroup.one_mem _
  exact MI.inner_innDiag_holds Nat.prime_three hL hchevL hcL hin

theorem t158g_cube_of_fgOn {Ω : Type} [Group Ω] [Finite Ω] {S L : Subgroup Ω} {b c : Ω}
    (hbN : b ∈ Subgroup.normalizer (S : Set Ω)) (hcN : c ∈ Subgroup.normalizer (S : Set Ω))
    (hb3 : b ^ 3 = 1) (hc3 : c ^ 3 = 1) (hL : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({b} : Set Ω)) L)
    (hCL : IsChevSimple 2 (PSimple 3 L)) (hFG : FGOn 3 c L)
    (hTq : CFSG.Open.IsQuasisimple ↥(chevTransfer 3 S L))
    (hZ : Subgroup.center ↥(chevTransfer 3 S L) = ⊥) :
    twoPart (Nat.card ↥(chevTransfer 3 S L ⊓ fixSubgroup (MI.indAut 3 S c hcN))) ^ 3 =
      twoPart (Nat.card ↥(chevTransfer 3 S L)) := by
  have hcL : c ∈ Subgroup.normalizer (L : Set Ω) := t158g_normalizer_of_fgOn hFG
  have hcube : centCard2 3 L c ^ 3 = card2 3 L := by
    rcases hFG with hF | hG
    · exact (FP.i91CentPartAt_of_stOrder (G := Ω) Nat.prime_three (by norm_num)
        (FQ.s10StOrderAt Nat.prime_three (by norm_num))) _ L c hL hCL hc3 hF
    · exact hG.2.2
  obtain ⟨h1, h2⟩ := t158g_fixNum_card_transfer hbN hcN hb3 hL hcL hTq hZ
  rw [FP.centCard2_eq_twoPart_fixNum hcL (FP.odd_card_center_pQuot Nat.prime_three (by norm_num) L),
    FP.card2_eq_twoPart_card_pSimple Nat.prime_three (by norm_num) L, h1, h2] at hcube
  exact hcube

theorem t158g_g2_component {P : Type} [Group P] [Finite P] {β : MulAut P} {J : Subgroup P}
    (hJc : GLAPComponent 3 (fixSubgroup β) J) {k : Type} [Field k] [Finite k] {m : ℕ} (hm : 1 ≤ m)
    (hk : Nat.card k = 2 ^ m) (φ : ↥(fixSubgroup β) ≃* adjointGroup Tag.G2 k) :
    IsSimpleGroup ↥J ∧ (∃ a b : ↥J, a * b ≠ b * a) ∧ (∀ s ∈ fixSubgroup β, s ^ 3 = 1 → s ∈ J) ∧
      (2 ≤ m → J = fixSubgroup β) := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  haveI : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
    (by rw [← Nat.card_eq_fintype_card, hk])
  have hJne : J ≠ ⊥ := glaPComponent_ne_bot' hJc
  have hsub : CFSG.Assembly.IsSubnormal J (fixSubgroup β) := CFSG.Assembly.isSubnormal_iff_open.2 hJc.2.1
  have hsq : ∀ t ∈ fixSubgroup β, t ^ 2 ∈ ⁅fixSubgroup β, fixSubgroup β⁆ := by
    intro t ht
    have hA : ∀ a : ↥(adjointGroup Tag.G2 k), a ^ 2 ∈ commutator ↥(adjointGroup Tag.G2 k) := by
      intro a
      have h1 := T156.sq_mem_commutator_adjointGroup Tag.G2 a.1 a.2
      rw [← Subgroup.map_subtype_commutator] at h1
      obtain ⟨b, hb, hba⟩ := h1
      have hb' : b = a ^ 2 := Subtype.ext (by simpa using hba)
      exact hb' ▸ hb
    have hmap : (commutator ↥(adjointGroup Tag.G2 k)).map φ.symm.toMonoidHom =
        commutator ↥(fixSubgroup β) :=
      CFSG.StandardType.ggMap_commutator_of_surjective φ.symm.toMonoidHom φ.symm.surjective
    have h2 : (⟨t, ht⟩ : ↥(fixSubgroup β)) ^ 2 ∈ commutator ↥(fixSubgroup β) := by
      rw [← hmap]
      exact ⟨φ ⟨t, ht⟩ ^ 2, hA _, by simp⟩
    have h3 : (((⟨t, ht⟩ : ↥(fixSubgroup β)) ^ 2 : ↥(fixSubgroup β)) : P) ∈
        (commutator ↥(fixSubgroup β)).map (fixSubgroup β).subtype := ⟨_, h2, rfl⟩
    rw [Subgroup.map_subtype_commutator] at h3
    simpa using h3
  have hle : (⁅fixSubgroup β, fixSubgroup β⁆ : Subgroup P) ≤ fixSubgroup β :=
    Subgroup.commutator_le.mpr fun a ha b hb => (fixSubgroup β).mul_mem
      ((fixSubgroup β).mul_mem ((fixSubgroup β).mul_mem ha hb) ((fixSubgroup β).inv_mem ha))
      ((fixSubgroup β).inv_mem hb)
  rcases Nat.lt_or_ge m 2 with hlt | hge
  ·
    have hk2 : Nat.card k = 2 := by rw [hk, show m = 1 by omega]; norm_num
    have hC : StatedClassicalModel ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ .PSU 3 3 1 := by
      rcases CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk2 with
        ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact h
      all_goals exact absurd h0 (by norm_num)
    obtain ⟨-, K₃, _, _, hK₃, ⟨eU⟩⟩ := hC
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsSimpleGroup (StatedProj (StatedSU 3 (3 ^ 1) K₃)) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K₃ 3 1 hK₃ 3 le_rfl (by decide)
    haveI : Group.IsPerfect ↥(StatedSU 3 (3 ^ 1) K₃) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 3) (f := 1) hK₃ le_rfl (by decide)
    haveI : Group.IsPerfect (StatedProj (StatedSU 3 (3 ^ 1) K₃)) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    let eCC : ↥(⁅fixSubgroup β, fixSubgroup β⁆ : Subgroup P) ≃* StatedProj (StatedSU 3 (3 ^ 1) K₃) :=
      (CFSG.StandardType.ggCommutatorEquiv (fixSubgroup β)).trans
        ((CFSG.StandardType.ggCommutatorCongr φ).trans
          ((CFSG.StandardType.ggCommutatorEquiv (adjointGroup Tag.G2 k)).symm.trans eU))
    haveI hsCC : IsSimpleGroup ↥(⁅fixSubgroup β, fixSubgroup β⁆ : Subgroup P) := eCC.isSimpleGroup
    have hJH : J = ⁅fixSubgroup β, fixSubgroup β⁆ :=
      T158Core.t158Core_eq_commutator_of_glaPComponent hJc hsCC hJne
    obtain ⟨a, b, hab⟩ := Sec8.Item8KFacts2Proof.exists_ne_comm_of_isPerfect
      (inferInstance : Group.IsPerfect (StatedProj (StatedSU 3 (3 ^ 1) K₃)))
    refine ⟨hJH ▸ hsCC, ?_, ?_, fun h => absurd h (by omega)⟩
    · rw [hJH]
      exact ⟨eCC.symm a, eCC.symm b, fun h => hab (by simpa using congrArg eCC h)⟩
    · intro s hs hs3
      rw [hJH]
      have h4 : s = (s ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hs3, one_mul]
      rw [h4]
      exact hsq _ ((fixSubgroup β).pow_mem hs 2)
  ·
    have h3 : 3 ≤ Nat.card k := by
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hge
    have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card k h3
    have hsG : IsSimpleGroup ↥(adjointGroup Tag.G2 k) :=
      CFSG.LieType.SeitzGeneration.isSimpleGroup_adjointGroup_of_isQuasisimple hq
    haveI hsC : IsSimpleGroup ↥(fixSubgroup β) := (MulEquiv.isSimpleGroup_congr φ).2 hsG
    have hJC : J = fixSubgroup β := CFSG.StandardType.ggEq_of_isSubnormal_of_isSimpleGroup hsub hsC hJne
    haveI : Group.IsPerfect ↥(adjointGroup Tag.G2 k) := hq.1
    haveI : Nontrivial ↥(adjointGroup Tag.G2 k) := hsG.toNontrivial
    obtain ⟨a, b, hab⟩ := Sec8.Item8KFacts2Proof.exists_ne_comm_of_isPerfect
      (inferInstance : Group.IsPerfect ↥(adjointGroup Tag.G2 k))
    refine ⟨hJC ▸ hsC, ?_, fun s hs _ => hJC ▸ hs, fun _ => hJC⟩
    rw [hJC]
    exact ⟨φ.symm a, φ.symm b, fun h => hab (by simpa using congrArg φ h)⟩

theorem t158g_fieldPart_of_hasNF {K : Type} [Field K] [Finite K] {α : MulAut (adjointGroup Tag.D4 K)} {ε : ℕ}
    {σ : K ≃+* K} (h : CFSG.LieType.SeitzGeneration.ExcWideThree.HasNF α ε σ) :
    CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart.fieldPart α = σ := by
  obtain ⟨g, a, rfl⟩ := h
  rw [map_mul, CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart.fieldPart_conj,
    CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart.fieldPart_normalForm, one_mul]

theorem t158g_hasNF_pow {K : Type} [Field K] [Finite K] {α : MulAut (adjointGroup Tag.D4 K)} {ε : ℕ}
    {σ : K ≃+* K} (h : CFSG.LieType.SeitzGeneration.ExcWideThree.HasNF α ε σ) (k : ℕ) :
    CFSG.LieType.SeitzGeneration.ExcWideThree.HasNF (α ^ k) (ε * k) (σ ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero, mul_zero, pow_zero, ← map_one (MulAut.conj : adjointGroup Tag.D4 K →* _)]
    exact CFSG.LieType.SeitzGeneration.ExcWideThree.hasNF_conj 1
  | succ k ih =>
    rw [pow_succ, pow_succ, Nat.mul_succ]
    exact ih.mul h

theorem t158g_d4_side {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {y y' : Ω} {L : Subgroup Ω}
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hSc : GLAPComponent 3 S S)
    (hcen : Subgroup.center (PSimple 3 S) = ⊥)
    (hyN : y ∈ Subgroup.normalizer (S : Set Ω)) (hy'N : y' ∈ Subgroup.normalizer (S : Set Ω))
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : PSimple 3 S ≃* adjointGroup Tag.D4 F)
    (hy3 : y ^ 3 = 1) (hy'3 : y' ^ 3 = 1) (hyy' : y * y' = y' * y)
    (hL : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({y} : Set Ω)) L) (hCL : IsChevSimple 2 (PSimple 3 L))
    (hFG : FGOn 3 y' L)
    (hout : MI.indAut 3 S y hyN ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 S)) :
    (∀ (s : PSimple 3 S) (j : ℕ), MI.indAut 3 S y' hy'N ≠ MulAut.conj s * MI.indAut 3 S y hyN ^ j) ∧
      IsSimpleGroup ↥(chevTransfer 3 S L) ∧ (∃ a b : ↥(chevTransfer 3 S L), a * b ≠ b * a) ∧
      chevTransfer 3 S L ≤ fixSubgroup (MI.indAut 3 S y hyN) ∧
      (((∃ σ : F ≃+* F, σ ≠ 1 ∧
            CFSG.LieType.SeitzGeneration.ExcWideThree.HasNF (MulAut.congr e (MI.indAut 3 S y hyN)) 0 σ) ∧
          chevTransfer 3 S L = fixSubgroup (MI.indAut 3 S y hyN) ∧ 3 ∣ n ∧
          twoPart (Nat.card ↥(chevTransfer 3 S L)) = 2 ^ (4 * n)) ∨
        ((∃ ε : ℕ, (ε = 1 ∨ ε = 2) ∧
            CFSG.LieType.SeitzGeneration.ExcWideThree.HasNF (MulAut.congr e (MI.indAut 3 S y hyN)) ε 1) ∧
          (3 ∣ n → (∀ f ∈ fixSubgroup (MI.indAut 3 S y hyN), ∀ t ∈ chevTransfer 3 S L,
              f * t * f⁻¹ ∈ chevTransfer 3 S L) ∧
            twoPart (Nat.card ↥(fixSubgroup (MI.indAut 3 S y hyN))) =
              twoPart (Nat.card ↥(chevTransfer 3 S L)) ∧
            (twoPart (Nat.card ↥(chevTransfer 3 S L)) = 2 ^ (6 * n) ∨
              twoPart (Nat.card ↥(chevTransfer 3 S L)) = 2 ^ (3 * n))))) := by
  classical
  set β := MI.indAut 3 S y hyN with hβdef
  set β' := MI.indAut 3 S y' hy'N with hβ'def
  set α := MulAut.congr e β with hαdef
  have hβ3 : β ^ 3 = 1 := T156.indAut_pow_eq_one hyN hy3
  have hβ'3 : β' ^ 3 = 1 := T156.indAut_pow_eq_one hy'N hy'3
  have hββ' : β * β' = β' * β := by
    have h3 : MI.indAut 3 S (y' * y) (Subgroup.mul_mem _ hy'N hyN) =
        MI.indAut 3 S (y * y') (Subgroup.mul_mem _ hyN hy'N) := T156.indAut_congr hyy'.symm _ _
    rw [T156.indAut_mul hy'N hyN, T156.indAut_mul hyN hy'N] at h3
    exact h3
  have hα3 : α ^ 3 = 1 := by rw [hαdef, ← map_pow, hβ3, map_one]
  have hαout : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.D4 F) :=
    fun h => hout ((congr_mem_inner_iff e β).1 h)
  have hap : IsPGroup 3 (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hy3
  have hJc := glaPComponent_chevTransfer Nat.prime_three hyN hap hL
  have hfixβ : fixSubgroup (chevAut 3 S ⟨y, hyN⟩) = fixSubgroup β := by
    rw [hβdef, T158Core.t158Core_indAut_eq_inv hyN,
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq]
  rw [hfixβ] at hJc
  have hJne : chevTransfer 3 S L ≠ ⊥ := glaPComponent_ne_bot' hJc
  have hsub : CFSG.Assembly.IsSubnormal (chevTransfer 3 S L) (fixSubgroup β) :=
    CFSG.Assembly.isSubnormal_iff_open.2 hJc.2.1
  have hnotInn : ¬ InnDiagOn 3 (Subgroup.zpowers y') L :=
    t158g_not_innDiagOn_of_fgOn Nat.prime_three (by norm_num) hFG
  have hy'L : y' ∈ Subgroup.normalizer (L : Set Ω) := t158g_normalizer_of_fgOn hFG
  have hsfix : ∀ (s : PSimple 3 S) (j : ℕ), β' = MulAut.conj s * β ^ j → s ∈ fixSubgroup β :=
    fun s j h => t158g_fix_of_conj_mul_pow hcen h hββ'
  let eF : ↥(fixSubgroup β) ≃* ↥(fixSubgroup α) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupCongrEquiv e β
  obtain ⟨g, a, σ, ε, hε, hαeq, hσ3, hcase⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.outer_cube_normal_form_cases α hα3 hαout
  rcases hcase with ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩
  ·
    subst hε0
    obtain ⟨d, k, _, _, hd, hdn, hk, ⟨eD⟩⟩ := t158g_d4_field_fix hn hF hα3 g a hσ3 hσ1 hαeq
    obtain ⟨hsD, u, v, huv⟩ := CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux.isSimple_adjointD4 k
    let eC : ↥(fixSubgroup β) ≃* ↥(adjointGroup Tag.D4 k) := eF.trans eD
    haveI hsC : IsSimpleGroup ↥(fixSubgroup β) := (MulEquiv.isSimpleGroup_congr eC).2 hsD
    have hJC : chevTransfer 3 S L = fixSubgroup β :=
      CFSG.StandardType.ggEq_of_isSubnormal_of_isSimpleGroup hsub hsC hJne
    refine ⟨fun s j hxeq => hnotInn (t158g_innDiagOn_of_conj_mem_transfer hcore hSc hyN hy'N hL hCL hy'L
      (by rw [hJC]; exact hsfix s j hxeq) hxeq), by rw [hJC]; exact hsC, ?_, hJc.1,
      Or.inl ⟨⟨σ, hσ1, g, a, hαeq⟩, hJC, ⟨d, by omega⟩, ?_⟩⟩
    · rw [hJC]
      exact ⟨eC.symm u, eC.symm v, fun h => huv (by simpa using congrArg eC h)⟩
    · rw [hJC, Nat.card_congr eC.toEquiv, t158g_twoPart_card_adjointD4 hd hk]
      congr 1
      omega
  ·
    exfalso
    obtain ⟨q₀, hv, ⟨eT⟩, hsT⟩ := t158g_d4_graphField_fix hn hF hα3 g a hσ3 hσ1 (by omega) hαeq
    haveI hsC : IsSimpleGroup ↥(fixSubgroup β) := (MulEquiv.isSimpleGroup_congr eF).2 hsT
    have hJC : chevTransfer 3 S L = fixSubgroup β :=
      CFSG.StandardType.ggEq_of_isSubnormal_of_isSimpleGroup hsub hsC hJne
    have hsJ : IsSimpleGroup ↥(chevTransfer 3 S L) := by rw [hJC]; exact hsC
    obtain ⟨hTq, hZ⟩ := t158g_isQuasisimple_of_simple hsJ (t158g_noncomm_of_glaPComponent hJc)
    obtain ⟨e1⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hyN hap hL
    obtain ⟨e2⟩ := I141F.centerQuot_equiv_pSimple Nat.prime_three hJc hTq
    let eL : PSimple 3 L ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q₀, hv⟩ :=
      e1.trans (e2.symm.trans (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
        ((MulEquiv.subgroupCongr hJC).trans (eF.trans eT))))
    have hTD4 : IsTD4 3 L := ⟨TauCeti.CFSGIndex.lie ⟨.trialityD4 q₀, hv⟩, trivial, ⟨eL⟩⟩
    rcases hFG with hF' | hG'
    · exact MI.td4_not_field_holds hTD4 hF'
    · exact hG'.2.1 ⟨rfl, hTD4⟩
  ·
    subst hσ1
    have hε' : ε = 1 ∨ ε = 2 := by omega
    rcases t158g_d4_graph_fix hn hF hα3 g a hε' hαeq with ⟨k, _, _, hk, ⟨eG⟩⟩ | ⟨π, F', _, _, hPi, hc, ⟨eP⟩⟩
    ·
      obtain ⟨hsJ, hnaJ, hmemJ, hJC2⟩ := t158g_g2_component hJc hn hk (eF.trans eG)
      refine ⟨fun s j hxeq => ?_, hsJ, hnaJ, hJc.1, Or.inr ⟨⟨ε, hε', g, a, hαeq⟩, fun h3n => ?_⟩⟩
      · have hs := hsfix s j hxeq
        have hs3 := t158g_pow_three_of_conj_mul_pow hcen hxeq (mem_fixSubgroup.1 hs) hβ3 hβ'3
        exact hnotInn (t158g_innDiagOn_of_conj_mem_transfer hcore hSc hyN hy'N hL hCL hy'L
          (hmemJ s hs hs3) hxeq)
      · have hn2 : 2 ≤ n := by
          obtain ⟨c, hc⟩ := h3n
          omega
        have hJC := hJC2 hn2
        refine ⟨fun f hf t ht => ?_, by rw [hJC], Or.inl ?_⟩
        · rw [hJC] at ht ⊢
          exact (fixSubgroup β).mul_mem ((fixSubgroup β).mul_mem hf ht) ((fixSubgroup β).inv_mem hf)
        · rw [hJC, Nat.card_congr (eF.trans eG).toEquiv, t158g_twoPart_card_adjointG2 hn hk]
    ·
      let eC : ↥(fixSubgroup β) ≃* ↥(CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F')) := eF.trans eP
      by_cases hn1 : n = 1
      · exfalso
        subst hn1
        have hπ : π = false := by
          cases π
          · rfl
          · exact absurd hc (by decide)
        subst hπ
        haveI : Group.IsSolvable ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ 1) F')) :=
          Sec13.isSolvable_projImage_glPi_two hPi (by norm_num)
        haveI : Group.IsSolvable ↥(fixSubgroup β) :=
          Group.isSolvable_of_isSolvable_injective (f := eC.toMonoidHom) eC.injective
        exact hJne (t158g_eq_bot_of_perfect_of_le_solvable hJc.1 (glaPComponent_perfect hJc))
      · have hn2 : 2 ≤ n := by omega
        have hq2 : 2 < 2 ^ n := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)
        have hCC : (⁅fixSubgroup β, fixSubgroup β⁆ : Subgroup (PSimple 3 S)) ≤ fixSubgroup β :=
          Subgroup.commutator_le.mpr fun a ha b hb => (fixSubgroup β).mul_mem
            ((fixSubgroup β).mul_mem ((fixSubgroup β).mul_mem ha hb) ((fixSubgroup β).inv_mem ha))
            ((fixSubgroup β).inv_mem hb)
        have hsP := Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hPi hq2
        have hpP := Sec13.isPerfect_projImage_slPi hPi hq2
        obtain ⟨eCC, -⟩ := t158g_exists_mulEquiv_projImage_slPi hPi hq2 eC hCC rfl
        have hsCC : IsSimpleGroup ↥(⁅fixSubgroup β, fixSubgroup β⁆ : Subgroup (PSimple 3 S)) :=
          (MulEquiv.isSimpleGroup_congr eCC).2 hsP
        have hJH : chevTransfer 3 S L = ⁅fixSubgroup β, fixSubgroup β⁆ :=
          T158Core.t158Core_eq_commutator_of_glaPComponent hJc hsCC hJne
        obtain ⟨eJ, -⟩ := t158g_exists_mulEquiv_projImage_slPi hPi hq2 eC hJc.1 hJH
        haveI : Nontrivial ↥(CFSG.PGLModel.projImage (Sec4.slPi π 3 (2 ^ n) F')) := hsP.toNontrivial
        obtain ⟨u, v, huv⟩ := Sec8.Item8KFacts2Proof.exists_ne_comm_of_isPerfect hpP
        obtain ⟨hcardG, h2S⟩ := t158g_card_projImage hPi hc
        refine ⟨fun s j hxeq => hnotInn (t158g_td4_pgl_finish hyN hy'N hy3 hL hy'L (hsfix s j hxeq) hxeq hPi
            hn2 eC), (MulEquiv.isSimpleGroup_congr eJ).2 hsP,
          ⟨eJ.symm u, eJ.symm v, fun h => huv (by simpa using congrArg eJ h)⟩, hJc.1,
          Or.inr ⟨⟨ε, hε', g, a, hαeq⟩, fun _ => ⟨?_, ?_, Or.inr ?_⟩⟩⟩
        · intro f hf t ht
          rw [hJH] at ht ⊢
          exact t158g_conj_mem_commutator hf ht
        · rw [Nat.card_congr eC.toEquiv, hcardG, Nat.card_congr eJ.toEquiv, mul_comm,
            FP.twoPart_mul_odd (by decide) Nat.card_pos.ne']
        · rw [Nat.card_congr eJ.toEquiv, h2S]

end D4Model

section D4Main


theorem t158g_d4_false_of_fgOn : ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x₁ x₂ : Ω) (L₁ L₂ : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore 3 ↥S = ⊥ → catalogIs (PSimple 3 S) isD4any →
    IsChevSimple 2 (PSimple 3 S) →
    x₁ ^ 3 = 1 → x₂ ^ 3 = 1 → x₁ * x₂ = x₂ * x₁ →
    GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x₁} : Set Ω)) L₁ → IsChevSimple 2 (PSimple 3 L₁) →
    GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x₂} : Set Ω)) L₂ → IsChevSimple 2 (PSimple 3 L₂) →
    FGOn 3 x₁ L₂ → FGOn 3 x₂ L₁ → NonInnDiag 3 x₁ S → False := by
  intro Ω _ _ S x₁ x₂ L₁ L₂ hSn hq hcore hD hchev hx1 hx2 hc hL1 hC1 hL2 hC2 hF12 hF21 hnon
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hSc : GLAPComponent 3 S S := glaPComponent_self_p hq hcore
  have hqP : CFSG.Open.IsQuasisimple (PQuot 3 S) := isQuasisimple_pQuot_of_glaPComponent hp hSc
  have hN : ∀ y : Ω, y ∈ Subgroup.normalizer (S : Set Ω) := fun y => by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top y
  have hcen : Subgroup.center (PSimple 3 S) = ⊥ := Y10F.center_centerQuot_eq_bot hqP
  obtain ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ := t158g_d4_model hD
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hF
  have hr2 : ringChar F = 2 := ringChar.eq F 2
  set β₁ := MI.indAut 3 S x₁ (hN x₁) with hβ₁
  set β₂ := MI.indAut 3 S x₂ (hN x₂) with hβ₂
  have hout1 : β₁ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 S) := fun h =>
    hnon.2 (MI.inner_innDiag_any hSc hchev hnon.1 ((MI.indAut_mem_inner_iff_any hqP hnon.1).1 h))
  obtain ⟨hA1, hs1, hna1, hJ1le, hT1⟩ :=
    t158g_d4_side hcore hSc hcen (hN x₁) (hN x₂) hn hF e hx1 hx2 hc hL1 hC1 hF21 hout1
  have hout2 : β₂ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 S) := by
    rintro ⟨s, hs⟩
    exact hA1 s 0 (by rw [pow_zero, mul_one]; exact hs.symm)
  obtain ⟨-, hs2, hna2, hJ2le, hT2⟩ :=
    t158g_d4_side hcore hSc hcen (hN x₂) (hN x₁) hn hF e hx2 hx1 hc.symm hL2 hC2 hF12 hout2
  have hβ₁3 : β₁ ^ 3 = 1 := T156.indAut_pow_eq_one (hN x₁) hx1
  have hβ₂3 : β₂ ^ 3 = 1 := T156.indAut_pow_eq_one (hN x₂) hx2
  set α₁ := MulAut.congr e β₁ with hα₁
  set α₂ := MulAut.congr e β₂ with hα₂
  have hα₁3 : α₁ ^ 3 = 1 := by rw [hα₁, ← map_pow, hβ₁3, map_one]
  have hα₂3 : α₂ ^ 3 = 1 := by rw [hα₂, ← map_pow, hβ₂3, map_one]
  have hα₁out : α₁ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.D4 F) :=
    fun h => hout1 ((congr_mem_inner_iff e β₁).1 h)
  have hfin : ∀ (s : adjointGroup Tag.D4 F) (j : ℕ), α₂ ≠ MulAut.conj s * α₁ ^ j := fun s j h =>
    hA1 (e.symm s) j (t158g_conj_pow_transport e h)
  obtain ⟨hTq1, hZ1⟩ := t158g_isQuasisimple_of_simple hs1 hna1
  obtain ⟨hTq2, hZ2⟩ := t158g_isQuasisimple_of_simple hs2 hna2
  have hcube1 := t158g_cube_of_fgOn (hN x₁) (hN x₂) hx1 hx2 hL1 hC1 hF21 hTq1 hZ1
  have hcube2 := t158g_cube_of_fgOn (hN x₂) (hN x₁) hx2 hx1 hL2 hC2 hF12 hTq2 hZ2
  rcases hT1 with ⟨⟨σ₁, hσ₁, hNF1⟩, hJC1, h3n, h2a1⟩ | ⟨⟨ε₁, hε₁, hNF1⟩, hG1⟩ <;>
    rcases hT2 with ⟨⟨σ₂, hσ₂, hNF2⟩, hJC2, h3n', h2a2⟩ | ⟨⟨ε₂, hε₂, hNF2⟩, hG2⟩
  ·
    have hf1 := t158g_fieldPart_of_hasNF hNF1
    have hf2 := t158g_fieldPart_of_hasNF hNF2
    have hσ₁3 : σ₁ ^ 3 = 1 := by rw [← hf1, ← map_pow, hα₁3, map_one]
    have hσ₂3 : σ₂ ^ 3 = 1 := by rw [← hf2, ← map_pow, hα₂3, map_one]
    haveI : IsCyclic (F ≃+* F) := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
    haveI : Finite (F ≃+* F) :=
      Finite.of_injective (fun f : F ≃+* F => (f : F → F)) (fun f g h => RingEquiv.ext (congrFun h))
    obtain ⟨j, hj3, hj⟩ := T158Core.t158Core_pow_of_cyclic hσ₁3 hσ₁ hσ₂3
    have hNF := hNF2.mul (t158g_hasNF_pow hNF1 (3 - j))
    have hσ : σ₂ * σ₁ ^ (3 - j) = 1 := by
      rw [hj, ← pow_add, show j + (3 - j) = 3 by omega, hσ₁3]
    rw [zero_mul, add_zero, hσ] at hNF
    obtain ⟨s, hs⟩ := KD264Lie.exists_conj_of_hasNF_zero hr2 hNF
    apply hfin s j
    have h1 : α₁ ^ (3 - j) * α₁ ^ j = 1 := by rw [← pow_add, show 3 - j + j = 3 by omega, hα₁3]
    calc α₂ = α₂ * α₁ ^ (3 - j) * α₁ ^ j := by rw [mul_assoc, h1, mul_one]
      _ = MulAut.conj s * α₁ ^ j := by rw [hs]
  ·
    obtain ⟨hg1, hg2, hg3⟩ := hG2 h3n
    exact t158g_twoPart_mixed hn hJC1 h2a1 hcube1 hJ2le hg1 hg2 hg3 hcube2
  ·
    obtain ⟨hg1, hg2, hg3⟩ := hG1 h3n'
    exact t158g_twoPart_mixed hn hJC2 h2a2 hcube2 hJ1le hg1 hg2 hg3 hcube1
  ·
    obtain ⟨g₁, a₁, hα₁eq⟩ := hNF1
    obtain ⟨g₂, a₂, hα₂eq⟩ := hNF2
    have hm1 := KD264Lie.mem_innAutDerived_of_graphType g₁ a₁ hε₁ (by rw [← hα₁eq]; exact hα₁3)
    have hm2 := KD264Lie.mem_innAutDerived_of_graphType g₂ a₂ hε₂ (by rw [← hα₂eq]; exact hα₂3)
    rw [← hα₁eq] at hm1
    rw [← hα₂eq] at hm2
    obtain ⟨j, s, -, hj⟩ :=
      KD264Lie.exists_conj_mul_pow_of_mem_innAutDerived_D4 hr2 hm1 hα₁3 hα₁out hm2 hα₂3
    exact hfin s j hj

theorem t158gD4Core_holds : T158GD4Core := t158g_d4_false_of_fgOn

end D4Main

end D4

end CFSG.LocalAnalysis.GLTheoremA.T158G

end
