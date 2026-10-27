module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma102
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.G2Class
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4OuterAux.Two
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.RankThree.PartTwo.Sec4 (PiField)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (exists_catEquiv_trialityD4)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (card_projImage_glPi_three)

private theorem td4_index {S : Type} [Group S]
    (h : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      Nonempty (S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | trialityD4 q => exact ⟨q, hv, ⟨e⟩⟩
  | _ => exact hP.elim

private theorem td4_blueprint_model {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    CFSG.Blueprint.LieModel S .trialityD4 0 q.p q.exponent := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hto : 0 < (CFSG.Blueprint.Chevalley.TwistTag.D4).order := by decide
  have hKc : Nat.card (GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order)) =
      (q.p ^ q.exponent) ^ (CFSG.Blueprint.Chevalley.TwistTag.D4).order := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' hto.ne'), pow_mul]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv
    (GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order))
    (by rw [hKc, TauCeti.PrimePower.card_def]) (iterateFrobenius _ q.p q.exponent)
    (fun x => by rw [iterateFrobenius_def, TauCeti.PrimePower.card_def])
  have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order), inferInstance,
      inferInstance, hKc, iterateFrobenius _ q.p q.exponent,
      fun x => by rw [iterateFrobenius_def], ⟨e.trans b.symm⟩⟩
  exact Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hC⟩)

private theorem td4_order {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    Finite S ∧ (Nat.card S).factorization q.p = 12 * q.exponent := by
  have hL := td4_blueprint_model hv e
  obtain ⟨hfin, -, hfac⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S
    .trialityD4 0 q.p q.exponent (CFSG.Blueprint.LieModel.admissible hL) hL
  exact ⟨hfin, hfac⟩

private theorem td4_odd_false {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hp : q.p ≠ 2)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) (hchev : IsChevSimple 2 S) :
    False := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hodd := td4_blueprint_model hv e
  have hadm := CFSG.Blueprint.LieModel.admissible hodd
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hcard := (hO S .trialityD4 0 q.p q.exponent hadm hodd).2.1
  have hp3 : 3 ≤ q.p := by
    have := q.prime_p.two_le
    omega
  have hQ : 3 ≤ q.p ^ q.exponent := le_trans hp3 (Nat.le_self_pow q.exponent_pos.ne' _)
  have hNS : Nat.card S = (q.p ^ q.exponent) ^ 12 * ((q.p ^ q.exponent) ^ 8 + (q.p ^ q.exponent) ^ 4 + 1) *
      ((q.p ^ q.exponent) ^ 6 - 1) * ((q.p ^ q.exponent) ^ 2 - 1) := by
    simpa [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
      CFSG.ComponentClassification.CatLeaf.lieOrderNumerator] using hcard
  have hbig : 3 ^ 12 ≤ Nat.card S := by
    rw [hNS]
    have h6 : 2 ≤ (q.p ^ q.exponent) ^ 6 := le_trans (by omega) (Nat.pow_le_pow_left hQ 6)
    have h2 : 2 ≤ (q.p ^ q.exponent) ^ 2 := le_trans (by omega) (Nat.pow_le_pow_left hQ 2)
    have hX : 0 < ((q.p ^ q.exponent) ^ 8 + (q.p ^ q.exponent) ^ 4 + 1) *
        ((q.p ^ q.exponent) ^ 6 - 1) * ((q.p ^ q.exponent) ^ 2 - 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    have h12 : 3 ^ 12 ≤ (q.p ^ q.exponent) ^ 12 := Nat.pow_le_pow_left hQ 12
    calc 3 ^ 12 ≤ (q.p ^ q.exponent) ^ 12 := h12
      _ ≤ (q.p ^ q.exponent) ^ 12 * (((q.p ^ q.exponent) ^ 8 + (q.p ^ q.exponent) ^ 4 + 1) *
          ((q.p ^ q.exponent) ^ 6 - 1) * ((q.p ^ q.exponent) ^ 2 - 1)) :=
        Nat.le_mul_of_pos_right _ hX
      _ = _ := by ring
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases hchev with ⟨t', n', f', hX⟩ | ⟨e6⟩ | hPSU
  · have hodd' : CFSG.Blueprint.OddLieType S :=
      ⟨.trialityD4, 0, q.p, q.exponent, q.prime_p, hp, hadm, hodd⟩
    rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType hO hX hodd' with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have h := (hO S _ _ 2 _ (CFSG.Blueprint.LieModel.admissible hX) hX).2.1
      rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 2 (2 ^ 2) = 60 from by decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 2 (2 ^ 2) = 1 from rfl] at h
      norm_num at hbig
      omega
    · have h := (hO S _ _ 2 _ (CFSG.Blueprint.LieModel.admissible hX) hX).2.1
      rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 (2 ^ 1) = 168 from by decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 (2 ^ 1) = 1 from rfl] at h
      norm_num at hbig
      omega
    · have h := (hO S _ _ 2 _ (CFSG.Blueprint.LieModel.admissible hX) hX).2.1
      rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 4 (2 ^ 1) = 25920 from by decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 4 (2 ^ 1) = 1 from rfl] at h
      norm_num at hbig
      omega
  · obtain ⟨e6'⟩ := e6
    have h6 : Nat.card S = 360 := by
      rw [Nat.card_congr e6'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    norm_num at hbig
    omega
  · have hL : CFSG.Blueprint.LieModel S .PSU 3 3 1 :=
      Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hPSU⟩
    have h := (hO S .PSU 3 3 1 (CFSG.Blueprint.LieModel.admissible hL) hL).2.1
    rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 3 (3 ^ 1) = 6048 from by decide,
      show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 3 (3 ^ 1) = 1 from rfl] at h
    norm_num at hbig
    omega

private theorem twoPart_two_pow_mul_odd {a m : ℕ} (hm : Odd m) :
    twoPart (2 ^ a * m) = 2 ^ a := by
  unfold twoPart
  congr 1
  have hm0 : m ≠ 0 := hm.pos.ne'
  have h2 : ¬ 2 ∣ m := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.2 hm
  rw [Nat.factorization_mul (pow_ne_zero a two_ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h2, add_zero, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization_self Nat.prime_two, smul_eq_mul, mul_one]

private theorem twoPart_pow_mul_odd {f k m : ℕ} (hm : Odd m) :
    twoPart ((2 ^ f) ^ k * m) = (2 ^ f) ^ k := by
  rw [← pow_mul, twoPart_two_pow_mul_odd hm, pow_mul]

private theorem odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [pow_succ]
  exact ⟨2 ^ j - 1, by omega⟩

private theorem odd_pow_sub_one_of_pos {f k : ℕ} (hf : 1 ≤ f) (hk : 1 ≤ k) :
    Odd ((2 ^ f) ^ k - 1) := by
  rw [← pow_mul]
  exact odd_two_pow_sub_one (Nat.mul_pos hf hk)

private theorem odd_pgl_factor {π : Bool} {f : ℕ} (hf : 1 ≤ f) :
    Odd (((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1)) := by
  refine Odd.mul (odd_pow_sub_one_of_pos (k := 2) hf (by norm_num)) ?_
  cases π
  · have hE : Even ((2 ^ f) ^ 3) :=
      Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by norm_num⟩
    exact hE.add_one
  · exact odd_pow_sub_one_of_pos (k := 3) hf (by norm_num)

private theorem autFix_inv' {X : Type} [Group X] (α : MulAut X) :
    CFSG.RankThree.PartTwo.Sec4.autFix α⁻¹ = CFSG.RankThree.PartTwo.Sec4.autFix α := by
  ext x
  rw [CFSG.RankThree.PartTwo.Sec4.mem_autFix, CFSG.RankThree.PartTwo.Sec4.mem_autFix]
  constructor
  · intro h
    have := congrArg α h
    rw [MulAut.inv_apply, MulEquiv.apply_symm_apply] at this
    exact this.symm
  · intro h
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact h.symm

private theorem card_autFix_fieldActor {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    Nat.card (CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) =
      (2 ^ f) ^ 6 * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) := by
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) =
      CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ) :=
    Subgroup.ext fun _ => Iff.rfl
  rw [← hfix, CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.card_fixSubgroup_fieldActor
    Nat.prime_two hf hK σ hσ]
  simp only [lieOrderNumerator, mul_assoc]

private theorem td4_fix_bound {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hα3 : α ^ 3 = 1)
    (hαout : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut α) :
    twoPart (Nat.card (CFSG.RankThree.PartTwo.Sec4.autFix α)) ≤ (2 ^ f) ^ 6 := by
  have hodd6 : Odd (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) :=
    (odd_pow_sub_one_of_pos (k := 6) hf (by norm_num)).mul
      (odd_pow_sub_one_of_pos (k := 2) hf (by norm_num))
  rcases CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv
      hf hK hσ hα3 hαout with ⟨β, hβ | hβ⟩ | ⟨e2⟩
  ·
    have hcardα : Nat.card (CFSG.RankThree.PartTwo.Sec4.autFix α) =
        Nat.card (CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) := by
      rw [hβ, ← CFSG.RankThree.PartTwo.Sec8.LangTwistedProof.mulAut_congr_eq]
      exact Nat.card_congr (CFSG.RankThree.PartTwo.Sec4.autFixCongrEquiv β _).toEquiv
    rw [hcardα, card_autFix_fieldActor hf hK hσ, twoPart_pow_mul_odd hodd6]
  ·
    have hcardα : Nat.card (CFSG.RankThree.PartTwo.Sec4.autFix α) =
        Nat.card (CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) := by
      rw [hβ, ← CFSG.RankThree.PartTwo.Sec8.LangTwistedProof.mulAut_congr_eq,
        Nat.card_congr (CFSG.RankThree.PartTwo.Sec4.autFixCongrEquiv β _).toEquiv, autFix_inv']
    rw [hcardα, card_autFix_fieldActor hf hK hσ, twoPart_pow_mul_odd hodd6]
  ·
    obtain ⟨e2⟩ := e2
    rcases Nat.even_or_odd f with hfe | hfo
    · obtain ⟨F, _, _, hF, ⟨e3⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0Even_holds f hfe hf K σ hK hσ
      have hPi : PiField true 2 f F := ⟨Nat.prime_two, hf, hF⟩
      rw [Nat.card_congr (e2.trans e3).toEquiv, card_projImage_glPi_three hPi, mul_assoc,
        twoPart_pow_mul_odd (odd_pgl_factor (π := true) hf)]
      exact Nat.pow_le_pow_right (by positivity) (by norm_num)
    · obtain ⟨F, _, _, hF, ⟨e3⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0_holds f hfo K σ hK hσ
      have hPi : PiField false 2 f F := ⟨Nat.prime_two, hf, hF⟩
      rw [Nat.card_congr (e2.trans e3).toEquiv, card_projImage_glPi_three hPi, mul_assoc,
        twoPart_pow_mul_odd (odd_pgl_factor (π := false) hf)]
      exact Nat.pow_le_pow_right (by positivity) (by norm_num)

theorem centTD4At_holds (G : Type) [Group G] [Finite G] : CentTD4At G := by
  intro X L g hL hchev hTD4 hg3 hNI
  have hp3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨q, hv, ⟨eS⟩⟩ := td4_index hTD4
  have hq2 : q.p = 2 := by
    by_contra hne
    exact td4_odd_false hv hne eS hchev
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eC⟩⟩ := exists_catEquiv_trialityD4 q hv
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hK' : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [hK, hq2]
  have hσ' : ∀ c, σ c = c ^ 2 ^ q.exponent := fun c => by rw [hσ c, hq2]
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 L) := isQuasisimple_pQuot_of_glaPComponent hp3 hL
  have hm : CFSG.Models.LieModel (PQuot 3 L ⧸ Subgroup.center (PQuot 3 L)) .trialityD4 0 q.p q.exponent :=
    CFSG.Models.lieModel_of_namesTag ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ eS
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 1) (d := 1) rfl rfl
    (by norm_num)
  have hc1 : Nat.card (Subgroup.center (PQuot 3 L)) = 1 := Nat.dvd_one.1 (by simpa using hdvd)
  have hcenter : Subgroup.center (PQuot 3 L) = ⊥ := Subgroup.eq_bot_of_card_eq _ hc1
  have eQS : PQuot 3 L ≃* PSimple 3 L :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
  obtain ⟨hfin, hfac⟩ := td4_order hv eS
  rw [hq2] at hfac
  have hcard2 : card2 3 L = 2 ^ (12 * q.exponent) := by
    unfold card2 twoPart
    rw [Nat.card_congr eQS.toEquiv, hfac]
  have hgN : g ∈ Subgroup.normalizer (L : Set G) := hNI.1
  have hψ3 : (CFSG.LocalAnalysis.GLTheoremA.CatB.barAut L g hgN) ^ 3 = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.barAut_pow_three L g hgN hg3
  have hψout : CFSG.LocalAnalysis.GLTheoremA.CatB.barAut L g hgN ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PQuot 3 L) :=
    fun h => hNI.2 (CFSG.LocalAnalysis.GLTheoremA.CatB.inducesInnerMod_of_inner hgN h)
  set eQC : PQuot 3 L ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := eQS.trans (eS.trans eC)
    with heQC
  set ψ' := MulAut.congr eQC (CFSG.LocalAnalysis.GLTheoremA.CatB.barAut L g hgN) with hψ'
  have hψ'3 : ψ' ^ 3 = 1 := by rw [hψ', ← map_pow, hψ3, map_one]
  have hψ'out : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut ψ' := by
    rintro ⟨y, hy⟩
    apply hψout
    refine ⟨eQC.symm y, MulEquiv.ext fun x => ?_⟩
    have key : ∀ z : PQuot 3 L,
        eQC (CFSG.LocalAnalysis.GLTheoremA.CatB.barAut L g hgN z) = y * eQC z * y⁻¹ := by
      intro z
      have h1 := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) => φ (eQC z)) hy
      simp only [MulAut.conj_apply] at h1
      rw [h1, hψ']
      show eQC (CFSG.LocalAnalysis.GLTheoremA.CatB.barAut L g hgN z) =
        eQC (CFSG.LocalAnalysis.GLTheoremA.CatB.barAut L g hgN (eQC.symm (eQC z)))
      rw [MulEquiv.symm_apply_apply]
    apply eQC.injective
    rw [key x, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hfixEq : ∀ z : PQuot 3 L,
      CFSG.LocalAnalysis.GLTheoremA.CatB.barAut L g hgN z = lemma102_conjQ 3 hgN z := by
    intro z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [CFSG.LocalAnalysis.GLTheoremA.CatB.barAut_mk, lemma102_conjQ_mk]
    congr 1
  have hfixSub : CFSG.RankThree.PartTwo.Sec4.autFix (CFSG.LocalAnalysis.GLTheoremA.CatB.barAut L g hgN) =
      lemma102_fixSub 3 hgN := by
    ext z
    show CFSG.LocalAnalysis.GLTheoremA.CatB.barAut L g hgN z = z ↔ z ∈ lemma102_fixSub 3 hgN
    rw [hfixEq z]
    exact Iff.rfl
  have hcardψ : Nat.card (CFSG.RankThree.PartTwo.Sec4.autFix ψ') =
      Nat.card (CFSG.RankThree.PartTwo.Sec4.autFix (CFSG.LocalAnalysis.GLTheoremA.CatB.barAut L g hgN)) :=
    Nat.card_congr (CFSG.RankThree.PartTwo.Sec4.autFixCongrEquiv eQC _).toEquiv
  have hcentFix : centCard2 3 L g = twoPart (Nat.card (CFSG.RankThree.PartTwo.Sec4.autFix ψ')) := by
    rw [lemma102_centCard2_eq_fixSub 3 hgN, hcardψ, hfixSub]
  have hbound := td4_fix_bound hf hK' hσ' hψ'3 hψ'out
  rw [hcentFix]
  have hsq : Nat.sqrt (card2 3 L) = (2 ^ q.exponent) ^ 6 := by
    rw [hcard2, show (2 : ℕ) ^ (12 * q.exponent) = ((2 ^ q.exponent) ^ 6) ^ 2 by ring]
    exact Nat.sqrt_eq' _
  rw [hsq]
  exact hbound

end CFSG.LocalAnalysis.GLTheoremA

end
