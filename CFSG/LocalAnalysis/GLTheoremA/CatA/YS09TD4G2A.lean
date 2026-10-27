module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.FieldActorFixed
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4OuterAux.Two
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.G2Subgroup
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor fieldActor_one fieldActor_mul
  ringEquiv_cube_apply_eq fixSubfield)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (exists_catEquiv_trialityD4)
open CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3 (fixSubgroupFieldActorEquiv)
open CFSG.HardMathSupport.Seitz.TrialityOdd.Inner (trialityFieldImageEquivG2)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (card_projImage_glPi_three)
open CFSG.RankThree.PartTwo.Sec4 (PiField)
open CFSG.LocalAnalysis.GLTheoremA.CatB (barAut barAut_mk barAut_pow_three conjL conjL_apply)


section Field

variable {K : Type} [Field K] [Finite K]

theorem td4g2_sigma_cube {p f : ℕ} (hK : Nat.card K = (p ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (p ^ f)) : σ ^ 3 = 1 := by
  refine RingEquiv.ext fun c => ?_
  simpa [pow_succ] using ringEquiv_cube_apply_eq hK hσ c

theorem td4g2_fieldActor_pow (σ δ : K ≃+* K) (n : ℕ) :
    fieldActor (t := TwistTag.D4) σ (δ ^ n) = fieldActor (t := TwistTag.D4) σ δ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, fieldActor_one]
  | succ n ih => rw [pow_succ δ n, fieldActor_mul, ih, pow_succ (fieldActor (t := TwistTag.D4) σ δ) n]

theorem td4g2_sigma0_cube {p f : ℕ} (hK : Nat.card K = (p ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (p ^ f)) : fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
  rw [← td4g2_fieldActor_pow, td4g2_sigma_cube hK hσ, fieldActor_one]

theorem td4g2_frob_ne_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (p ^ f)) : σ ≠ 1 := by
  intro h1
  have hroot : ∀ c : K, c ^ (p ^ f) = c := fun c => by
    have := congrArg (fun τ : K ≃+* K => τ c) h1
    simpa [hσ] using this
  classical
  haveI := Fintype.ofFinite K
  have hQ : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  have hdeg : (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial K).natDegree = p ^ f :=
    FiniteField.X_pow_card_sub_X_natDegree_eq K hQ
  have hne : (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial K) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset K).val ⊆
      (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial K).roots := by
    intro c _
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hroot c, sub_self]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg, Finset.card_univ, ← Nat.card_eq_fintype_card, hK] at hle
  generalize p ^ f = x at hle hQ
  have h2 : 2 ≤ x := hQ
  nlinarith [Nat.mul_le_mul_left x h2, Nat.mul_le_mul_left (x * x) h2]

end Field

abbrev td4g2C (K : Type) [Field K] (σ : K ≃+* K) : Type :=
  CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom

theorem td4g2_td4_of_catalog {S : Type} [Group S] (h : catalogIs S (onLie isTrialityD4Big)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      2 < q.card ∧ ¬ 3 ∣ q.card ∧
        Nonempty (S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | trialityD4 q =>
    obtain ⟨h1, h2⟩ := hP
    exact ⟨q, hv, h1, h2, ⟨e⟩⟩
  | _ => exact hP.elim

theorem td4g2_blueprint_model {S : Type} [Group S] {q : TauCeti.PrimePower}
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

theorem td4g2_order {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    Finite S ∧ (Nat.card S).factorization q.p = 12 * q.exponent := by
  have hL := td4g2_blueprint_model hv e
  obtain ⟨hfin, -, hfac⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S
    .trialityD4 0 q.p q.exponent (CFSG.Blueprint.LieModel.admissible hL) hL
  exact ⟨hfin, hfac⟩

theorem td4g2_odd_false {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hp : q.p ≠ 2)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) (hchev : IsChevSimple 2 S) :
    False := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hodd := td4g2_blueprint_model hv e
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

theorem td4g2_p_two {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) (hchev : IsChevSimple 2 S) :
    q.p = 2 := by
  by_contra hne
  exact td4g2_odd_false hv hne e hchev

theorem td4g2_fixSub_G2 {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (q.p ^ q.exponent) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent)) :
    Nonempty (↥(CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) ≃*
      TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (fun a b h => RingEquiv.ext fun x => congrFun h x)
  have hq3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hσ3' : σ ^ 3 = 1 := td4g2_sigma_cube hK hσ
  have hσ1 : σ ≠ 1 := td4g2_frob_ne_one q.prime_p q.exponent_pos hK hσ
  have hF : Nat.card (fixSubfield σ) = q.card := by
    have hK' : Nat.card K = q.p ^ (3 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
    have hord : orderOf σ = 3 := orderOf_eq_prime hσ3' hσ1
    obtain ⟨-, hc⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield q.prime_p
      (by have := q.exponent_pos; omega) hK' σ
    rw [hord, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)] at hc
    rw [TauCeti.PrimePower.card_def]
    exact hc
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    rw [ENat.card_eq_coe_natCard, hF]
    exact_mod_cast hq3
  have hZ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := CFSG.Blueprint.Chevalley.Tag.G2)
    (K := ↥(fixSubfield σ))
  obtain ⟨eQ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv ↥(fixSubfield σ) hF
  have eAdj := ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eQ
  have hfix : fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) =
      CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ) :=
    Subgroup.ext fun _ => Iff.rfl
  rw [← hfix]
  exact ⟨(fixSubgroupFieldActorEquiv K σ hσ3).trans ((trialityFieldImageEquivG2 σ hk3).trans eAdj)⟩

theorem td4g2_fixSub_catalog {q : TauCeti.PrimePower} (hq : 2 < q.card ∧ ¬ 3 ∣ q.card)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (q.p ^ q.exponent) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent)) :
    catalogIs ↥(CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ))
      (onLie isG2Big) := by
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid :=
    (TauCeti.LieTypeIndex.valid_iff _).2
      ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 (show 3 ≤ q.card by omega),
        by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
  obtain ⟨e⟩ := td4g2_fixSub_G2 hv hK hσ
  exact ⟨TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩, hq, ⟨e⟩⟩

private theorem td4g2_twoPart_two_pow_mul_odd {a m : ℕ} (hm : Odd m) :
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

private theorem td4g2_twoPart_pow_mul_odd {f k m : ℕ} (hm : Odd m) :
    twoPart ((2 ^ f) ^ k * m) = (2 ^ f) ^ k := by
  rw [← pow_mul, td4g2_twoPart_two_pow_mul_odd hm, pow_mul]

private theorem td4g2_odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [pow_succ]
  exact ⟨2 ^ j - 1, by omega⟩

private theorem td4g2_odd_pow_sub_one {f k : ℕ} (hf : 1 ≤ f) (hk : 1 ≤ k) :
    Odd ((2 ^ f) ^ k - 1) := by
  rw [← pow_mul]
  exact td4g2_odd_two_pow_sub_one (Nat.mul_pos hf hk)

private theorem td4g2_odd_pgl {π : Bool} {f : ℕ} (hf : 1 ≤ f) :
    Odd (((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1)) := by
  refine Odd.mul (td4g2_odd_pow_sub_one (k := 2) hf (by norm_num)) ?_
  cases π
  · have hE : Even ((2 ^ f) ^ 3) :=
      Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, by norm_num⟩
    exact hE.add_one
  · exact td4g2_odd_pow_sub_one (k := 3) hf (by norm_num)

theorem td4g2_pgl_case_twoPart {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {β : MulAut (td4g2C K σ)} (e2 : ↥(CFSG.RankThree.PartTwo.Sec4.autFix β) ≃*
      ↥(CFSG.RankThree.PartTwo.Sec4.autFix (MulAut.conj (CFSG.RankThree.PartTwo.Sec8.d4TrialityY0Elt K σ) * fieldActor (t := TwistTag.D4) σ σ))) :
    twoPart (Nat.card ↥(CFSG.RankThree.PartTwo.Sec4.autFix β)) = (2 ^ f) ^ 3 := by
  rcases Nat.even_or_odd f with hfe | hfo
  · obtain ⟨F, _, _, hF, ⟨e3⟩⟩ :=
      CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0Even_holds f hfe hf K σ hK hσ
    have hPi : PiField true 2 f F := ⟨Nat.prime_two, hf, hF⟩
    rw [Nat.card_congr (e2.trans e3).toEquiv, card_projImage_glPi_three hPi, mul_assoc,
      td4g2_twoPart_pow_mul_odd (td4g2_odd_pgl (π := true) hf)]
  · obtain ⟨F, _, _, hF, ⟨e3⟩⟩ :=
      CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0_holds f hfo K σ hK hσ
    have hPi : PiField false 2 f F := ⟨Nat.prime_two, hf, hF⟩
    rw [Nat.card_congr (e2.trans e3).toEquiv, card_projImage_glPi_three hPi, mul_assoc,
      td4g2_twoPart_pow_mul_odd (td4g2_odd_pgl (π := false) hf)]

end CFSG.LocalAnalysis.GLTheoremA

end
