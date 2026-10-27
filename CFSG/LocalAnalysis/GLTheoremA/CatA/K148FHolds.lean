module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148FFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09TD4G2C
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148FTwoGlue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM4Twist
import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
import CFSG.RankThree.PartTwo.Sec12.Hering129LG2
import CFSG.RankThree.PartTwo.Sec19.SimsC198G2
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieD4
import CFSG.RankThree.PartTwo.Sec4.Ronan148SBasic
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.FieldCopy
import CFSG.LocalAnalysis.GLTheoremA.CatA.T266G2Holds
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapParam
public import CFSG.RankThree.PartTwo.KFacts.K71G2
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.PGLModel (projImage)


private theorem k148Hold_pp_eq {q q' : TauCeti.PrimePower} (hq : q.p = 2) (h : q'.card = q.card) :
    q'.p = 2 ∧ q'.exponent = q.exponent := by
  have hcardq : q'.p ^ q'.exponent = 2 ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def, h, TauCeti.PrimePower.card_def, hq]
  have hp2 : q'.p = 2 := by
    have hdvd : q'.p ∣ 2 ^ q.exponent := by
      rw [← hcardq]
      exact dvd_pow_self _ (Nat.pos_iff_ne_zero.1 q'.exponent_pos)
    exact (Nat.prime_dvd_prime_iff_eq q'.prime_p Nat.prime_two).1 (q'.prime_p.dvd_of_dvd_pow hdvd)
  refine ⟨hp2, ?_⟩
  have h2 := hcardq
  rw [hp2] at h2
  exact Nat.pow_right_injective (le_refl 2) h2

private theorem k148Hold_model {P : Type} [Group P] {q : TauCeti.PrimePower} (hq : q.p = 2)
    (hcat : catalogIs P (CFSG.LocalAnalysis.GLTheoremA.I2023.isTD4Of q)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (2 ^ q.exponent) ^ 3 ∧ (∀ c, σ c = c ^ (2 ^ q.exponent)) ∧
      Nonempty (P ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨d, hv, hP, ⟨eS⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  cases d with
  | trialityD4 q' =>
    have hP' : q'.card = q.card := hP
    obtain ⟨hp2, hn⟩ := k148Hold_pp_eq hq hP'
    obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eC⟩⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q' hv
    rw [hp2, hn] at hK
    simp only [hp2, hn] at hσ
    exact ⟨K, inferInstance, inferInstance, σ, hK, hσ, ⟨eS.trans eC⟩⟩
  | _ => exact hP.elim

private theorem k148Hold_transport {P C : Type} [Group P] [Group C] (eS : P ≃* C) {τ : MulAut P}
    (hτ3 : τ ^ 3 = 1) (hτi : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut τ) :
    (MulAut.congr eS τ) ^ 3 = 1 ∧ ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut (MulAut.congr eS τ) ∧
      (∀ x : P, MulAut.congr eS τ (eS x) = eS (τ x)) := by
  have hβx : ∀ x : P, MulAut.congr eS τ (eS x) = eS (τ x) := fun x =>
    CFSG.LocalAnalysis.GLTheoremA.td4g2_congr_apply eS τ x
  refine ⟨by rw [← map_pow, hτ3, map_one], ?_, hβx⟩
  rintro ⟨g, hg⟩
  apply hτi
  refine ⟨eS.symm g, MulEquiv.ext fun y => ?_⟩
  apply eS.injective
  have key := congrArg (fun ψ : MulAut C => ψ (eS y)) hg
  simp only [MulAut.conj_apply] at key
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hβx]
  exact key

private theorem k148Hold_g2_ne_sl3 {π : Bool} {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hq : ModThree π (2 ^ f)) {M : ℕ}
    (hM : M * 3 = (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1))
    (hG : M = CFSG.Open.orderG2 (2 ^ g)) : False := by
  have hodd1 : Odd (3 * (((2 ^ g) ^ 6 - 1) * ((2 ^ g) ^ 2 - 1))) :=
    Odd.mul (by decide) ((CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hg (by norm_num)).mul
      (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hg (by norm_num)))
  have hodd2 : Odd (((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1)) := by
    refine (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hf (by norm_num)).mul ?_
    cases π
    · exact CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_add_one hf (by norm_num)
    · exact CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hf (by norm_num)
  have heq : 2 ^ (6 * g) * (3 * (((2 ^ g) ^ 6 - 1) * ((2 ^ g) ^ 2 - 1))) =
      2 ^ (3 * f) * (((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1)) := by
    have h1 : 2 ^ (6 * g) = (2 ^ g) ^ 6 := by rw [mul_comm, pow_mul]
    have h2 : 2 ^ (3 * f) = (2 ^ f) ^ 3 := by rw [mul_comm, pow_mul]
    rw [h1, h2, ← mul_assoc]
    rw [hG] at hM
    unfold CFSG.Open.orderG2 at hM
    calc (2 ^ g) ^ 6 * 3 * (((2 ^ g) ^ 6 - 1) * ((2 ^ g) ^ 2 - 1))
        = (2 ^ g) ^ 6 * ((2 ^ g) ^ 6 - 1) * ((2 ^ g) ^ 2 - 1) * 3 := by ring
      _ = _ := by rw [hM]; ring
  obtain ⟨hfg, hodd⟩ := CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj hodd1 hodd2 heq
  have hf2 : f = 2 * g := by omega
  have h4 : (2 ^ f) % 3 = 1 := by
    rw [hf2, pow_mul]
    norm_num [Nat.pow_mod]
  cases π
  · exact absurd hq (by simp [ModThree, h4])
  · obtain ⟨r, hr⟩ : ∃ r : ℕ, r = 2 ^ g := ⟨_, rfl⟩
    have hr2 : 2 ≤ r := by
      rw [hr]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
    have hqr : 2 ^ f = r ^ 2 := by rw [hf2, pow_mul', ← hr]
    simp only [cond_true] at hodd
    have hodd' : 3 * ((r ^ 6 - 1) * (r ^ 2 - 1)) = (r ^ 4 - 1) * (r ^ 6 - 1) := by
      calc 3 * ((r ^ 6 - 1) * (r ^ 2 - 1)) = 3 * (((2 ^ g) ^ 6 - 1) * ((2 ^ g) ^ 2 - 1)) := by rw [hr]
        _ = ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) := hodd
        _ = ((r ^ 2) ^ 2 - 1) * ((r ^ 2) ^ 3 - 1) := by rw [hqr]
        _ = (r ^ 4 - 1) * (r ^ 6 - 1) := by rw [← pow_mul, ← pow_mul]
    have h6 : 0 < r ^ 6 - 1 := by
      have : 2 ^ 6 ≤ r ^ 6 := Nat.pow_le_pow_left hr2 6
      omega
    have hcancel : 3 * (r ^ 2 - 1) = r ^ 4 - 1 := by
      have e1 : 3 * ((r ^ 6 - 1) * (r ^ 2 - 1)) = (r ^ 6 - 1) * (3 * (r ^ 2 - 1)) := by ring
      have e2 : (r ^ 4 - 1) * (r ^ 6 - 1) = (r ^ 6 - 1) * (r ^ 4 - 1) := by ring
      rw [e1, e2] at hodd'
      exact Nat.eq_of_mul_eq_mul_left h6 hodd'
    have h1 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h1' : 1 ≤ r ^ 4 := Nat.one_le_pow _ _ (by omega)
    have hR : 4 ≤ r ^ 2 := by nlinarith
    have hz : (3 : ℤ) * ((r : ℤ) ^ 2 - 1) = (r : ℤ) ^ 4 - 1 := by
      have := congrArg (fun x : ℕ => (x : ℤ)) hcancel
      push_cast [Nat.cast_sub h1, Nat.cast_sub h1'] at this
      linarith
    have hR' : (4 : ℤ) ≤ (r : ℤ) ^ 2 := by exact_mod_cast hR
    nlinarith

private theorem k148Hold_num_three (Q : ℕ) :
    CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 Q = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) ∧
    CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 3 Q = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) := by
  have hI : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  have h3 : (3 * (3 - 1) / 2 : ℕ) = 3 := by norm_num
  refine ⟨?_, ?_⟩
  · simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator, hI, h3]
    rw [Finset.prod_insert (by decide), Finset.prod_singleton]
  · simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator, hI, h3]
    rw [Finset.prod_insert (by decide), Finset.prod_singleton, if_pos (by decide), if_neg (by decide)]

private theorem k148Hold_sl3_not_g2 {π : Bool} {f : ℕ} (hf2 : 2 ≤ f) {F : Type} [Field F]
    (hF : PiField π 2 f F) (hq : ModThree π (2 ^ f)) {i : TauCeti.CFSGIndex} (hi : isG2Quot i)
    (e : ↥(projImage (slPi π 3 (2 ^ f) F)) ≃* i.Group) : False := by
  have := hF.finite
  haveI : Finite ↥(projImage (slPi π 3 (2 ^ f) F)) := inferInstance
  have hcard := CFSG.RankThree.PartTwo.Sec13.card_projImage_slPi_mul_three hF hq
  have hf1 : 1 ≤ f := by omega
  have hadm : CFSG.Open.StatedLieAdmissible (cond π .PSL .PSU) 3 2 f := by
    cases π
    · refine ⟨Nat.prime_two, hf1, le_rfl, ?_⟩
      intro h
      have h2 : 2 ^ f = 2 := (Prod.mk.inj h).2
      have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      omega
    · refine ⟨Nat.prime_two, hf1, by norm_num, ?_, ?_⟩ <;> intro h <;> exact absurd (Prod.mk.inj h).1 (by norm_num)
  have hM : Nat.card ↥(projImage (slPi π 3 (2 ^ f) F)) *
      CFSG.ComponentClassification.CatLeaf.lieOrderDivisor (cond π .PSL .PSU) 3 (2 ^ f) =
      CFSG.ComponentClassification.CatLeaf.lieOrderNumerator (cond π .PSL .PSU) 3 (2 ^ f) := by
    cases π
    · have hg : Nat.gcd 3 (2 ^ f + 1) = 3 := by
        apply Nat.gcd_eq_left
        have : (2 ^ f) % 3 = 2 := hq
        omega
      simp only [cond_false, CFSG.ComponentClassification.CatLeaf.lieOrderDivisor, hg,
        (k148Hold_num_three _).2]
      rw [hcard]
      simp only [cond_false]
      ring
    · have hg : Nat.gcd 3 (2 ^ f - 1) = 3 := by
        apply Nat.gcd_eq_left
        have : (2 ^ f) % 3 = 1 := hq
        have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        omega
      simp only [cond_true, CFSG.ComponentClassification.CatLeaf.lieOrderDivisor, hg,
        (k148Hold_num_three _).1]
      rw [hcard]
      simp only [cond_true]
      ring
  have hb := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  rcases hi with hiG | hiU
  ·
    cases i with
    | cyclic _ _ => exact (show False from hiG).elim
    | alternating _ _ => exact (show False from hiG).elim
    | sporadic _ => exact (show False from hiG).elim
    | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | G2 q' =>
      have hq3 : 3 ≤ q'.card :=
        (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      have hcardG : Nat.card ↥(projImage (slPi π 3 (2 ^ f) F)) = CFSG.Open.orderG2 q'.card :=
        hb ⟨.G2 q', hv⟩ _ ⟨e⟩
      by_cases hp : q'.p = 2
      · have hqc : q'.card = 2 ^ q'.exponent := by rw [TauCeti.PrimePower.card_def, hp]
        rw [hqc] at hcardG
        exact k148Hold_g2_ne_sl3 hf1 q'.exponent_pos hq hcard hcardG
      · have hadm' : CFSG.Open.StatedLieAdmissible .G2 0 q'.p q'.exponent :=
          ⟨q'.prime_p, q'.exponent_pos, rfl, by rwa [TauCeti.PrimePower.card_def] at hq3⟩
        have hM' : Nat.card ↥(projImage (slPi π 3 (2 ^ f) F)) *
            CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .G2 0 (q'.p ^ q'.exponent) =
            CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .G2 0 (q'.p ^ q'.exponent) := by
          rw [hcardG]
          simp [CFSG.Open.orderG2, CFSG.ComponentClassification.CatLeaf.lieOrderNumerator,
            CFSG.ComponentClassification.CatLeaf.lieOrderDivisor, TauCeti.PrimePower.card_def]
        rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hadm hadm' hp hM hM' with
          ⟨-, -, -, h, -⟩ | ⟨-, -, -, h, -⟩ | ⟨-, -, -, h, -⟩ <;> exact absurd h (by decide)
    | _ => exact (show False from hiG).elim
  ·
    have hcardU : Nat.card ↥(projImage (slPi π 3 (2 ^ f) F)) = 6048 :=
      CFSG.LocalAnalysis.GLTheoremA.CatDistinct.card_isU33 hb ⟨i, hiU, ⟨e⟩⟩
    have hadm' : CFSG.Open.StatedLieAdmissible .PSU 3 3 1 :=
      ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
    have hM' : Nat.card ↥(projImage (slPi π 3 (2 ^ f) F)) *
        CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 3 (3 ^ 1) =
        CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 3 (3 ^ 1) := by
      rw [hcardU]
      decide
    rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hadm hadm' (by norm_num) hM hM' with
      ⟨-, -, -, h, -⟩ | ⟨-, -, -, h, -⟩ | ⟨-, -, -, h, -⟩ <;> exact absurd h (by decide)

private theorem k148Hold_pgl_no_g2 {π : Bool} {f : ℕ} (hf2 : 2 ≤ f) {F : Type} [Field F]
    (hF : PiField π 2 f F) (hq : ModThree π (2 ^ f)) {P : Type} [Group P] [Finite P] {X S : Subgroup P}
    (e : ↥X ≃* ↥(projImage (glPi π 3 (2 ^ f) F))) (hS : GLAPComponent 3 X S) (hG2 : IsG2Quot 3 S) :
    False := by
  have := hF.finite
  have hq2 : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F :=
    fun h => by subst h; exact hF.unitary
  have hO : GLAPPrimeCore 3 ↥X = ⊥ := by
    set N := GLAPPrimeCore 3 ↥X with hN
    have hNn : (N.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ e.surjective
    have hcop : Nat.Coprime 3 (Nat.card ↥(N.map e.toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective e.injective]
      exact CFSG.pPrimeCore_coprime_card
    have hb := CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.pgl_normal_coprime_eq_bot hF hq hq2 _ hcop
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hb
  have hSP : projImage (slPi π 3 (2 ^ f) F) ≤ projImage (glPi π 3 (2 ^ f) F) :=
    Subgroup.map_mono (CFSG.RankThree.PartTwo.Sec4.slPi_le_glPi hπ)
  have hcomm : (commutator ↥X).map e.toMonoidHom =
      (projImage (slPi π 3 (2 ^ f) F)).subgroupOf (projImage (glPi π 3 (2 ^ f) F)) := by
    rw [← CFSG.RankThree.PartTwo.Sec13.commutator_projImage_glPi hF hq2, commutator_def, commutator_def,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.surjective]
  let eD : ↥(commutator ↥X) ≃* ↥(projImage (slPi π 3 (2 ^ f) F)) :=
    ((commutator ↥X).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hcomm).trans (Subgroup.subgroupOfEquivOfLe hSP))
  haveI hsimpleQ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hF hq2
  have hR : IsSimpleGroup ↥(commutator ↥X) := eD.isSimpleGroup
  have hSeq := CFSG.LocalAnalysis.GLTheoremA.K148FTwo.pComp_eq_derived hO hR hS
  haveI hSs : IsSimpleGroup ↥S := by
    rw [hSeq]
    exact CFSG.LocalAnalysis.GLTheoremA.K148FTwo.simple_derivedIn hR
  have hQS := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hS
  have hOS : GLAPPrimeCore 3 ↥S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥S) with h | h
    · exact h
    · exfalso
      haveI := hQS.2.toNontrivial
      haveI : Nontrivial (PQuot 3 S) :=
        CFSG.LocalAnalysis.GLTheoremA.K148FTwo.nontrivial_of_quotient (Subgroup.center (PQuot 3 S))
      obtain ⟨x, hx⟩ := exists_ne (1 : PQuot 3 S)
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      apply hx
      rw [QuotientGroup.eq_one_iff]
      show y ∈ GLAPPrimeCore 3 ↥S
      rw [h]
      trivial
  let eP : PQuot 3 S ≃* ↥S := (QuotientGroup.quotientMulEquivOfEq hOS).trans QuotientGroup.quotientBot
  let eDS : ↥S ≃* ↥(commutator ↥X) :=
    (MulEquiv.subgroupCongr hSeq).trans
      (Subgroup.equivMapOfInjective (commutator ↥X) X.subtype X.subtype_injective).symm
  obtain ⟨i, hi, ⟨eC⟩⟩ := hG2
  exact k148Hold_sl3_not_g2 hf2 hF hq hi ((eP.trans (eDS.trans eD)).symm.trans eC)

theorem k148FLangFact_holds : K148FLangFact := by
  intro P _ _ q hq2 hcat τ hτ3 hτi S hS hG2
  classical
  obtain ⟨K, _, _, σ, hK, hσ, ⟨eS⟩⟩ := k148Hold_model hq2 hcat
  set n := q.exponent with hn
  have hn1 : 1 ≤ n := q.exponent_pos
  obtain ⟨hβ3, hβout, -⟩ := k148Hold_transport eS hτ3 hτi
  set β := MulAut.congr eS τ with hβ
  have eF : ↥(CFSG.RankThree.PartTwo.Sec4.autFix τ) ≃* ↥(CFSG.RankThree.PartTwo.Sec4.autFix β) :=
    (CFSG.RankThree.PartTwo.Sec4.autFixCongrEquiv eS τ).symm
  have hSX : S ≤ CFSG.RankThree.PartTwo.Sec4.autFix τ := hS.1
  rcases CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hn1 hK hσ
      hβ3 hβout with ⟨γ, hγ⟩ | he2
  ·
    obtain ⟨eG⟩ : Nonempty (↥(CFSG.RankThree.PartTwo.Sec4.autFix τ) ≃*
        ↥(CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ))) := by
      rcases hγ with hγ | hγ
      · obtain ⟨e1⟩ := td4g2_autFix_conj γ (fieldActor (t := TwistTag.D4) σ σ)
        rw [← hγ] at e1
        exact ⟨eF.trans e1⟩
      · obtain ⟨e1⟩ := td4g2_autFix_conj γ (fieldActor (t := TwistTag.D4) σ σ)⁻¹
        rw [← hγ] at e1
        exact ⟨(eF.trans e1).trans (MulEquiv.subgroupCongr (td4g2_autFix_inv _))⟩
    by_cases hf1 : n = 1
    ·
      right
      refine ⟨hf1, ?_⟩
      obtain ⟨i, hi, ⟨eQ⟩⟩ := hG2
      rcases hi with hiG | hiU
      · exfalso
        have hcardF : Nat.card ↥(CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) =
            12096 := by
          have h := CFSG.LocalAnalysis.GLTheoremA.I2023.sfm4_card_fix hn1 K hK σ hσ (Or.inl rfl)
          have hfixeq : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) =
              CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ) :=
            Subgroup.ext fun _ => Iff.rfl
          rw [← hfixeq, h, hf1]
          norm_num
        have hle1 : Nat.card (PQuot 3 S) ≤ Nat.card ↥S :=
          Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
        have hle2 : Nat.card ↥S ≤ Nat.card ↥(CFSG.RankThree.PartTwo.Sec4.autFix τ) :=
          Subgroup.card_le_of_le hSX
        rw [Nat.card_congr eG.toEquiv, hcardF] at hle2
        cases i with
        | cyclic _ _ => exact (show False from hiG).elim
        | alternating _ _ => exact (show False from hiG).elim
        | sporadic _ => exact (show False from hiG).elim
        | lie idx =>
        obtain ⟨d, hv⟩ := idx
        cases d with
        | G2 q' =>
          have hq3 : 3 ≤ q'.card :=
            (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
          have hcardG : Nat.card (PQuot 3 S) = CFSG.Open.orderG2 q'.card :=
            CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.G2 q', hv⟩ _ ⟨eQ⟩
          have hbig := CFSG.LocalAnalysis.GLTheoremA.CatDistinct.orderG2_ge hq3
          omega
        | _ => exact (show False from hiG).elim
      · exact ⟨i, hiU, ⟨eQ⟩⟩
    ·
      left
      refine ⟨by omega, ?_⟩
      have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
        have h3 : 3 ≤ q.card := by
          rw [TauCeti.PrimePower.card_def, hq2]
          calc 3 ≤ 2 ^ 2 := by norm_num
            _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact (TauCeti.LieTypeIndex.valid_iff _).2
          ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 (show 3 ≤ q.card from h3),
            by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
      have hK' : Nat.card K = (q.p ^ q.exponent) ^ 3 := by rw [hq2]; exact hK
      have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := by rw [hq2]; exact hσ
      obtain ⟨e'⟩ := td4g2_fixSub_G2 hv hK' hσ'
      exact ⟨TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩, ⟨hq2, rfl⟩, ⟨eG.trans e'⟩⟩
  ·
    exfalso
    obtain ⟨e2⟩ := he2
    rcases Nat.even_or_odd n with hne | hno
    · obtain ⟨F, _, _, hF, ⟨e3⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0Even_holds n hne hn1 K σ hK hσ
      have hPi : PiField true 2 n F := ⟨Nat.prime_two, hn1, hF⟩
      have hqm : ModThree true (2 ^ n) :=
        CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.two_pow_mod_three_even hne
      have hf2 : 2 ≤ n := by
        obtain ⟨k, hk⟩ := hne
        omega
      exact k148Hold_pgl_no_g2 hf2 hPi hqm ((eF.trans e2).trans e3) hS hG2
    · obtain ⟨F, _, _, hF, ⟨e3⟩⟩ := CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0_holds n hno K σ hK hσ
      have hPi : PiField false 2 n F := ⟨Nat.prime_two, hn1, hF⟩
      by_cases hn1' : n = 1
      ·
        have h2 : (2 : ℕ) ^ n = 2 := by rw [hn1']; norm_num
        haveI hsolv := CFSG.RankThree.PartTwo.Sec13.isSolvable_projImage_glPi_two hPi h2
        haveI : Group.IsSolvable ↥(CFSG.RankThree.PartTwo.Sec4.autFix τ) :=
          solvable_of_solvable_injective (f := ((eF.trans e2).trans e3).toMonoidHom)
            ((eF.trans e2).trans e3).injective
        exact CFSG.LocalAnalysis.GLTheoremA.K148FTwo.not_pComp_of_solvable hS
      · have hqm : ModThree false (2 ^ n) :=
          CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.two_pow_mod_three_odd hno
        have hf2 : 2 ≤ n := by omega
        exact k148Hold_pgl_no_g2 hf2 hPi hqm ((eF.trans e2).trans e3) hS hG2

private theorem k148Hold_pquot_not_comm {G : Type} [Group G] [Finite G] {X M : Subgroup G}
    (hM : GLAPComponent 3 X M) (hc : ∀ a b : PQuot 3 M, a * b = b * a) : False := by
  obtain ⟨hcQ, hsQ⟩ := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hM
  haveI := hsQ.toNontrivial
  haveI : Nontrivial (PQuot 3 M) :=
    CFSG.LocalAnalysis.GLTheoremA.K148FTwo.nontrivial_of_quotient (Subgroup.center (PQuot 3 M))
  have h : commutator (PQuot 3 M) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hc y x
  rw [hcQ] at h
  exact top_ne_bot h

private theorem k148Hold_card_psimple_of_simple {G : Type} [Group G] [Finite G] {X N M : Subgroup G}
    (hNX : N ≤ X) (hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ N) (hN : IsSimpleGroup ↥N)
    (h3 : 3 ∣ Nat.card N) (hM : GLAPComponent 3 X M) : Nat.card (PSimple 3 M) = Nat.card N := by
  classical
  have hQ := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hM
  obtain ⟨hMX, hIS, -, -⟩ := id hM
  have hNM : N ≤ M := by
    have hsub := CFSG.LocalAnalysis.GLTheoremA.K148FTwo.isSubnormal_inf N hIS
    rw [inf_eq_right.2 hNX] at hsub
    haveI := hN
    rcases CFSG.LocalAnalysis.GLTheoremA.K148FTwo.subnormal_eq_bot_or_top_of_simple N hsub rfl with h0 | h1
    · exfalso
      refine k148Hold_pquot_not_comm hM fun x y => ?_
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      have hc : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ M ⊓ N :=
        ⟨M.mul_mem (M.mul_mem (M.mul_mem a.2 b.2) (M.inv_mem a.2)) (M.inv_mem b.2),
          hcomm a (hMX a.2) b (hMX b.2)⟩
      rw [h0, Subgroup.mem_bot] at hc
      have hab : a * b = b * a := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        calc (a : G) * b = (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ * (b * a) := by group
          _ = b * a := by rw [hc, one_mul]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab]
    · calc N = M ⊓ N := h1.symm
        _ ≤ M := inf_le_left
  set φ : ↥N →* PQuot 3 M := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)).comp (Subgroup.inclusion hNM)
    with hφ
  have hsurj : Function.Surjective φ := by
    have hle : commutator (PQuot 3 M) ≤ φ.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      refine ⟨⟨(a : G) * b * (a : G)⁻¹ * (b : G)⁻¹, hcomm a (hMX a.2) b (hMX b.2)⟩, ?_⟩
      rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, commutatorElement_def,
        ← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
    rw [hQ.1] at hle
    exact MonoidHom.range_eq_top.1 (top_le_iff.1 hle)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    haveI := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      have hle : (⊤ : Subgroup ↥N).map (Subgroup.inclusion hNM) ≤ GLAPPrimeCore 3 ↥M := by
        rintro _ ⟨n, -, rfl⟩
        have hn : n ∈ φ.ker := h ▸ Subgroup.mem_top n
        rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hn
        exact (QuotientGroup.eq_one_iff _).1 hn
      have hcard := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hNM), Subgroup.card_top] at hcard
      have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥M)) := CFSG.pPrimeCore_coprime_card
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop (h3.trans hcard)
  let e₁ : ↥N ≃* PQuot 3 M := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  haveI : IsSimpleGroup (PQuot 3 M) := e₁.symm.isSimpleGroup
  have hZ : Subgroup.center (PQuot 3 M) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PQuot 3 M)) with h | h
    · exact h
    · exfalso
      refine k148Hold_pquot_not_comm hM fun a b => ?_
      have hb : b ∈ Subgroup.center (PQuot 3 M) := h ▸ Subgroup.mem_top b
      exact Subgroup.mem_center_iff.1 hb a
  show Nat.card (PQuot 3 M ⧸ Subgroup.center (PQuot 3 M)) = Nat.card ↥N
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv,
    Nat.card_congr e₁.symm.toEquiv]

private theorem k148Hold_card_psimple_of_quasisimple {G : Type} [Group G] [Finite G] {X M : Subgroup G}
    (hXq : CFSG.IsQuasisimple ↥X) (hZ : IsPGroup 3 (Subgroup.center ↥X)) (h3 : 3 ∣ Nat.card X)
    (hM : GLAPComponent 3 X M) : Nat.card (PSimple 3 M) * Nat.card (Subgroup.center ↥X) = Nat.card X := by
  classical
  have hO : GLAPPrimeCore 3 ↥X = ⊥ :=
    CFSG.RankThree.PartTwo.Sec15.pPrimeCore_three_eq_bot_of_isQuasisimple hXq h3 hZ
  obtain ⟨hMX, hIS, hMq⟩ := CFSG.LocalAnalysis.GLTheoremA.K148FTwo.pComp_facts hO hM
  have hsub : (M.subgroupOf X).IsSubnormal := (CFSG.Open.IsSubnormal.iff_subgroupOf hMX).1 hIS
  have hMeq : M = X := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hXq hsub with h | h
    · exact le_antisymm hMX fun x hx => by
        have : (⟨x, hx⟩ : ↥X) ∈ M.subgroupOf X := h ▸ Subgroup.mem_top _
        exact this
    · exfalso
      obtain ⟨hcM, hsM⟩ := hMq
      haveI := hsM.toNontrivial
      haveI : Nontrivial ↥M :=
        CFSG.LocalAnalysis.GLTheoremA.K148FTwo.nontrivial_of_quotient (Subgroup.center ↥M)
      have hc : commutator ↥M = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a _
        rw [Subgroup.mem_centralizer_iff]
        intro b _
        have hb : (⟨(b : G), hMX b.2⟩ : ↥X) ∈ Subgroup.center ↥X :=
          h (Subgroup.mem_subgroupOf.2 b.2)
        have := Subgroup.mem_center_iff.1 hb ⟨(a : G), hMX a.2⟩
        exact Subtype.ext (congrArg Subtype.val this).symm
      rw [hcM] at hc
      exact top_ne_bot hc
  subst hMeq
  let eP : PQuot 3 M ≃* ↥M := (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hcenter : (Subgroup.center ↥M).map eP.symm.toMonoidHom = Subgroup.center (PQuot 3 M) :=
    Subgroup.map_center_eq eP.symm
  let eS : PSimple 3 M ≃* ↥M ⧸ Subgroup.center ↥M :=
    QuotientGroup.congr (Subgroup.center (PQuot 3 M)) (Subgroup.center ↥M) eP
      (by rw [← Subgroup.map_center_eq eP])
  rw [Nat.card_congr eS.toEquiv]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥M)).symm

private theorem k148Hold_g2_order_ne {a : ℕ} (ha : 1 ≤ a) :
    CFSG.Open.ordG2 (2 ^ a) ≠ 60 ∧ ∀ n : ℕ, 1 ≤ n → CFSG.Open.ordG2 (2 ^ a) ≠ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hodd : Odd (((2 ^ a) ^ 6 - 1) * ((2 ^ a) ^ 2 - 1)) :=
    (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one ha (by norm_num)).mul
      (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one ha (by norm_num))
  have heq : CFSG.Open.ordG2 (2 ^ a) = 2 ^ (6 * a) * (((2 ^ a) ^ 6 - 1) * ((2 ^ a) ^ 2 - 1)) := by
    unfold CFSG.Open.ordG2
    rw [show 2 ^ (6 * a) = (2 ^ a) ^ 6 by rw [mul_comm, pow_mul], mul_assoc]
  refine ⟨fun h => ?_, fun n hn h => ?_⟩
  · rw [heq] at h
    have h60 : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
    rw [h60] at h
    have := (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj hodd (by decide) h).1
    omega
  · rw [heq] at h
    have hodd' : Odd ((2 ^ n) ^ 2 - 1) :=
      CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hn (by norm_num)
    obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj hodd hodd' h
    subst h1
    obtain ⟨r, hr⟩ : ∃ r : ℕ, r = (2 ^ a) ^ 2 := ⟨_, rfl⟩
    have hr4 : 4 ≤ r := by
      rw [hr, ← pow_mul]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (a * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 : (2 ^ a) ^ 6 = r ^ 3 := by rw [hr]; ring
    have e2 : (2 ^ (6 * a)) ^ 2 = r ^ 6 := by rw [hr, ← pow_mul, ← pow_mul, ← pow_mul]; ring_nf
    rw [e1, ← hr, e2] at h2
    have h3 : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h6 : 1 ≤ r ^ 6 := Nat.one_le_pow _ _ (by omega)
    have hz : ((r : ℤ) ^ 3 - 1) * ((r : ℤ) - 1) = (r : ℤ) ^ 6 - 1 := by
      have := congrArg (fun x : ℕ => (x : ℤ)) h2
      push_cast [Nat.cast_sub h3, Nat.cast_sub h6, Nat.cast_sub (show 1 ≤ r by omega)] at this
      linarith
    have hr' : (4 : ℤ) ≤ r := by exact_mod_cast hr4
    nlinarith [sq_nonneg ((r : ℤ) ^ 2), sq_nonneg ((r : ℤ))]

private theorem k148Hold_6048_ne : (6048 : ℕ) ≠ 60 ∧ ∀ n : ℕ, 1 ≤ n → (6048 : ℕ) ≠ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  refine ⟨by norm_num, fun n hn h => ?_⟩
  have hodd' : Odd ((2 ^ n) ^ 2 - 1) :=
    CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hn (by norm_num)
  have h6048 : (6048 : ℕ) = 2 ^ 5 * 189 := by norm_num
  rw [h6048] at h
  obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj (by decide) hodd' h
  subst h1
  norm_num at h2

private theorem k148Hold_sl3_card_ne {f : ℕ} (hf : 2 ≤ f) {X z P : ℕ} (ε : Bool)
    (hX : X = (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * cond ε ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1))
    (hz : Odd z) (hP : P * z = X) : P ≠ 60 ∧ ∀ n : ℕ, 1 ≤ n → P ≠ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hf1 : 1 ≤ f := by omega
  have hoddX : Odd (((2 ^ f) ^ 2 - 1) * cond ε ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1)) := by
    refine (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hf1 (by norm_num)).mul ?_
    cases ε
    · exact CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_add_one hf1 (by norm_num)
    · exact CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hf1 (by norm_num)
  have hX' : X = 2 ^ (3 * f) * (((2 ^ f) ^ 2 - 1) * cond ε ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1)) := by
    rw [hX, show 2 ^ (3 * f) = (2 ^ f) ^ 3 by rw [mul_comm, pow_mul], mul_assoc]
  refine ⟨fun h => ?_, fun n hn h => ?_⟩
  · rw [h, hX'] at hP
    have e : 60 * z = 2 ^ 2 * (15 * z) := by ring
    rw [e] at hP
    have := (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj ((by decide : Odd 15).mul hz)
      hoddX hP).1
    omega
  · rw [h, hX'] at hP
    have hodd' : Odd ((2 ^ n) ^ 2 - 1) :=
      CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hn (by norm_num)
    have e : 2 ^ n * ((2 ^ n) ^ 2 - 1) * z = 2 ^ n * (((2 ^ n) ^ 2 - 1) * z) := by ring
    rw [e] at hP
    obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj (hodd'.mul hz) hoddX hP
    subst h1
    set q := 2 ^ f with hq
    have hq4 : 4 ≤ q := by
      rw [hq]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have e6 : (2 ^ (3 * f)) ^ 2 = q ^ 6 := by rw [hq, ← pow_mul, ← pow_mul]; ring_nf
    rw [e6] at h2
    have hz1 : 1 ≤ z := hz.pos
    have hle : ((q ^ 2 - 1) * cond ε (q ^ 3 - 1) (q ^ 3 + 1)) ≤ (q ^ 2 - 1) * (q ^ 3 + 1) := by
      apply Nat.mul_le_mul_left
      cases ε <;> simp <;> omega
    have hlt : (q ^ 2 - 1) * (q ^ 3 + 1) < q ^ 6 - 1 := by
      have h2 : 16 ≤ q ^ 2 := by nlinarith
      have h3 : 64 ≤ q ^ 3 := by nlinarith
      have e : q ^ 6 = q ^ 3 * q ^ 3 := by ring
      have e2 : q ^ 3 = q * q ^ 2 := by ring
      zify [show 1 ≤ q ^ 2 by omega, show 1 ≤ q ^ 6 by nlinarith]
      push_cast
      nlinarith
    have hge : q ^ 6 - 1 ≤ (q ^ 6 - 1) * z := Nat.le_mul_of_pos_right _ hz1
    omega

private theorem k148Hold_card_l2n {S : Type} [Group S] [Finite S] {n : ℕ} (h : catalogIs S (isL2n n)) :
    (n = 2 ∧ Nat.card S = 60) ∨ (1 ≤ n ∧ Nat.card S = 2 ^ n * ((2 ^ n) ^ 2 - 1)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact (show False from hi).elim
  | sporadic _ => exact (show False from hi).elim
  | alternating m hm =>
    obtain ⟨hn, rfl⟩ : n = 2 ∧ m = 5 := hi
    left
    refine ⟨hn, ?_⟩
    rw [CFSG.LocalAnalysis.GLTheoremA.CatDistinct.card_alternating_of_iso hm e]
    decide
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      rcases r with _ | _ | r
      · exact (show False from hi).elim
      · obtain ⟨hp, hn⟩ : q.p = 2 ∧ q.exponent = n := hi
        right
        refine ⟨hn ▸ q.exponent_pos, ?_⟩
        rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.A 1 q, hv⟩ S ⟨e⟩]
        show CFSG.Open.orderA 1 q.card = _
        rw [TauCeti.PrimePower.card_def, hp, hn]
        exact CFSG.LocalAnalysis.GLTheoremA.CatDistinct.orderA_one_eq (hn ▸ q.exponent_pos)
      · exact (show False from hi).elim
    | _ => exact (show False from hi).elim

private theorem k148Hold_three_dvd_sq_sub_one (f : ℕ) : 3 ∣ (2 ^ f) ^ 2 - 1 := by
  rw [← pow_mul, mul_comm, pow_mul]
  exact Nat.sub_one_dvd_pow_sub_one (2 ^ 2) f

private theorem k148Hold_g2_model {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : 2 ≤ f) (β : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) (hβ3 : β ^ 3 = 1) {X M : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)}
    (hX : ∀ x, x ∈ X ↔ β x = x) (hM : GLAPComponent 3 X M) {n : ℕ}
    (hL : catalogIs (PSimple 3 M) (isL2n n)) : n = f := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hF
  have hchar : ringChar F = 2 := ringChar.eq F 2
  have hchar3 : ringChar F ≠ 3 := by rw [hchar]; norm_num
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hf1 : 1 ≤ f := by omega
  have hZ : Subgroup.center (CFSG.Blueprint.Chevalley.adjointGroup .G2 F) = ⊥ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have h3G : ∀ a : ℕ, 3 ∣ CFSG.Open.ordG2 (2 ^ a) := fun a => by
    unfold CFSG.Open.ordG2
    exact Dvd.dvd.mul_left (k148Hold_three_dvd_sq_sub_one a) _
  by_cases hβ1 : β = 1
  ·
    exfalso
    subst hβ1
    have hXtop : X = ⊤ := Subgroup.ext fun z => by simp [hX]
    subst hXtop
    haveI : IsSimpleGroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 F) := CFSG.QuasithinUnique.Id2519.isSimpleGroup_adjointGroup_g2 (by omega)
    have hN : IsSimpleGroup ↥(⊤ : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) := Subgroup.topEquiv.isSimpleGroup
    have hcardG : Nat.card ↥(⊤ : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) = CFSG.Open.ordG2 (2 ^ f) := by
      rw [Subgroup.card_top, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hF]
    have hPS := k148Hold_card_psimple_of_simple le_rfl (fun a _ b _ => Subgroup.mem_top _) hN
      (by rw [hcardG]; exact h3G f) hM
    rw [hcardG] at hPS
    obtain ⟨h60, hL2⟩ := k148Hold_g2_order_ne hf1
    rcases k148Hold_card_l2n hL with ⟨-, h⟩ | ⟨hn, h⟩
    · exact h60 (hPS.symm.trans h)
    · exact hL2 n hn (hPS.symm.trans h)
  by_cases hin : CFSG.RankThree.PartTwo.KFacts.IsInnerAut β
  · obtain ⟨z, rfl⟩ := hin
    have hCz : X = Subgroup.centralizer ({z} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) := by
      ext x
      rw [hX, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
      constructor
      · intro h
        calc x * z = z * x * z⁻¹ * z := by rw [h]
          _ = z * x := by group
      · intro h
        rw [← h]
        group
    subst hCz
    have hz1 : z ≠ 1 := by
      rintro rfl
      exact hβ1 (by rw [map_one])
    have hz3 : z ^ 3 = 1 := by
      have hc : MulAut.conj (z ^ 3) = 1 := by rw [map_pow, hβ3]
      have hmem : z ^ 3 ∈ Subgroup.center (CFSG.Blueprint.Chevalley.adjointGroup .G2 F) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg := congrArg (fun φ : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 F) => φ g) hc
        simp only [MulAut.conj_apply, MulAut.one_apply] at hg
        calc g * z ^ 3 = z ^ 3 * g * (z ^ 3)⁻¹ * z ^ 3 := by rw [hg]
          _ = z ^ 3 * g := by group
      rw [hZ, Subgroup.mem_bot] at hmem
      exact hmem
    obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds F hchar3 h4 z hz3 hz1
    have hιinj : Function.Injective ((MulAut.conj g : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) : CFSG.Blueprint.Chevalley.adjointGroup .G2 F →* CFSG.Blueprint.Chevalley.adjointGroup .G2 F) :=
      (MulAut.conj g).injective
    have hCmap : (Subgroup.centralizer ({z} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))).map ((MulAut.conj g : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) : CFSG.Blueprint.Chevalley.adjointGroup .G2 F →* CFSG.Blueprint.Chevalley.adjointGroup .G2 F) =
        Subgroup.centralizer ({g * z * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) :=
      CFSG.RankThree.PartTwo.Sec4.Ronan148S.map_centralizer_singleton_equiv (MulAut.conj g) z
    have hM' := (CFSG.LocalAnalysis.GLTheoremA.T123C.glaPComponent_map_iff hιinj 3 _ _).2 hM
    rw [hCmap] at hM'
    have hL' := (CFSG.LocalAnalysis.GLTheoremA.T123C.catalogIs_pSimple_map_iff hιinj 3 M _).2 hL
    have hz'3 : (g * z * g⁻¹) ^ 3 = 1 := by
      rw [show g * z * g⁻¹ = MulAut.conj g z from rfl, ← map_pow, hz3, map_one]
    have hz'1 : g * z * g⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have : MulAut.conj g z = MulAut.conj g 1 := by rw [map_one]; exact h
      exact (MulAut.conj g).injective this
    rcases hg with hS | hLg
    ·
      exfalso
      obtain ⟨-, ⟨K', _, _, hK'⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec12.Hering129L.g2_centralizer_threeA hchar3 h4 hS hz'3 hz'1
      obtain ⟨hq, -⟩ := CFSG.RankThree.PartTwo.Sec19.SimsC198.G2.centralizer_threeA hchar h4 hS hz'3 hz'1
      obtain ⟨ε, hcardC, hzC⟩ : ∃ ε : Bool,
          Nat.card ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))) =
            (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * cond ε ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1) ∧
          Nat.card (Subgroup.center ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)))) = 3 := by
        rcases hK' with ⟨hK'c, hq1, ⟨e⟩⟩ | ⟨hK'c, hq2, ⟨e⟩⟩
        · refine ⟨true, ?_, ?_⟩
          · rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three, hK'c, hF]
            simp only [cond_true, mul_assoc]
          · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
            exact CFSG.Open.StatedCenterThree.card_center_statedSL_three (by rw [hK'c]; omega)
        · refine ⟨false, ?_, ?_⟩
          · rw [Nat.card_congr e.toEquiv,
              CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK'c, hF]
            simp only [cond_false]
          · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
            exact CFSG.Open.StatedCenterThree.card_center_statedSU_three hK'c (by omega)
      have hZ3 : IsPGroup 3 (Subgroup.center ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)))) :=
        IsPGroup.of_card (n := 1) (by rw [hzC, pow_one])
      have h3C : 3 ∣ Nat.card ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))) :=
        hzC ▸ Subgroup.card_subgroup_dvd_card _
      have hPS := k148Hold_card_psimple_of_quasisimple hq hZ3 h3C hM'
      have hodd : Odd (Nat.card (Subgroup.center ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))))) := by
        rw [hzC]; decide
      obtain ⟨h60, hL2⟩ := k148Hold_sl3_card_ne hf ε hcardC hodd hPS
      rcases k148Hold_card_l2n hL' with ⟨-, h⟩ | ⟨hn, h⟩
      · exact h60 h
      · exact hL2 n hn h
    ·
      obtain ⟨hcomm, -⟩ :=
        CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ThreeBCent_holds F hchar3 h4 _ hLg hz'3 hz'1
      obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := F)
      have hNX : CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 F ≤
          Subgroup.centralizer ({g * z * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) :=
        fun s hs => Subgroup.mem_centralizer_singleton_iff.2
          (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2Short_commute_g2Long hs hLg)
      haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
        CFSG.SeitzReduction.LinearPilot.isSimpleGroup_specialLinearGroup_two h4
      have hN : IsSimpleGroup ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 F) :=
        e.symm.isSimpleGroup
      have hcardS : Nat.card ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 F) =
          2 ^ f * ((2 ^ f) ^ 2 - 1) := by
        rw [← Nat.card_congr e.toEquiv]
        show Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = _
        rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF,
          show Finset.Icc 2 2 = {2} by decide, Finset.prod_singleton]
        norm_num
      have hPS := k148Hold_card_psimple_of_simple hNX hcomm hN
        (by rw [hcardS]; exact Dvd.dvd.mul_left (k148Hold_three_dvd_sq_sub_one f) _) hM'
      rw [hcardS] at hPS
      have hoddf : Odd ((2 ^ f) ^ 2 - 1) :=
        CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hf1 (by norm_num)
      rcases k148Hold_card_l2n hL' with ⟨hn2, h⟩ | ⟨hn, h⟩
      · rw [hPS, show (60 : ℕ) = 2 ^ 2 * 15 by norm_num] at h
        have := (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj hoddf (by decide) h).1
        omega
      · rw [hPS] at h
        have hoddn : Odd ((2 ^ n) ^ 2 - 1) :=
          CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hn (by norm_num)
        exact (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj hoddf hoddn h).1.symm
  ·
    exfalso
    obtain ⟨φ, hφ, k, hβk⟩ :=
      CFSG.RankThree.PartTwo.KFacts.g2_order_three_field_descent hchar3 h4 hβ3 hin
    obtain ⟨h3n, -⟩ :=
      CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two hf1 hF hφ
    obtain ⟨m, rfl⟩ := h3n
    have hcard : Nat.card (CFSG.LieType.Chevalley.fixSubfield φ) = 2 ^ m := by
      have h := CFSG.RankThree.PartTwo.KFacts.card_fixSubfield_pow φ
      rw [hφ, hF, show 2 ^ (3 * m) = (2 ^ m) ^ 3 by rw [← pow_mul, mul_comm]] at h
      exact Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) h
    have hm1 : 1 ≤ m := by omega
    have hfixeq : CFSG.RankThree.PartTwo.Sec4.autFix (CFSG.RankThree.PartTwo.KFacts.g2FieldHom F φ) =
        (CFSG.RankThree.PartTwo.KFacts.g2Incl φ).range := by
      ext h
      rw [CFSG.RankThree.PartTwo.Sec4.mem_autFix, CFSG.RankThree.PartTwo.KFacts.mem_range_g2Incl_iff hchar φ]
    have hCeq : X = CFSG.RankThree.PartTwo.Sec4.autFix β :=
      Subgroup.ext fun z => (hX z).trans CFSG.RankThree.PartTwo.Sec4.mem_autFix.symm
    have eα : ↥(CFSG.RankThree.PartTwo.Sec4.autFix β) ≃*
        CFSG.Blueprint.Chevalley.adjointGroup .G2 (CFSG.LieType.Chevalley.fixSubfield φ) := by
      rw [hβk]
      exact ((CFSG.RankThree.PartTwo.Sec4.RonanK429Lie.autFixConjEquiv (MulAut.conj k)
        (CFSG.RankThree.PartTwo.KFacts.g2FieldHom F φ)).trans (MulEquiv.subgroupCongr hfixeq)).trans
          (MonoidHom.ofInjective (CFSG.RankThree.PartTwo.KFacts.g2Incl_injective φ)).symm
    subst hCeq
    by_cases hm : m = 1
    ·
      subst hm
      obtain ⟨hsimple, hcard'⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.g2Two_derived_exc
          (k := CFSG.LieType.Chevalley.fixSubfield φ) (by rw [hcard]; norm_num)
      have hcommeq : (commutator ↥(CFSG.RankThree.PartTwo.Sec4.autFix β)).map eα.toMonoidHom =
          commutator ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (CFSG.LieType.Chevalley.fixSubfield φ)) := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          (MonoidHom.range_eq_top (f := eα.toMonoidHom)).2 eα.surjective]
      let eD : ↥(commutator ↥(CFSG.RankThree.PartTwo.Sec4.autFix β)) ≃*
          ↥(commutator ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (CFSG.LieType.Chevalley.fixSubfield φ))) :=
        ((commutator _).equivMapOfInjective eα.toMonoidHom eα.injective).trans
          (MulEquiv.subgroupCongr hcommeq)
      haveI := hsimple
      have hR : IsSimpleGroup ↥(commutator ↥(CFSG.RankThree.PartTwo.Sec4.autFix β)) := eD.isSimpleGroup
      have hN := CFSG.LocalAnalysis.GLTheoremA.K148FTwo.simple_derivedIn hR
      have hcardN : Nat.card ↥(CFSG.LocalAnalysis.GLTheoremA.K148FTwo.derivedIn
          (CFSG.RankThree.PartTwo.Sec4.autFix β)) = 6048 := by
        unfold CFSG.LocalAnalysis.GLTheoremA.K148FTwo.derivedIn
        rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Nat.card_congr eD.toEquiv, hcard']
      have hcomm : ∀ a ∈ CFSG.RankThree.PartTwo.Sec4.autFix β, ∀ b ∈ CFSG.RankThree.PartTwo.Sec4.autFix β,
          a * b * a⁻¹ * b⁻¹ ∈ CFSG.LocalAnalysis.GLTheoremA.K148FTwo.derivedIn
            (CFSG.RankThree.PartTwo.Sec4.autFix β) := by
        intro a ha b hb
        unfold CFSG.LocalAnalysis.GLTheoremA.K148FTwo.derivedIn
        set a' : ↥(CFSG.RankThree.PartTwo.Sec4.autFix β) := ⟨a, ha⟩
        set b' : ↥(CFSG.RankThree.PartTwo.Sec4.autFix β) := ⟨b, hb⟩
        refine Subgroup.mem_map.2 ⟨a' * b' * a'⁻¹ * b'⁻¹,
          Subgroup.commutator_mem_commutator (Subgroup.mem_top a') (Subgroup.mem_top b'), ?_⟩
        simp [a', b']
      have hPS := k148Hold_card_psimple_of_simple
        (CFSG.LocalAnalysis.GLTheoremA.K148FTwo.derivedIn_le _) hcomm hN (by rw [hcardN]; norm_num) hM
      rw [hcardN] at hPS
      obtain ⟨h60, hL2⟩ := k148Hold_6048_ne
      rcases k148Hold_card_l2n hL with ⟨-, h⟩ | ⟨hn, h⟩
      · exact h60 (hPS.symm.trans h)
      · exact hL2 n hn (hPS.symm.trans h)
    ·
      haveI : IsSimpleGroup
          (CFSG.Blueprint.Chevalley.adjointGroup .G2 (CFSG.LieType.Chevalley.fixSubfield φ)) :=
        CFSG.QuasithinUnique.Id2519.isSimpleGroup_adjointGroup_g2 (by
          rw [hcard]
          calc 3 ≤ 2 ^ 2 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega))
      have hN : IsSimpleGroup ↥(CFSG.RankThree.PartTwo.Sec4.autFix β) := eα.isSimpleGroup
      have hcardX : Nat.card ↥(CFSG.RankThree.PartTwo.Sec4.autFix β) = CFSG.Open.ordG2 (2 ^ m) := by
        rw [Nat.card_congr eα.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hcard]
      have hPS := k148Hold_card_psimple_of_simple le_rfl
        (fun a ha b hb => Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
          (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)) hN (by rw [hcardX]; exact h3G m) hM
      rw [hcardX] at hPS
      obtain ⟨h60, hL2⟩ := k148Hold_g2_order_ne hm1
      rcases k148Hold_card_l2n hL with ⟨-, h⟩ | ⟨hn, h⟩
      · exact h60 (hPS.symm.trans h)
      · exact hL2 n hn (hPS.symm.trans h)

theorem k148FG2CompFact_holds : K148FG2CompFact := by
  intro C _ _ H f y hH hyN hy3 M hM n hL
  obtain ⟨hf, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.T266.G2Holds.g2_adjoint_equiv hH
  refine ⟨hf, ?_⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let β' : MulAut ↥H := H.normalizerMonoidHom ⟨y, hyN⟩
  have hβ'3 : β' ^ 3 = 1 := by
    show H.normalizerMonoidHom ⟨y, hyN⟩ ^ 3 = 1
    rw [← map_pow]
    have h1 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (H : Set C))) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [h1, map_one]
  have hβ'app : ∀ a : ↥H, (β' a : C) = y * a * y⁻¹ := fun a =>
    Subgroup.normalizerMonoidHom_apply_apply_coe H ⟨y, hyN⟩ a
  let β : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)) := MulAut.congr e.symm β'
  have hβ3 : β ^ 3 = 1 := by
    show MulAut.congr e.symm β' ^ 3 = 1
    rw [← map_pow, hβ'3, map_one]
  have hβapp : ∀ x, β x = e.symm (β' (e x)) := fun x => rfl
  have hfix : ∀ x, β x = x ↔ ((e x : ↥H) : C) * y = y * (e x : C) := by
    intro x
    rw [hβapp, MulEquiv.symm_apply_eq, ← SetLike.coe_eq_coe, hβ'app]
    constructor
    · intro h
      calc ((e x : ↥H) : C) * y = y * (e x : C) * y⁻¹ * y := by rw [h]
        _ = y * (e x : C) := by group
    · intro h
      rw [← h]
      group
  let ι : CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f) →* C := H.subtype.comp e.toMonoidHom
  have hιinj : Function.Injective ι := H.subtype_injective.comp e.injective
  have hXeq : (CFSG.RankThree.PartTwo.Sec4.autFix β).map ι = H ⊓ Subgroup.centralizer ({y} : Set C) := by
    ext c
    rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [CFSG.RankThree.PartTwo.Sec4.mem_autFix, hfix] at hx
      exact ⟨(e x).2, hx⟩
    · rintro ⟨hcH, hcy⟩
      refine ⟨e.symm ⟨c, hcH⟩, ?_, ?_⟩
      · rw [CFSG.RankThree.PartTwo.Sec4.mem_autFix, hfix, MulEquiv.apply_symm_apply]
        exact hcy
      · show ((e (e.symm ⟨c, hcH⟩) : ↥H) : C) = c
        rw [MulEquiv.apply_symm_apply]
  have hMle : M ≤ ι.range := by
    have h1 : M ≤ H ⊓ Subgroup.centralizer ({y} : Set C) := hM.1
    rw [← hXeq] at h1
    exact h1.trans (Subgroup.map_le_range ι _)
  obtain ⟨M₀, rfl⟩ : ∃ M₀ : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)), M₀.map ι = M := ⟨_, Subgroup.map_comap_eq_self hMle⟩
  rw [← hXeq] at hM
  have hM₀ := (CFSG.LocalAnalysis.GLTheoremA.T123C.glaPComponent_map_iff hιinj 3 _ _).1 hM
  have hL₀ := (CFSG.LocalAnalysis.GLTheoremA.T123C.catalogIs_pSimple_map_iff hιinj 3 M₀ _).1 hL
  exact k148Hold_g2_model hF hf β hβ3 (fun x => CFSG.RankThree.PartTwo.Sec4.mem_autFix) hM₀ hL₀

end CFSG.LocalAnalysis.GLTheoremA

end
