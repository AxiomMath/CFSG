module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148FFacts
import CFSG.LocalAnalysis.GLTheoremA.CatA.K148FC1Layer2
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusionTrialityConj
import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoDFourAux
import CFSG.LocalAnalysis.GLTheoremA.CatA.T266G2Holds
import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4OuterAux.Two
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K148FC1

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor)

private theorem k148fc1_pp_eq {q q' : TauCeti.PrimePower} (hq : q.p = 2) (h : q'.card = q.card) :
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

private theorem k148fc1_g2_ne_pgl {f : ℕ} (hf : 1 ≤ f) (π : Bool) :
    CFSG.Open.ordG2 (2 ^ f) ≠
      (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1) := by
  intro h
  have hodd1 : Odd (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) :=
    (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hf (by norm_num)).mul
      (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hf (by norm_num))
  have hodd2 : Odd (((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1)) := by
    refine (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hf (by norm_num)).mul ?_
    cases π
    · exact CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_add_one hf (by norm_num)
    · exact CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hf (by norm_num)
  have e1 : CFSG.Open.ordG2 (2 ^ f) = 2 ^ (6 * f) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) := by
    unfold CFSG.Open.ordG2
    rw [show 2 ^ (6 * f) = (2 ^ f) ^ 6 by rw [mul_comm, pow_mul], mul_assoc]
  have e2 : (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1) =
      2 ^ (3 * f) * (((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1)) := by
    rw [show 2 ^ (3 * f) = (2 ^ f) ^ 3 by rw [mul_comm, pow_mul], mul_assoc]
  rw [e1, e2] at h
  have := (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj hodd1 hodd2 h).1
  omega

section Certified


private theorem k148fc1_model {P : Type} [Group P] {q : TauCeti.PrimePower} (hq : q.p = 2)
    (hcat : catalogIs P (CFSG.LocalAnalysis.GLTheoremA.I2023.isTD4Of q)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (2 ^ q.exponent) ^ 3 ∧ (∀ c, σ c = c ^ (2 ^ q.exponent)) ∧
      Nonempty (P ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨d, hv, hP, ⟨eS⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  cases d with
  | trialityD4 q' =>
    have hP' : q'.card = q.card := hP
    obtain ⟨hp2, hn⟩ := k148fc1_pp_eq hq hP'
    obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eC⟩⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q' hv
    rw [hp2, hn] at hK
    simp only [hp2, hn] at hσ
    exact ⟨K, inferInstance, inferInstance, σ, hK, hσ, ⟨eS.trans eC⟩⟩
  | _ => exact hP.elim

private theorem k148fc1_from_model {P : Type} [Group P] [Finite P] {f : ℕ} (hf : 2 ≤ f)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (ε : P ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (τ : MulAut P) (τ₀ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hετ : ∀ x, ε (τ x) = τ₀ (ε x))
    (hτ₀ : τ₀ ⟨CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.d4T0 σ,
        CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.d4T0_mem σ⟩ =
      ⟨CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.d4T0 σ, CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.d4T0_mem σ⟩)
    (hτ3 : τ ^ 3 = 1) (hFG2 : catalogIs ↥(CFSG.RankThree.PartTwo.Sec4.autFix τ) (isG2n f))
    (c : P) (hc3 : c ^ 3 = 1) (hτc : τ c = c)
    (hS' : ∃ S' : Subgroup P, GLAPComponent 3 (CFSG.RankThree.PartTwo.Sec4.autFix τ ⊓
        Subgroup.centralizer ({c} : Set P)) S' ∧ catalogIs (PSimple 3 S') (isL2n f)) :
    ∃ M₀ : Subgroup P, GLAPComponent 3 (Subgroup.centralizer ({c} : Set P)) M₀ ∧
      (∀ M : Subgroup P, GLAPComponent 3 (Subgroup.centralizer ({c} : Set P)) M → M = M₀) ∧
      catalogIs (PSimple 3 M₀) (isL2n (3 * f)) ∧ (∀ m ∈ M₀, τ m ∈ M₀) ∧
      ∃ φ : MulAut (PQuot 3 M₀), φ ^ 3 = 1 ∧ ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut φ ∧
        (∀ m : M₀, ∃ m' : M₀, (m' : P) = τ⁻¹ m ∧ φ (QuotientGroup.mk m) = QuotientGroup.mk m') ∧
        K148FFieldAut 3 (PQuot 3 M₀) φ := by
  classical
  have hσ3' : ∀ c : K, σ (σ (σ c)) = c := CFSG.LieType.Chevalley.ringEquiv_cube_apply_eq hK hσ
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by simpa [pow_succ] using hσ3' c
  have h3 : ¬ 3 ∣ 2 ^ f := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  set S₀ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom with hS₀
  have hinj := CFSG.LieType.Chevalley.orbitRankOneHom_injective_D4 hσ3
    CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4Outer
  have hle := CFSG.LieType.Chevalley.range_orbitRankOneHom_le (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom) CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4Outer
  let e₀ : Matrix.SpecialLinearGroup (Fin 2)
      (CFSG.LieType.Chevalley.orbitField TwistTag.D4 K σ.toRingHom
        CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4Outer) ≃* ↥S₀ :=
    (MonoidHom.ofInjective hinj).trans (Subgroup.subgroupOfEquivOfLe hle).symm
  have hmem : ∀ c : K, c ∈ CFSG.LieType.Chevalley.orbitField TwistTag.D4 K σ.toRingHom
      CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4Outer := by
    intro c
    rw [CFSG.LieType.Chevalley.orbitField_D4_zero_eq_top σ hσ3']
    exact Subfield.mem_top c
  have hcardF : Nat.card (CFSG.LieType.Chevalley.orbitField TwistTag.D4 K σ.toRingHom
      CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4Outer) = 2 ^ (3 * f) := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hmem), hK, ← pow_mul, mul_comm]
  haveI : Finite (CFSG.LieType.Chevalley.orbitField TwistTag.D4 K σ.toRingHom
      CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4Outer) := Subtype.finite
  set S : Subgroup P := S₀.map (ε.symm : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* P) with hS
  have hmemS : ∀ p : P, p ∈ S ↔ ε p ∈ S₀ := fun p => by
    constructor
    · rintro ⟨y, hy, rfl⟩
      show ε (ε.symm y) ∈ S₀
      rw [MulEquiv.apply_symm_apply]
      exact hy
    · intro hp
      exact ⟨ε p, hp, ε.symm_apply_apply p⟩
  let eSL : Matrix.SpecialLinearGroup (Fin 2)
      (CFSG.LieType.Chevalley.orbitField TwistTag.D4 K σ.toRingHom
        CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4Outer) ≃* ↥S :=
    e₀.trans (MulEquiv.subgroupMap ε.symm S₀)
  set t₀ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    ⟨CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.d4T0 σ, CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.d4T0_mem σ⟩
    with ht₀
  have ht₀C : t₀ ∈ Subgroup.centralizer (S₀ : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.d4T0_mem_centralizer σ
  obtain ⟨ht₀3', ht₀1'⟩ := CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo.d4T0_pow_three hσ3
  have ht₀3 : t₀ ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact ht₀3')
  have ht₀1 : t₀ ≠ 1 := fun h => ht₀1' (congrArg Subtype.val h)
  have hεC : ∀ (t p : P), p ∈ Subgroup.centralizer ({t} : Set P) ↔
      ε p ∈ Subgroup.centralizer ({ε t} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro t p
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact ε.injective.eq_iff.symm
  have hεCS : ∀ t : P, t ∈ Subgroup.centralizer (S : Set P) ↔
      ε t ∈ Subgroup.centralizer (S₀ : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro t
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h s₀ hs₀
      have hs : ε.symm s₀ ∈ S := (hmemS _).2 (by rw [MulEquiv.apply_symm_apply]; exact hs₀)
      have := congrArg ε (h _ hs)
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
      exact this
    · intro h s hs
      apply ε.injective
      rw [map_mul, map_mul]
      exact h _ ((hmemS s).1 hs)
  have htPS : ε.symm t₀ ∈ Subgroup.centralizer (S : Set P) := by
    rw [hεCS, MulEquiv.apply_symm_apply]
    exact ht₀C
  have htPτ : τ (ε.symm t₀) = ε.symm t₀ := by
    apply ε.injective
    rw [hετ, MulEquiv.apply_symm_apply, hτ₀]
  have htP3 : (ε.symm t₀) ^ 3 = 1 := by rw [← map_pow, ht₀3, map_one]
  have htP1 : ε.symm t₀ ≠ 1 := fun h => ht₀1 (by rw [← ε.apply_symm_apply t₀, h, map_one])
  have hB : ∀ t ∈ Subgroup.centralizer (S : Set P), t ^ 3 = 1 → t ≠ 1 →
      ∀ x ∈ Subgroup.centralizer ({t} : Set P), ∀ y ∈ Subgroup.centralizer ({t} : Set P),
        x * y * x⁻¹ * y⁻¹ ∈ S := by
    intro t ht ht3 ht1 x hx y hy
    have hBC := (CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeBCent_holds K (2 ^ f) σ hK hσ h3 (ε t)
      ((hεCS t).1 ht) (by rw [← map_pow, ht3, map_one])
      (fun h => ht1 (ε.injective (by rw [h, map_one])))).1 (ε x) ((hεC t x).1 hx) (ε y) ((hεC t y).1 hy)
    rw [hmemS, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hBC
  exact k148fc1_core hf τ hτ3 hFG2 hcardF eSL htPS htPτ htP3 htP1 hB c hc3 hτc hS'

theorem k148FC1LayerFact_holds : K148FC1LayerFact := by
  intro P _ _ q hq2 hf2 hcat τ hτ3 hτi hFG2 c hc3 hτc hS'
  classical
  obtain ⟨K, _, _, σ, hK, hσ, ⟨eS⟩⟩ := k148fc1_model hq2 hcat
  set n := q.exponent with hn
  have hn1 : 1 ≤ n := q.exponent_pos
  set β := MulAut.congr eS τ with hβ
  have hβx : ∀ x : P, β (eS x) = eS (τ x) := fun x => by
    show eS (τ (eS.symm (eS x))) = eS (τ x)
    rw [MulEquiv.symm_apply_apply]
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hτ3, map_one]
  have hβout : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut β := by
    rintro ⟨g, hg⟩
    apply hτi
    refine ⟨eS.symm g, MulEquiv.ext fun y => ?_⟩
    apply eS.injective
    have key := congrArg (fun ψ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) => ψ (eS y)) hg
    simp only [MulAut.conj_apply] at key
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hβx]
    exact key
  have hd4T0 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusion.fieldActor_d4T0 σ
  rcases CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hn1 hK hσ
      hβ3 hβout with ⟨γ, hγ | hγ⟩ | he2
  ·
    refine k148fc1_from_model hf2 hK hσ (eS.trans γ⁻¹) τ (fieldActor σ σ) (fun x => ?_) hd4T0 hτ3 hFG2 c hc3 hτc
      hS'
    show γ⁻¹ (eS (τ x)) = fieldActor σ σ (γ⁻¹ (eS x))
    rw [← hβx, hγ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  ·
    refine k148fc1_from_model hf2 hK hσ (eS.trans γ⁻¹) τ (fieldActor σ σ)⁻¹ (fun x => ?_) ?_ hτ3 hFG2 c hc3 hτc
      hS'
    · show γ⁻¹ (eS (τ x)) = (fieldActor σ σ)⁻¹ (γ⁻¹ (eS x))
      rw [← hβx, hγ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    · calc (fieldActor σ σ)⁻¹ ⟨CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.d4T0 σ,
            CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.d4T0_mem σ⟩ =
          (fieldActor σ σ)⁻¹ (fieldActor σ σ ⟨CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.d4T0 σ,
            CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.d4T0_mem σ⟩) := by rw [hd4T0]
        _ = _ := MulAut.inv_apply_self _ _ _
  ·
    exfalso
    obtain ⟨e2⟩ := he2
    obtain ⟨-, ⟨eG⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.T266.G2Holds.g2_adjoint_equiv hFG2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcardFix : Nat.card ↥(CFSG.RankThree.PartTwo.Sec4.autFix τ) = CFSG.Open.ordG2 (2 ^ n) := by
      rw [← Nat.card_congr eG.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2,
        GaloisField.card 2 n (by omega)]
    let eF : ↥(CFSG.RankThree.PartTwo.Sec4.autFix τ) ≃* ↥(CFSG.RankThree.PartTwo.Sec4.autFix β) :=
      (CFSG.RankThree.PartTwo.Sec4.autFixCongrEquiv eS τ).symm
    rcases Nat.even_or_odd n with hne | hno
    · obtain ⟨F, _, _, hF, ⟨e3⟩⟩ := CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0Even_holds n hne hn1 K σ hK hσ
      have hPi : CFSG.RankThree.PartTwo.Sec4.PiField true 2 n F := ⟨Nat.prime_two, hn1, hF⟩
      have h := Nat.card_congr ((eF.trans e2).trans e3).toEquiv
      rw [hcardFix, CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.card_projImage_glPi_three hPi] at h
      exact k148fc1_g2_ne_pgl hn1 true h
    · obtain ⟨F, _, _, hF, ⟨e3⟩⟩ := CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0_holds n hno K σ hK hσ
      have hPi : CFSG.RankThree.PartTwo.Sec4.PiField false 2 n F := ⟨Nat.prime_two, hn1, hF⟩
      have h := Nat.card_congr ((eF.trans e2).trans e3).toEquiv
      rw [hcardFix, CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.card_projImage_glPi_three hPi] at h
      exact k148fc1_g2_ne_pgl hn1 false h

end Certified

end CFSG.LocalAnalysis.GLTheoremA.K148FC1

end
