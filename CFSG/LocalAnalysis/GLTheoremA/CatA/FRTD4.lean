module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQTD4
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityTransposition
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LieType.Chevalley.GraphFixedParameterFields
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.PartOne.S11d.OrthSubfieldDickson

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.Coordinator CFSG.Assembly CFSG.StandardType


theorem trialityD4_outer_fixed_equiv {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime)
    (hp5 : 5 ≤ p) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hαp : α ^ p = 1)
    (hαin : α ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ (f₀ : ℕ) (k₀ : Type) (_ : Field k₀) (_ : Finite k₀) (σ₀ : k₀ ≃+* k₀),
      f = p * f₀ ∧ Nat.card k₀ = (ℓ ^ f₀) ^ 3 ∧ (∀ c, σ₀ c = c ^ ((ℓ ^ f₀) ^ (p % 3))) ∧ p % 3 ≠ 0 ∧
        Nonempty (↥(FP.fixSub α) ≃*
          ↥(graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hα1 : α ≠ 1 := fun h => hαin (h ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hαord : orderOf α = p := orderOf_eq_prime hαp hα1
  obtain ⟨-, hcyc, Θ, hΘ, -⟩ := triality_normal_form_data hℓ hf K hK σ hσ
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK σ hσ Θ hΘ hp
      (by omega) ⊤ le_top ⟨α, Subgroup.mem_top _⟩ hαin
      (by rw [Subgroup.orderOf_mk]; exact hαord)
  obtain ⟨f', hff'⟩ := hpf
  have hd : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with h | h
    · rw [h, mul_zero] at hff'
      omega
    · exact h
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨φ, hφ, hφord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 3 * f) hK3
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ ℓ ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega) (by rw [hφord, hff']; exact ⟨p, by ring⟩),
      hφord, hff', show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers (Θ α) = Subgroup.zpowers δc := by
    have h1 : Nat.card (Subgroup.zpowers (Θ α)) = p := by rw [Nat.card_zpowers]; exact hηord
    have h2 : Nat.card (Subgroup.zpowers δc) = p := by rw [Nat.card_zpowers, hδcord]
    have : Finite (Subgroup.zpowers (Θ α)) :=
      Nat.finite_of_card_ne_zero (by rw [h1]; exact hp.ne_zero)
    have : Finite (Subgroup.zpowers δc) :=
      Nat.finite_of_card_ne_zero (by rw [h2]; exact hp.ne_zero)
    exact IsCyclic.subgroup_eq_iff_card_eq.mpr (h1.trans h2.symm)
  have hfix_eq : fixedSubgroup (fieldActor (t := TwistTag.D4) σ (Θ α)) = fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc) := by
    have h := CFSG.RankThree.PartOne.CTP.fixedSubgroup_eq_of_zpowers_eq
      (fieldActorHom (t := TwistTag.D4) σ) hzp
    ext x
    exact SetLike.ext_iff.1 h x
  have hK' : Nat.card K = ℓ ^ (3 * f' * p) := by
    rw [hK3, hff']
    ring_nf
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (f' * p) := fun c => by rw [hσ c, hff', mul_comm p f']
  obtain ⟨-, -, hk, hres, -, -, hfixJ, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd hp.two_le hm3 K hK' σ hσ'
      δc hδc
  have e3 : ↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc)) ≃*
      ↥(trialityFieldImage σ δc) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  have e4 : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
      (fixSubfieldRestrict σ δc).toRingHom) ≃* ↥(trialityFieldImage σ δc) :=
    Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective (fixSubfield δc).subtype)
  have : Finite (fixSubfield δc) := Subtype.finite
  have : Fintype (fixSubfield δc) := Fintype.ofFinite _
  have hcardK0 : Fintype.card (fixSubfield δc) = ℓ ^ (3 * f') := by
    rw [← Nat.card_eq_fintype_card, hk]
  have hσ0pow : ∀ c : fixSubfield δc, fixSubfieldRestrict σ δc c = c ^ ℓ ^ (f' * p) := fun c =>
    Subtype.ext (by rw [hres c, hσ', SubmonoidClass.coe_pow])
  have hj : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : p % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    omega
  have hpowj : ∀ c : fixSubfield δc, c ^ (ℓ ^ (3 * f')) ^ (p / 3) = c := fun c => by
    have h := FiniteField.pow_card_pow (p / 3) c
    rwa [hcardK0] at h
  have hσ0 : ∀ c : fixSubfield δc,
      (fixSubfieldRestrict σ δc).toRingHom c = c ^ (ℓ ^ f') ^ (p % 3) := fun c => by
    have h2 : ℓ ^ (f' * p) = (ℓ ^ (3 * f')) ^ (p / 3) * (ℓ ^ f') ^ (p % 3) := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      calc f' * p = f' * (3 * (p / 3) + p % 3) := by rw [Nat.div_add_mod]
        _ = 3 * f' * (p / 3) + f' * (p % 3) := by ring
    have h3 : (fixSubfieldRestrict σ δc).toRingHom c = c ^ ℓ ^ (f' * p) := hσ0pow c
    rw [h3, h2, pow_mul, hpowj c]
  have hp3 : p % 3 ≠ 0 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
    omega
  have eα : ↥(FP.fixSub α) ≃* ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
      (fixSubfieldRestrict σ δc).toRingHom) :=
    (fixSubEquivConj (MulAut.conj h₀) α).trans ((MulEquiv.subgroupCongr (congrArg FP.fixSub hh₀)).trans
      ((MulEquiv.subgroupCongr hfix_eq).trans (e3.trans e4.symm)))
  exact ⟨f', ↥(fixSubfield δc), inferInstance, inferInstance, fixSubfieldRestrict σ δc, hff',
    by rw [hk, ← pow_mul, mul_comm], hσ0, hp3, ⟨eα⟩⟩

theorem recipe_equiv_graph (k : Type) [Field k] [Finite k] (f' : ℕ) (hf' : 1 ≤ f')
    (hk : Nat.card k = (2 ^ f') ^ 3) (σ' : k ≃+* k) (hσ' : ∀ c, σ' c = c ^ 2 ^ f') :
    Nonempty (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 k LargeEvenRhoD4 f') ≃*
      graphFixedRootGroup TwistTag.D4 k σ'.toRingHom) := by
  obtain ⟨e₁⟩ := centerQuot_twistedH_equiv k TwistTag.D4 f' σ'.toRingHom hσ'
  have hperf := (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two hf' k hk σ'.toRingHom
    hσ').2.2.1
  obtain ⟨e₂⟩ := nonempty_derivedCentralQuotient_equiv hperf
    (exceptional_fixed_center_trivial TwistTag.D4 k σ')
  exact ⟨e₁.trans e₂⟩

theorem graph_orientation_equiv (k : Type) [Field k] (σ' : k ≃+* k) (hσ3 : σ' ^ 3 = 1) :
    Nonempty (↥(graphFixedRootGroup TwistTag.D4 k σ'.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 k (σ' ^ 2).toRingHom)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨e, -⟩, -⟩ :=
    CFSG.RankThree.Chevalley.triality_diagram_transposition_exchanges_field_orientations k σ' hσ3
  exact ⟨e⟩

theorem subBody_td4 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (I F : Set (MulAut (LargeEvenCenterQuot
      (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)))) (hF : FQ.InnFree p F) :
    ∀ f ∈ F, orderOf f = p → p ∣ n ∧
      ∃ D : Subgroup (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)),
        SubfieldGrp f D ∧ LargeEvenRecipeTwisted LargeEvenCartanD4 LargeEvenRhoD4 3 (n / p)
          (fun R' _ _ _ => Nonempty (↥D ≃* R')) := by
  intro f hf hord
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  have hchev : ChevalleyExceptionalModel
      (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n))
      .trialityD4 2 n :=
    ⟨⟨Nat.prime_two, hn, rfl⟩, twistedChevalleyModel_largeEven .D4 hK⟩
  obtain ⟨K', _, _, σ, hcard', hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hn hchev.2
  have hfp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  have hβp : MulAut.congr e f ^ p = 1 := by rw [← map_pow, hfp, map_one]
  have hβout : MulAut.congr e f ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) :=
    fun hin => hF f hf hord ((FQ.congr_mem_range_conj e f).1 hin)
  obtain ⟨f₀, k₀, hk₀F, hk₀fin, σ₀, hf0, hk₀card, hσ₀, hp3', ⟨eα⟩⟩ :=
    trialityD4_outer_fixed_equiv Nat.prime_two hn hp hp5 K' hcard' σ hσ (MulAut.congr e f) hβp hβout
  have hf1 : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf0; omega
    · exact h0
  have hdiv : n / p = f₀ := by rw [hf0, Nat.mul_div_cancel_left _ hp.pos]
  refine ⟨⟨f₀, by rw [hf0, mul_comm]⟩, FP.fixSub f,
    ⟨le_rfl, Subgroup.commutator_le_of_le le_rfl le_rfl, ?_⟩, ?_⟩
  · rw [Subgroup.relIndex_self]; exact odd_one
  obtain ⟨σ', hσ'', hσ'ord, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf1
    k₀ hk₀card
  obtain ⟨eR⟩ := recipe_equiv_graph k₀ f₀ hf1 hk₀card σ' hσ''
  have e₁ : ↥(FP.fixSub f) ≃* ↥(graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom) :=
    (fixSubEquivCongr e f).trans eα
  have hj : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have e₂ : Nonempty (↥(graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 k₀ σ'.toRingHom)) := by
    rcases hj with hj | hj
    · have : σ₀ = σ' := RingEquiv.ext fun c => by rw [hσ₀, hσ'', hj, pow_one]
      subst this
      exact ⟨MulEquiv.refl _⟩
    · have hσ3 : σ' ^ 3 = 1 := by
        have := pow_orderOf_eq_one σ'
        rwa [hσ'ord] at this
      obtain ⟨eo⟩ := graph_orientation_equiv k₀ σ' hσ3
      have : σ₀ = σ' ^ 2 := RingEquiv.ext fun c => by
        rw [hσ₀, hj, show (σ' ^ 2) c = σ' (σ' c) by rw [pow_two]; rfl, hσ'', hσ'', sq (2 ^ f₀),
          pow_mul]
      subst this
      exact ⟨eo.symm⟩
  obtain ⟨e₂⟩ := e₂
  rw [hdiv]
  exact ⟨k₀, hk₀F, hk₀fin, hk₀card, ⟨(e₁.trans e₂).trans eR.symm⟩⟩

end FR

end CFSG.LocalAnalysis.GLTheoremA
