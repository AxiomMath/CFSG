module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRLift
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)


@[expose] def l154ExcTits : TauCeti.CFSGIndex → Prop :=
  onLie fun | .tits => True | _ => False

theorem l154_oddInner_of_card_outer_two {S : Type} [Group S] (h : Nat.card (OuterAutomorphisms.Outer S) = 2) :
    ∀ φ : MulAut S, Odd (orderOf φ) → ∃ g : S, φ = MulAut.conj g := by
  intro φ hφ
  have h1 : orderOf (QuotientGroup.mk' (OuterAutomorphisms.inner S) φ) ∣ orderOf φ :=
    orderOf_map_dvd (QuotientGroup.mk' (OuterAutomorphisms.inner S)) φ
  have h2 : orderOf (QuotientGroup.mk' (OuterAutomorphisms.inner S) φ) ∣ 2 := by
    rw [← h]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk' (OuterAutomorphisms.inner S) φ) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · rw [h] at h1
      exact absurd (hφ.of_dvd_nat h1) (by decide)
  have h5 : QuotientGroup.mk' (OuterAutomorphisms.inner S) φ = 1 := orderOf_eq_one_iff.1 h3
  have h6 : φ ∈ OuterAutomorphisms.inner S := (QuotientGroup.eq_one_iff φ).1 h5
  obtain ⟨g, hg⟩ := h6
  exact ⟨g, hg.symm⟩

section TitsOut


theorem l154_oddInner_of_tits {S : Type} [Group S] (h : catalogIs S l154ExcTits) :
    ∀ φ : MulAut S, Odd (orderOf φ) → ∃ g : S, φ = MulAut.conj g := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | tits =>
      exact l154_oddInner_of_card_outer_two
        (CFSG.AGLEmbeddingD2.card_outer_tits_of_mulEquiv ⟨.tits, hv⟩ rfl e)
    | _ => exact hi.elim

end TitsOut

section Certs


theorem l154NIDOn_tits : L154NIDOn l154ExcTits := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hQ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  exact (l154_false_of_odd_inner hp hp2 hK hKc hyN hyp hField (l154_oddInner_of_tits hQ)).elim

theorem l154TD4On_tits : L154TD4On l154ExcTits := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hQ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  exact (l154_false_of_odd_inner hp hp2 hK hKc hyN hyp hField (l154_oddInner_of_tits hQ)).elim

end Certs

@[expose] def l154ExcSuz : TauCeti.CFSGIndex → Prop :=
  onLie fun | .suzuki _ => True | _ => False

theorem l154_suzukiModel_of_catalogIs {S : Type} [Group S] (h : catalogIs S l154ExcSuz) :
    ∃ f, CFSG.Blueprint.SuzukiModel S 2 f := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | suzuki m =>
      obtain ⟨hp, a, ha, K, i1, i2, hf, hK, ⟨e'⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
      exact ⟨2 * m + 1, hp, a, ha, K, i1, i2, hf, hK, ⟨e.trans e'⟩⟩
    | _ => exact hi.elim

section SuzCore


theorem l154_false_of_suzuki_centralizer {S : Type} [Group S] [Finite S] {f : ℕ}
    (hS : CFSG.Blueprint.SuzukiModel S 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {s : S}
    (hsp : s ^ p = 1) (hs1 : s ≠ 1) {T : Subgroup S} (hT : ⁅T, T⁆ = T) (hT1 : T ≠ ⊥)
    (hTs : ∀ t ∈ T, t * s = s * t) : False := by
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hT1
  haveI : Group.IsPerfect ↥T := Subgroup.isPerfect_iff.2 hT
  have hev : 2 ∣ Nat.card ↥T := by
    by_contra h2
    have hodd : Odd (Nat.card ↥T) := Nat.odd_iff.2 (by omega)
    haveI := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    exact Group.IsPerfect.not_isSolvable ↥T inferInstance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hev
  obtain ⟨-, a, ha, K, _, _, hfa, hKcard, ⟨e⟩⟩ := hS
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hKcard
  have ht2 : orderOf (t : S) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have hyo : orderOf (e (t : S)) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht2
  obtain ⟨S₂, hS₂⟩ :=
    ComponentClassification.UnbalancedGS.SuzukiOddCore.suzuki_involution_centralizer_sylow hK (e (t : S)) hyo
  have hsS : e s ∈ (S₂ : Subgroup (CFSG.Blueprint.suzukiGroup a K)) := by
    rw [hS₂]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, (hTs t t.2).symm])
  have hsord : orderOf (e s) = p :=
    orderOf_eq_prime (by rw [← map_pow, hsp, map_one])
      (fun h1 => hs1 (e.injective (h1.trans (map_one e).symm)))
  have hpS : IsPGroup 2 (S₂ : Subgroup (CFSG.Blueprint.suzukiGroup a K)) := S₂.isPGroup'
  obtain ⟨k, hk⟩ := hpS ⟨e s, hsS⟩
  have hdvd : p ∣ 2 ^ k := by
    have h1 : orderOf (⟨e s, hsS⟩ : (S₂ : Subgroup (CFSG.Blueprint.suzukiGroup a K))) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_mk, hsord] at h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

end SuzCore

section SuzMark


theorem l154_canonInnSuz (lab : CFSG.Assembly.LargeEvenLabel) :
    CFSG.LocalAnalysis.GLTheoremA.MI.CAll lab (CFSG.StandardType.LargeEvenSimpleGuard
      fun R _ I _ => lab.tag = .twB2 → I = CFSG.Assembly.LargeEvenInnSet R) := by
  intro Q hQ
  obtain ⟨t, r, n⟩ := lab
  cases t
  case twB2 =>
    dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hq⟩ := hQ
    exact ⟨K, hF, hfin, hK, hq, fun _ _ _ => rfl⟩
  all_goals exact CFSG.StandardType.Canonical.largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq, fun _ _ h => absurd h (by simp)⟩) hQ

theorem l154_inner_of_innDiagOn_suz {p : ℕ} (hp : p.Prime) {Γ : Type} [Group Γ] [Finite Γ]
    {X K : Subgroup Γ} {x : Γ} (hK : GLAPComponent p X K) (hcat : catalogIs (PSimple p K) l154ExcSuz)
    (hxN : x ∈ Subgroup.normalizer (K : Set Γ)) (hInn : InnDiagOn p (Subgroup.zpowers x) K) :
    MI.indAut p K x hxN ∈ OuterAutomorphisms.inner (PSimple p K) := by
  obtain ⟨f, hSz⟩ := l154_suzukiModel_of_catalogIs hcat
  have hperf : commutator (PQuot p K) = ⊤ := (isQuasisimple_pQuot_of_glaPComponent hp hK).1
  have hm : CFSG.Blueprint.LieModel (PQuot p K ⧸ Subgroup.center (PQuot p K)) .twistedB2 0 2 f :=
    CFSG.Blueprint.LieModel.twistedB2_iff.2 ⟨rfl, hSz⟩
  have h1 := CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hperf hm
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p K)
      fun _ _ _ I _ θ => ∃ φ ∈ I, CFSG.Assembly.LargeEvenInduces θ (indRel p K x) φ :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono
      (fun _ _ _ _ _ _ hh => hh x (Subgroup.mem_zpowers x)) hInn.2
  have h2 := MI.marking_transport (indRel p K x) hdiag h1
  have h3 := FP.canon_marking_and_labelAll_simple'
    (P' := fun lab R _ I _ => lab.tag = .twB2 → I = CFSG.Assembly.LargeEvenInnSet R)
    (fun lab _ => l154_canonInnSuz lab) h2
  obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, ⟨⟨hmodel, φ, hφ, hind⟩, hI⟩⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists h3
  have htag : lab.tag = .twB2 := by
    have h := hmodel.1
    obtain ⟨t, r, n⟩ := lab
    cases t <;> first | rfl | (simp [CFSG.StandardType.markTag] at h; done) |
      (simp only [CFSG.StandardType.markTag] at h; split_ifs at h <;> exact absurd h (by decide))
  have hI' := hI htag
  rw [hI'] at hφ
  obtain ⟨g, hg⟩ := hφ
  have e1 : φ = MulAut.congr θ (MI.indAut p K x hxN) := (MI.induces_indRel_iff hxN θ).1 hind
  have e2 : MulAut.congr θ.symm (MulAut.conj g) = MulAut.conj (θ.symm g) :=
    OuterAutomorphisms.congr_conj θ.symm g
  have e3 : MulAut.congr θ.symm (MulAut.congr θ (MI.indAut p K x hxN)) = MI.indAut p K x hxN := by
    ext y
    simp [MulAut.congr_apply]
  refine ⟨θ.symm g, ?_⟩
  rw [← e2, hg, e1, e3]

theorem l154_indAut_eq_inv {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    MI.indAut p L g hg = (chevAut p L ⟨g, hg⟩)⁻¹ := by
  rw [MI.indAut, ← map_inv]
  rfl

theorem l154_false_of_suzuki {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Γ : Type} [Group Γ] [Finite Γ]
    {X K J : Subgroup Γ} {x : Γ} (hK : GLAPComponent p X K) (hcat : catalogIs (PSimple p K) l154ExcSuz)
    (hxp : x ^ p = 1) (hxN : x ∈ Subgroup.normalizer (K : Set Γ)) (hcm : ¬ CentMod p K x)
    (hInn : InnDiagOn p (Subgroup.zpowers x) K)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J) : False := by
  obtain ⟨f, hSz⟩ := l154_suzukiModel_of_catalogIs hcat
  obtain ⟨s, hs⟩ := l154_inner_of_innDiagOn_suz hp hK hcat hxN hInn
  have hα1 : MI.indAut p K x hxN ≠ 1 := by
    intro h
    have h1 : chevAut p K ⟨x, hxN⟩ = 1 := by
      have : (chevAut p K ⟨x, hxN⟩)⁻¹ = 1 := by rw [← l154_indAut_eq_inv hxN]; exact h
      exact inv_eq_one.1 this
    exact hcm ((chevAut_eq_one_iff hp hK hxN).1 h1)
  have hαp : MI.indAut p K x hxN ^ p = 1 := l154_indAut_pow_eq_one hxN hxp
  obtain ⟨hsimple, hnab⟩ := chev_pSimple_simple_nonabelian hp hK
  have hcen : Subgroup.center (PSimple p K) = ⊥ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.center_eq_bot_of_isSimpleGroup_of_noncomm hsimple hnab
  have hsp : s ^ p = 1 := by
    have h1 : MulAut.conj (s ^ p) = 1 := by rw [map_pow, hs]; exact hαp
    have h2 : s ^ p ∈ Subgroup.center (PSimple p K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut (PSimple p K) => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [hcen] at h2
    exact Subgroup.mem_bot.1 h2
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hα1 (by rw [← hs, map_one])
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (K : Set Γ) := Subgroup.inv_mem _ hxN
  have hJ' : GLAPComponent p (K ⊓ Subgroup.centralizer ({x⁻¹} : Set Γ)) J := by
    rw [l154_centralizer_inv_singleton]
    exact hJ
  have hT := glaPComponent_chevTransfer hp hxN'
    (l154_isPGroup_zpowers_of_pow_eq_one (by simp [inv_pow, hxp])) hJ'
  refine l154_false_of_suzuki_centralizer hSz hp hp2 hsp hs1 (glaPComponent_perfect hT)
    (glaPComponent_ne_bot' hT) (fun t ht => ?_)
  have h1 : chevAut p K ⟨x⁻¹, hxN'⟩ t = t := mem_fixSubgroup.1 (hT.1 ht)
  have h2 : MulAut.conj s t = t := by rw [hs]; exact h1
  rw [MulAut.conj_apply] at h2
  exact (mul_inv_eq_iff_eq_mul.1 h2).symm

theorem l154NIDOn_suz : L154NIDOn l154ExcSuz := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hQ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  exact (l154_false_of_suzuki hp hp2 hK hQ hxp hxN hcm hInn hJ).elim

theorem l154TD4On_suz : L154TD4On l154ExcSuz := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hQ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  exact (l154_false_of_suzuki hp hp2 hK hQ hxp hxN hcm hInn hJ).elim

end SuzMark

@[expose] def l154ExcTwo : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E6 q => q.card = 2 | .E7 q => q.card = 2 | .E8 q => q.card = 2 | .F4 q => q.card = 2
    | .twistedE6 q => q.card = 2 | .trialityD4 q => q.card = 2
    | _ => False

theorem l154_primePower_card_two (q : TauCeti.PrimePower) (h : q.card = 2) : q.p = 2 ∧ q.exponent = 1 := by
  have h0 : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans h
  have h1 : q.p ∣ 2 := by
    rw [← h0]
    exact dvd_pow_self _ (Nat.pos_iff_ne_zero.1 q.exponent_pos)
  have hp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
  refine ⟨hp, ?_⟩
  rw [hp] at h0
  exact Nat.pow_right_injective le_rfl (h0.trans (pow_one 2).symm)

section Two


theorem l154_false_of_fieldOn_exponent_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Γ : Type} [Group Γ]
    [Finite Γ] {K : Subgroup Γ} {y : Γ} (hF : FieldOn p y K)
    (h : ∀ lab : CFSG.Assembly.LargeEvenLabel, CFSG.Assembly.LargeEvenInLambda2 lab →
      CFSG.StandardType.markChar lab = 2 → CFSG.StandardType.MarkedModel lab (PSimple p K) →
        lab.n = 1) : False := by
  obtain ⟨lab, hlab, -, hM, hpn, -⟩ := FR.fieldOn_subfield hp hp2 hF
  have h1 : 1 ≤ lab.n := hlab.1
  have hn : p ≤ lab.n := Nat.le_of_dvd h1 hpn
  have hp3 : 2 ≤ p := hp.two_le
  have hc : CFSG.StandardType.markChar lab = 2 :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markChar_eq_two_of_two_le hlab (by omega)
  have := h lab hlab hc hM
  omega

theorem l154_labels_two {S : Type} [Group S] (h : catalogIs S l154ExcTwo) :
    ∀ lab : CFSG.Assembly.LargeEvenLabel, CFSG.Assembly.LargeEvenInLambda2 lab →
      CFSG.StandardType.markChar lab = 2 → CFSG.StandardType.MarkedModel lab S → lab.n = 1 := by
  intro lab hlab hc hM
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | E6 q =>
      obtain ⟨hp2, he1⟩ := l154_primePower_card_two q hi
      have hX : CFSG.Blueprint.LieModel S .E6 0 2 1 := by
        have := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E6 q hv e
        rwa [hp2, he1] at this
      exact (CFSG.StandardType.NbrInnerMore.eq_of_markedModel_E6 le_rfl hX hlab hc hM).2
    | E7 q =>
      obtain ⟨hp2, he1⟩ := l154_primePower_card_two q hi
      have hX : CFSG.Blueprint.LieModel S .E7 0 2 1 := by
        have := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E7 q hv e
        rwa [hp2, he1] at this
      obtain ⟨hT, -, hD⟩ := CFSG.SeitzReduction.E8Pilot.lieModel_E7_two_unique hX
        (CFSG.StandardType.NbrInnerMore.lieModel_of_markedModel_two hc hM)
      obtain ⟨t, r, n⟩ := lab
      cases t <;> first | exact hD | (exfalso; revert hT; simp [CFSG.StandardType.markTag]; done) |
        (exfalso; revert hT; simp only [CFSG.StandardType.markTag]; split_ifs <;> decide)
    | E8 q =>
      obtain ⟨hp2, he1⟩ := l154_primePower_card_two q hi
      have hX : CFSG.Blueprint.LieModel S .E8 0 2 1 := by
        have := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_E8 q hv e
        rwa [hp2, he1] at this
      exact (CFSG.StandardType.NbrInnerMore.eq_of_markedModel_E8 le_rfl hX hlab hc hM).2
    | F4 q =>
      obtain ⟨hp2, he1⟩ := l154_primePower_card_two q hi
      have hX : CFSG.Blueprint.LieModel S .F4 0 2 1 := by
        have := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_F4 q hv e
        rwa [hp2, he1] at this
      exact (CFSG.StandardType.NbrInnerMore.eq_of_markedModel_F4 le_rfl hX hlab hc hM).2
    | twistedE6 q =>
      obtain ⟨hp2, he1⟩ := l154_primePower_card_two q hi
      have hX : CFSG.Blueprint.LieModel S .twistedE6 0 2 1 := by
        have := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_twistedE6 q hv e
        rwa [hp2, he1] at this
      exact (CFSG.StandardType.NbrInnerMore.eq_of_markedModel_twE6 le_rfl hX hlab hc hM).2
    | trialityD4 q =>
      obtain ⟨hp2, he1⟩ := l154_primePower_card_two q hi
      have hX : CFSG.Blueprint.LieModel S .trialityD4 0 2 1 := by
        have := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_trialityD4 q hv e
        rwa [hp2, he1] at this
      exact (CFSG.StandardType.NbrInnerMore.eq_of_markedModel_triD4 le_rfl hX hlab hc hM).2
    | _ => exact hi.elim

theorem l154NIDOn_two : L154NIDOn l154ExcTwo := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hQ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  exact (l154_false_of_fieldOn_exponent_one hp hp2 hField (l154_labels_two hQ)).elim

theorem l154TD4On_two : L154TD4On l154ExcTwo := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hQ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  exact (l154_false_of_fieldOn_exponent_one hp hp2 hField (l154_labels_two hQ)).elim

end Two

@[expose] def l154ExcRest : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E6 q => q.p = 2 ∧ q.card ≠ 2 | .E7 q => q.p = 2 ∧ q.card ≠ 2 | .E8 q => q.p = 2 ∧ q.card ≠ 2
    | .F4 q => q.p = 2 ∧ q.card ≠ 2 | .twistedE6 q => q.p = 2 ∧ q.card ≠ 2
    | .trialityD4 q => q.p = 2 ∧ q.card ≠ 2 | .G2 q => q.p = 2 | .reeF4 _ => True
    | _ => False

theorem l154_exc_cover (i : TauCeti.CFSGIndex) (h : l154Exc i) :
    l154ExcTits i ∨ l154ExcSuz i ∨ l154ExcTwo i ∨ l154ExcRest i := by
  cases i with
  | cyclic p hp => exact h.elim
  | alternating n hn => exact h.elim
  | sporadic s => exact h.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | E6 q =>
      by_cases hq : q.card = 2
      · exact Or.inr (Or.inr (Or.inl hq))
      · exact Or.inr (Or.inr (Or.inr ⟨h, hq⟩))
    | E7 q =>
      by_cases hq : q.card = 2
      · exact Or.inr (Or.inr (Or.inl hq))
      · exact Or.inr (Or.inr (Or.inr ⟨h, hq⟩))
    | E8 q =>
      by_cases hq : q.card = 2
      · exact Or.inr (Or.inr (Or.inl hq))
      · exact Or.inr (Or.inr (Or.inr ⟨h, hq⟩))
    | F4 q =>
      by_cases hq : q.card = 2
      · exact Or.inr (Or.inr (Or.inl hq))
      · exact Or.inr (Or.inr (Or.inr ⟨h, hq⟩))
    | twistedE6 q =>
      by_cases hq : q.card = 2
      · exact Or.inr (Or.inr (Or.inl hq))
      · exact Or.inr (Or.inr (Or.inr ⟨h, hq⟩))
    | trialityD4 q =>
      by_cases hq : q.card = 2
      · exact Or.inr (Or.inr (Or.inl hq))
      · exact Or.inr (Or.inr (Or.inr ⟨h, hq⟩))
    | G2 q => exact Or.inr (Or.inr (Or.inr h))
    | reeF4 m => exact Or.inr (Or.inr (Or.inr trivial))
    | suzuki m => exact Or.inr (Or.inl trivial)
    | tits => exact Or.inl trivial
    | A r q => exact h.elim
    | twistedA r q => exact h.elim
    | B r q => exact h.elim
    | C r q => exact h.elim
    | D r q => exact h.elim
    | twistedD r q => exact h.elim
    | reeG2 m => exact h.elim

section Assembly


theorem l154NIDOn_exc_of_rest (hR : L154NIDOn l154ExcRest) : L154NIDOn l154Exc :=
  l154NIDOn_mono l154_exc_cover
    (l154NIDOn_or l154NIDOn_tits (l154NIDOn_or l154NIDOn_suz (l154NIDOn_or l154NIDOn_two hR)))

theorem l154TD4On_exc_of_rest (hR : L154TD4On l154ExcRest) : L154TD4On l154Exc :=
  l154TD4On_mono l154_exc_cover
    (l154TD4On_or l154TD4On_tits (l154TD4On_or l154TD4On_suz (l154TD4On_or l154TD4On_two hR)))

theorem l154NonInnDiag_of_rest_exc (hUni : L154NIDOn l154Uni) (hSymp : L154NIDOn l154Symp)
    (hOrth : L154NIDOn l154Orth) (hTwOrth : L154NIDOn l154TwOrth) (hExc : L154NIDOn l154ExcRest) :
    L154NonInnDiag :=
  l154NonInnDiag_of_rest hUni hSymp hOrth hTwOrth (l154NIDOn_exc_of_rest hExc)

theorem l154NotTD4_of_rest_exc (hUni : L154TD4On l154Uni) (hSymp : L154TD4On l154Symp)
    (hOrth : L154TD4On l154Orth) (hTwOrth : L154TD4On l154TwOrth) (hExc : L154TD4On l154ExcRest) :
    L154NotTD4 :=
  l154NotTD4_of_rest hUni hSymp hOrth hTwOrth (l154TD4On_exc_of_rest hExc)

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.K155X
