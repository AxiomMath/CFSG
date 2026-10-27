module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Link
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Build
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Out
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Spec
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Sylow
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuterParts
import CFSG.LocalAnalysis.SectionRank.TrialityEvenCover
import CFSG.Adapters.TauCetiExceptional.EvenB1

public section

open CFSG.Quasithin CFSG.Open CFSG.SectionRank CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4

namespace CFSG.AGLEmbedding.ChevOuterD48

theorem map_conj_eq_of_normal_d48 {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (g : G) :
    N.map (MulAut.conj g).toMonoidHom = N := by
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance n hn g
  · intro n hn
    refine ⟨g⁻¹ * n * g, ?_, ?_⟩
    · simpa using Subgroup.Normal.conj_mem inferInstance n hn g⁻¹
    · simp [MulAut.conj_apply, mul_assoc]

theorem exists_pow_eight_ne {k : Type} [Field k] [Finite k] (hk : Nat.card k = 8 ^ 3) :
    ∃ c : k, c ^ 8 ≠ c := by
  by_contra h
  push Not at h
  have : Fintype k := Fintype.ofFinite k
  have hcard : Fintype.card k = 8 ^ 3 := by rw [← Nat.card_eq_fintype_card]; exact hk
  open Polynomial in
  let p : k[X] := X ^ 8 - X
  have hp : p = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p (f := id)
      Function.injective_id (fun a => by simp [p, h a]) ?_
    rw [hcard]
    simp only [p]
    have : (Polynomial.X ^ 8 - Polynomial.X : Polynomial k).natDegree ≤ 8 := by
      compute_degree
    omega
  have h8 : p.coeff 8 = 1 := by
    simp [p, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  rw [hp] at h8
  simp at h8

theorem eq_one_of_conj_eq_one {C : Type*} [Group C] (hZ : Subgroup.center C = ⊥) {g : C}
    (h : (MulAut.conj g : MulAut C) = 1) : g = 1 := by
  have hc : g ∈ Subgroup.center C := Subgroup.mem_center_iff.2 fun y => by
    have := congrArg (fun φ : MulAut C => φ y) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rw [hZ] at hc
  exact hc

set_option linter.unusedSectionVars false

section Main


theorem exists_model_C {L : Type} [Group L] (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (hq : q.p = 2) (hq3 : q.exponent = 3) (hdq : d.1 = .trialityD4 q)
    (e : L ≃* CatGroup d) :
    CFSG.Blueprint.ChevalleyExceptionalModel L .trialityD4 2 3 ∧
      ∃ (kf : Type) (_ : Field kf) (_ : Finite kf) (σ : kf ≃+* kf), Nat.card kf = (2 ^ 3) ^ 3 ∧
        (∀ c, σ c = c ^ (2 ^ 3)) ∧
        Nonempty (L ≃* graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.trialityD4 q := hdq
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel
      (CatGroup ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩) .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide)
        (MulEquiv.refl _)⟩
  rw [hq, hq3] at hm
  have hmod := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e hm
  refine ⟨hmod, ?_⟩
  exact exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two (by norm_num) hmod.2

theorem chevOuterGenAt_d48 (d : TauCeti.ValidLieTypeIndex)
    (hd : IsChevTwoOuter3D48Index d) : ChevTwoOuterGenAt d := by
  intro X _ _ K hKn hq ⟨e⟩ hC hodd R hR
  obtain ⟨q, hqp, hq3, hdq⟩ := hd
  have : K.Normal := hKn
  have : Group.IsPerfect K := ⟨hq.1⟩
  obtain ⟨hmod, kf, _, _, σ, hkf, hσ, ⟨eC⟩⟩ := exists_model_C d q hqp hq3 hdq e
  have hZ3 : IsPGroup 3 (Subgroup.center K) := by
    let f : Subgroup.center K →* Subgroup.centralizer (K : Set X) :=
      (K.subtype.comp (Subgroup.center K).subtype).codRestrict
        (Subgroup.centralizer (K : Set X)) (fun z => by
          rw [Subgroup.mem_centralizer_iff]
          intro k hk
          have := Subgroup.mem_center_iff.1 z.2 ⟨k, hk⟩
          exact congrArg Subtype.val this)
    have hinj : Function.Injective f := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
    exact hC.of_injective f hinj
  have hZodd : Odd (Nat.card (QuotientGroup.mk' (Subgroup.center K)).ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZ3
    rw [hn]
    exact Odd.pow (by decide)
  have hZK : Subgroup.center K = ⊥ := by
    have := triality_even_perfect_odd_cover_trivial hmod (QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hZodd
    rwa [QuotientGroup.ker_mk'] at this
  have hCX : Subgroup.centralizer (K : Set X) = ⊥ := by
    by_contra hne
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hC
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hne
      rw [← Subgroup.card_eq_one]
      simpa using hn
    have h3 : 3 ∣ Nat.card (Subgroup.centralizer (K : Set X)) := by
      rw [hn]
      exact dvd_pow_self 3 hn0
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hxo : orderOf (x : X) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    have := hodd x x.2 hxo
    rw [hZK, Subgroup.map_bot, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hxo
    omega
  let eKL : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot).symm
  let eK : K ≃* graphFixedRootGroup TwistTag.D4 kf σ.toRingHom := eKL.trans eC
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have : IsSimpleGroup K := MulEquiv.isSimpleGroup eKL
  have hk8 : Nat.card kf = 8 ^ 3 := by simpa using hkf
  have hσ8 : ∀ c, σ c = c ^ 8 := fun c => by simpa using hσ c
  have hK9 : Nat.card kf = 2 ^ (3 * 3) := by rw [hkf, ← pow_mul]
  have : CharP kf 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hK9
  have : Fintype kf := Fintype.ofFinite kf
  let e' : kf ≃+* GF512 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk8, GF512.card_eq]
    norm_num)
  have hC0 : graphFixedRootGroup TwistTag.D4 kf σ.toRingHom =
      (twistedGroup σ.toRingHom).map (adjointGroup d4 kf).subtype := graph_eq_map σ hk8 hσ8
  let ψC := psiC σ e' hC0
  have hrange : ψC.range = letterGroup := range_psiC σ hk8 hσ8 e' hC0
  let ψK : K →* GL (Fin 8) GF512 := ψC.comp eK.toMonoidHom
  have hlet : ∀ k, k < 24 → ∃ c, ψC c = letterGL k := by
    intro k hk
    have : letterGL k ∈ ψC.range := by rw [hrange]; exact letterGL_mem hk
    exact this
  have hmemK : ∀ k, k < 24 → letterGL k ∈ ψK.range := by
    intro k hk
    obtain ⟨c, hc⟩ := hlet k hk
    refine ⟨eK.symm c, ?_⟩
    show ψC (eK (eK.symm c)) = letterGL k
    rw [MulEquiv.apply_symm_apply]
    exact hc
  have hψKinj : Function.Injective ψK := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψK.ker with h | h
    · exact h
    · exfalso
      obtain ⟨c, hc⟩ := hlet 0 (by norm_num)
      have h1 : ψK (eK.symm c) = 1 := by
        rw [← MonoidHom.mem_ker, h]; trivial
      have h2 : ψK (eK.symm c) = letterGL 0 := by
        show ψC (eK (eK.symm c)) = letterGL 0
        rw [MulEquiv.apply_symm_apply]
        exact hc
      rw [h1] at h2
      have h3 : (1 : GL (Fin 8) GF512) = letterGL 0 := h2
      exact letterMat_zero_ne_one (congrArg (fun g : GL (Fin 8) GF512 =>
        (g : Matrix (Fin 8) (Fin 8) GF512)) h3).symm
  have hψCinj : Function.Injective ψC := by
    intro a b hab
    apply eK.symm.injective
    apply hψKinj
    show ψC (eK (eK.symm a)) = ψC (eK (eK.symm b))
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hab
  have hcardK : Nat.card K = ordTrialityD4 (2 ^ q.exponent) := by
    rw [Nat.card_congr (eKL.trans e).toEquiv]
    exact card_catGroup_trialityD4_even hqp hdq
  have hv3 : (Nat.card K).factorization 3 = 6 := by
    rw [hcardK, hq3]
    have h : ordTrialityD4 (2 ^ 3) = 3 ^ 6 * 26125046257273041584128 := by
      norm_num [ordTrialityD4]
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have rankK : ∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2 :=
    rank_le_nine_of_letters ψK hψKinj hmemK hv3
  let ρ : X →* MulAut (graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) :=
    (MulAut.congr eK).toMonoidHom.comp (MulAut.conjNormal : X →* MulAut K)
  have hρK : ∀ k : K, ρ (k : X) = MulAut.conj (eK k) := by
    intro k
    show MulAut.congr eK (MulAut.conjNormal (k : X)) = _
    rw [MulAut.conjNormal_val]
    refine MulEquiv.ext fun t => ?_
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (MulAut.conjNormal x : MulAut K) = 1 := by
      exact (MulAut.congr eK).injective (by rw [map_one]; exact hx)
    have hxc : x ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := congrArg (fun α : MulAut K => ((α ⟨k, hk⟩ : K) : X)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [hCX] at hxc
    exact hxc
  have hKne : K ≠ ⊤ := by
    intro hKtop
    have hrank : Open.pRank 3 (R : Subgroup X) ≤ 2 := by
      apply CFSG.SectionRank.pRank_le (by norm_num)
      intro E hER hE
      have hEK : E ≤ K := by rw [hKtop]; exact le_top
      have hE' : IsElemAbelian 3 (E.subgroupOf K) :=
        isElemAbelian_of_equiv_le_d48 hE le_rfl (Subgroup.subgroupOfEquivOfLe hEK)
      have hb := rankK (E.subgroupOf K) hE'
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv] at hb
    omega
  have hne : ∃ x : X, ∀ g : graphFixedRootGroup TwistTag.D4 kf σ.toRingHom,
      ρ x ≠ MulAut.conj g := by
    obtain ⟨x, hx⟩ : ∃ x : X, x ∉ K := by
      by_contra h
      push Not at h
      exact hKne (eq_top_iff.2 fun x _ => h x)
    refine ⟨x, fun g hg => hx ?_⟩
    have : ρ x = ρ ((eK.symm g : K) : X) := by rw [hρK, MulEquiv.apply_symm_apply, hg]
    rw [hρinj this]
    exact (eK.symm g).2
  have hinner : ∀ g : graphFixedRootGroup TwistTag.D4 kf σ.toRingHom,
      ∃ κ : X, ρ κ = MulAut.conj g := fun g =>
    ⟨((eK.symm g : K) : X), by rw [hρK, MulEquiv.apply_symm_apply]⟩
  obtain ⟨-, hunique, ⟨Θ, hΘ, -, -, -⟩, hcyc, hcard9, -, hZC, -⟩ :=
    even_triality_exact_automorphism_normal_form (f := 3) (by norm_num) kf hkf σ hσ
  let fa : RingAut kf →* MulAut (graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) :=
    fieldActorHom (t := TwistTag.D4) σ
  have hΘ' : ∀ (g : graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) (δ : kf ≃+* kf),
      Θ (MulAut.conj g * fa δ) = δ := fun g δ => hΘ _ g δ rfl
  have hex : ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 kf σ.toRingHom),
      ∃ (g : graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) (δ : kf ≃+* kf),
        α = MulAut.conj g * fa δ := fun α => by
    obtain ⟨⟨g, δ⟩, h, -⟩ := hunique α
    exact ⟨g, δ, h⟩
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    show σ (σ (σ c)) = c
    exact sigma_three_of_card (q := 8) hk8 (σ := σ.toRingHom)
      (fun c => by simpa using hσ8 c) c
  have hσ1 : σ ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := exists_pow_eight_ne hk8
    apply hc
    rw [← hσ8 c, h]
    rfl
  have hcard9' : Nat.card (kf ≃+* kf) = 9 := by rw [hcard9]
  have : Finite (kf ≃+* kf) := Nat.finite_of_card_ne_zero (by rw [hcard9']; norm_num)
  obtain ⟨x0, hx0⟩ : ∃ x : X, ρ x = fa σ :=
    exists_phi_mem hcard9' ρ fa Θ hΘ' hex hinner hne hσ3 hσ1
  have hφ3 : fa σ ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  have hid : ∀ (g : graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) (j : ℕ), j < 3 →
      MulAut.conj g * fa σ ^ j = 1 → j = 0 ∧ g = 1 := by
    intro g j hj h
    have h1 : Θ (MulAut.conj g * fa (σ ^ j)) = σ ^ j := hΘ' g _
    rw [map_pow, h, map_one] at h1
    have hj0 : j = 0 := by
      interval_cases j
      · rfl
      · exact absurd (by simpa using h1.symm) hσ1
      · exfalso
        apply hσ1
        have h2 : σ ^ 2 = 1 := h1.symm
        calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
          _ = 1 := by rw [hσ3, h2]; simp
    subst hj0
    refine ⟨rfl, ?_⟩
    rw [pow_zero, mul_one] at h
    exact eq_one_of_conj_eq_one hZC h
  have hφψ : ∀ g : graphFixedRootGroup TwistTag.D4 kf σ.toRingHom,
      (ψC (fa σ g) : Matrix (Fin 8) (Fin 8) GF512) =
        (ψC g : Matrix (Fin 8) (Fin 8) GF512).map frobF := by
    intro g
    have h1 := psiC_fieldActor σ hk8 hσ8 e' hC0 σ g
    show (ψC (fieldActor (t := TwistTag.D4) σ σ g) : Matrix (Fin 8) (Fin 8) GF512) = _
    rw [h1, coe_map_gl]
    congr 1
    funext x
    show e' (σ (e'.symm x)) = frobF x
    rw [frobF_apply, hσ8, map_pow, RingEquiv.apply_symm_apply]
  choose! gk hgk using hlet
  let lt : ℕ → X := fun k => ((eK.symm (gk k) : K) : X)
  have hlt : ∀ k, k < 24 → ∃ g : graphFixedRootGroup TwistTag.D4 kf σ.toRingHom,
      (ψC g : Matrix (Fin 8) (Fin 8) GF512) = letterMat k ∧ ρ (lt k) = MulAut.conj g :=
    fun k hk => ⟨gk k, by rw [hgk k hk]; rfl, by
      show ρ ((eK.symm (gk k) : K) : X) = _
      rw [hρK, MulEquiv.apply_symm_apply]⟩
  let R0 : Realization X := buildReal ρ ψC (fa σ) hφ3 hφψ hρinj hψCinj hid lt hlt x0 hx0
  have hE : IsPGroup 3 R0.Egrp := by
    obtain ⟨-, -, hEcard⟩ := R0.egrp_facts Certificates.certificate9641
    exact IsPGroup.of_card hEcard
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  have hletter : ∀ k, k < 24 → lt k ∈ GLBWeakCore 3 (Q : Subgroup X) := fun k hk =>
    R0.letter_mem_weakCore_of_cert hQ k hk
  have hKQ : K ≤ GLBWeakCore 3 (Q : Subgroup X) := by
    intro κ hκ
    let ι : graphFixedRootGroup TwistTag.D4 kf σ.toRingHom →* X :=
      K.subtype.comp eK.symm.toMonoidHom
    let H : Subgroup (graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) :=
      Subgroup.closure {c | ∃ k, k < 24 ∧ gk k = c}
    have hmapH : H.map ψC = letterGroup := by
      rw [MonoidHom.map_closure, letterGroup]
      congr 1
      ext A
      constructor
      · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
        exact ⟨k, hk, (hgk k hk).symm⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨gk k, ⟨k, hk, rfl⟩, hgk k hk⟩
    have hHtop : ∀ c, c ∈ H := by
      intro c
      have hc : ψC c ∈ letterGroup := by rw [← hrange]; exact ⟨c, rfl⟩
      rw [← hmapH] at hc
      obtain ⟨c', hc', hcc⟩ := hc
      exact (hψCinj hcc) ▸ hc'
    have hcl : H.map ι ≤ GLBWeakCore 3 (Q : Subgroup X) := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact hletter k hk
    exact hcl ⟨eK ⟨κ, hκ⟩, hHtop _, by
      show ((eK.symm (eK ⟨κ, hκ⟩) : K) : X) = κ
      rw [MulEquiv.symm_apply_apply]⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q R
  have hPQ : (R : Subgroup X) = (Q : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    have h : ((g • Q : Sylow 3 X) : Subgroup X) = (R : Subgroup X) :=
      congrArg (fun S : Sylow 3 X => (S : Subgroup X)) hg
    rw [← h, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have h2 := map_glbWeakCore_le Nat.prime_three (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective (Q : Subgroup X)
  rw [← hPQ] at h2
  have h3 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hKQ
  rw [map_conj_eq_of_normal_d48 K g] at h3
  exact h3.trans h2

theorem kFactChevTwoOuterGen3D48 : KFactChevTwoOuterGen3D48 :=
  fun d hd => chevOuterGenAt_d48 d hd

end Main

end CFSG.AGLEmbedding.ChevOuterD48
