module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1310s
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnerLine
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwA2Conj
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoIn
public import CFSG.HardMathSupport.Lang.E6Descent.CenterE6

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310t

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LieType.Chevalley CFSG.LieType.Seitz
open CFSG.HardMathSupport.Dickson.I271 (actPre autImage actHom mem_actPre actHom_mk coe_normalizerMonoidHom
  actPre_le_left centreOf isElemAbelian_actPre eq_top_of_sup_center_eq_top pRank_actPre)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns (gammaPrimeIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (IsTwoPow)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

set_option linter.unusedSectionVars false

section Tools

theorem center_ne_bot_of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : Subgroup.center P ≠ ⊥) : Subgroup.center Q ≠ ⊥ := by
  intro hQ
  apply h
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    have h1 := hz (e.symm y)
    calc y * e z = e (e.symm y * z) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = e (z * e.symm y) := by rw [h1]
      _ = e z * y := by rw [map_mul, MulEquiv.apply_symm_apply]
  rw [hQ, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact e.injective (hz'.trans (map_one e).symm)

theorem closure_fixed_eq_top_of_seitzHyperGamma {S C : Type*} [Group S] [Group C] (e : S ≃* C) {p : ℕ}
    {E : Subgroup (MulAut C)} (h : seitzHyperGamma p E = ⊤) :
    Subgroup.closure {s : S | ∃ P ∈ {P : Subgroup (MulAut S) | ∃ F : Subgroup (MulAut C), F ≤ E ∧
      F.relIndex E = p ∧ P = F.map (MulAut.congr e).symm.toMonoidHom}, ∀ φ ∈ P, φ s = s} = ⊤ := by
  set T : Set S := {s : S | ∃ P ∈ {P : Subgroup (MulAut S) | ∃ F : Subgroup (MulAut C), F ≤ E ∧
      F.relIndex E = p ∧ P = F.map (MulAut.congr e).symm.toMonoidHom}, ∀ φ ∈ P, φ s = s} with hT
  have hle : seitzHyperGamma p E ≤ (Subgroup.closure T).map e.toMonoidHom := by
    refine iSup₂_le fun F hF => ?_
    intro c hc
    refine ⟨e.symm c, Subgroup.subset_closure ⟨_, ⟨F, hF.1, hF.2, rfl⟩, ?_⟩, by simp⟩
    rintro _ ⟨ψ, hψ, rfl⟩
    have hψc : ψ c = c := (mem_fixedPoints.1 hc) ψ hψ
    show ((MulAut.congr e).symm ψ) (e.symm c) = e.symm c
    have h1 : MulAut.congr e ((MulAut.congr e).symm ψ) = ψ := MulEquiv.apply_symm_apply _ _
    have h2 := congrArg (fun f : MulAut C => f c) h1
    simp only [MulAut.congr_apply, MulEquiv.trans_apply] at h2
    apply e.injective
    rw [h2, hψc, MulEquiv.apply_symm_apply]
  rw [eq_top_iff]
  intro s _
  have hs : e s ∈ seitzHyperGamma p E := by rw [h]; exact Subgroup.mem_top _
  obtain ⟨t, ht, hts⟩ := hle hs
  have hts' : t = s := e.injective hts
  rw [← hts']
  exact ht

end Tools

section Lift

variable {X : Type} [Group X] [Finite X]

theorem le_gammaPrime_of_fixed_center_three {k : ℕ} {B K : Subgroup X} (hperf : commutator ↥K = ⊤)
    (hBel : IsElemAbelian 3 B) (hZ3 : Nat.card (Subgroup.center ↥K) = 3)
    (Fam : Set (Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))))
    (hFam : ∀ P ∈ Fam, k + 1 ≤ CFSG.Open.pRank 3 (actPre B K P))
    (hgen : Subgroup.closure {s : ↥K ⧸ Subgroup.center ↥K | ∃ P ∈ Fam, ∀ e ∈ P, e s = s} = ⊤) :
    K ≤ gammaPrimeIn 3 k B K := by
  classical
  have hZc : Nat.card (centreOf K) = 3 := by
    rw [centreOf, Subgroup.card_map_of_injective K.subtype_injective, hZ3]
  have hlift : ∀ s ∈ {s : ↥K ⧸ Subgroup.center ↥K | ∃ P ∈ Fam, ∀ e ∈ P, e s = s},
      ∃ x ∈ (gammaPrimeIn 3 k B K).subgroupOf K,
        (QuotientGroup.mk x : ↥K ⧸ Subgroup.center ↥K) = s := by
    rintro s ⟨P, hP, hs⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨x, ?_, rfl⟩
    show (x : X) ∈ gammaPrimeIn 3 k B K
    have hconj : ∀ q ∈ actPre B K P, (x : X)⁻¹ * (q * x * q⁻¹) ∈ centreOf K := by
      intro q hq
      obtain ⟨hqN, -, hqP⟩ := mem_actPre.1 hq
      have hfix := hs _ hqP
      rw [actHom_mk] at hfix
      have hz : x⁻¹ * K.normalizerMonoidHom ⟨q, hqN⟩ x ∈ Subgroup.center ↥K :=
        QuotientGroup.eq.1 hfix.symm
      rw [centreOf]
      refine Subgroup.mem_map.2 ⟨_, hz, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, coe_normalizerMonoidHom]
    have hcard := CFSG.ComponentClassification.AschbacherTheorem3.FourEight.card_le_of_conj_mem hconj
    have hQel : IsElemAbelian 3 (actPre B K P) := isElemAbelian_actPre P hBel
    have hCel : IsElemAbelian 3 (Subgroup.centralizer ({(x : X)} : Set X) ⊓ actPre B K P) :=
      hQel.mono inf_le_right
    have hQc := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoAux.card_eq_pow_pRank
      Nat.prime_three hQel
    have hCc := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoAux.card_eq_pow_pRank
      Nat.prime_three hCel
    have hrk : k ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({(x : X)} : Set X) ⊓ actPre B K P) := by
      have h1 := hFam P hP
      rw [hQc, hCc, hZc] at hcard
      have h2 : 3 ^ CFSG.Open.pRank 3 (actPre B K P) ≤
          3 ^ (CFSG.Open.pRank 3 (Subgroup.centralizer ({(x : X)} : Set X) ⊓ actPre B K P) + 1) := by
        rw [pow_succ, mul_comm]
        exact hcard
      have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h2
      omega
    have hxC : (x : X) ∈ K ⊓ Subgroup.centralizer
        ((Subgroup.centralizer ({(x : X)} : Set X) ⊓ actPre B K P : Subgroup X) : Set X) := by
      refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun c hc => ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).1
    have hle : K ⊓ Subgroup.centralizer
        ((Subgroup.centralizer ({(x : X)} : Set X) ⊓ actPre B K P : Subgroup X) : Set X) ≤
          gammaPrimeIn 3 k B K :=
      le_iSup₂_of_le (f := fun (E : Subgroup X) (_ : E ≤ B ∧ k ≤ CFSG.Open.pRank 3 E) =>
        K ⊓ Subgroup.centralizer (E : Set X)) _ ⟨inf_le_right.trans actPre_le_left, hrk⟩ le_rfl
    exact hle hxC
  have hle : Subgroup.closure {s : ↥K ⧸ Subgroup.center ↥K | ∃ P ∈ Fam, ∀ e ∈ P, e s = s} ≤
      ((gammaPrimeIn 3 k B K).subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨x, hx, rfl⟩ := hlift s hs
    exact ⟨x, hx, rfl⟩
  have hsup : (gammaPrimeIn 3 k B K).subgroupOf K ⊔ Subgroup.center ↥K = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : (QuotientGroup.mk g : ↥K ⧸ Subgroup.center ↥K) ∈
        Subgroup.closure {s : ↥K ⧸ Subgroup.center ↥K | ∃ P ∈ Fam, ∀ e ∈ P, e s = s} := by
      rw [hgen]; exact Subgroup.mem_top _
    obtain ⟨γ, hγ, hγg⟩ := hle hg
    have hz : γ⁻¹ * g ∈ Subgroup.center ↥K := QuotientGroup.eq.1 hγg
    have : g = γ * (γ⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hγ hz
  have htop : (gammaPrimeIn 3 k B K).subgroupOf K = ⊤ := eq_top_of_sup_center_eq_top hperf hsup
  intro x hx
  have : (⟨x, hx⟩ : ↥K) ∈ (gammaPrimeIn 3 k B K).subgroupOf K := by rw [htop]; exact Subgroup.mem_top _
  exact this

end Lift

section Seven


@[expose] def Rank3CuResExcSeven : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = 2 ^ 2 → (∀ c, σ c = c ^ 2) →
    ∀ D : Subgroup (MulAut ↥(twistedE6RootGroup K σ)), IsElemAbelian 3 D → Nat.card D = 3 ^ 4 →
      ∃ E : Subgroup (MulAut ↥(twistedE6RootGroup K σ)), E ≤ D ∧ 9 ≤ Nat.card E ∧
        ∃ V : Subgroup ↥(twistedE6RootGroup K σ), V ≠ ⊥ ∧ IsPGroup 2 ↥V ∧ ∀ φ ∈ E, ∀ v ∈ V, φ v ∈ V

end Seven

section Cases


variable {G : Type} [Group G] [Finite G]

theorem le_M_of_twE6Eight (hGA : GriessMultipliersAllModels)
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDefs.TwE6DiagNonParCubes)
    {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139b : Prop139b p M D) {U : Subgroup G}
    (hU : IsU1312 p B M D L0 d U) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) {Kc : Subgroup G}
    (hKc : GLAPComponent 3 (Cg u) Kc) (hN : B ≤ Subgroup.normalizer (Kc : Set G))
    (hcen : CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
      Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ 1)
    (hZ : Subgroup.center (barOf 3 Kc) ≠ ⊥) (i : TauCeti.ValidLieTypeIndex)
    (e : barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc) ≃* (TauCeti.CFSGIndex.lie i).Group)
    {q : TauCeti.PrimePower} (hq : IsTwoPow q 3) (hiq : i.1 = .twistedE6 q)
    (hno : Claims1310r.NoPlaneTwoSub (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)))
    (hni : ¬ InputsSeitz3.autIm (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≤
      (MulAut.conj : ↥(barX 3 (Cg u) Kc) →* MulAut ↥(barX 3 (Cg u) Kc)).range)
    (hhigh : Claims1310s.IsHighTwE6 (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc))
      (q.p ^ q.exponent)) :
    Kc ≤ M := by
  classical
  obtain ⟨hcard, hB4⟩ := Claims1310r.card_autImage_eq h h139b hU hu hu1 hKc hN hcen
  obtain ⟨hp3, -⟩ := h139b
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hBel : IsElemAbelian 3 B := h.bOne.1.1
  have huB : u ∈ B := hU.1.1 hu
  have hnorm : ∀ E' : Subgroup G, E' ≤ B → 2 ≤ CFSG.Open.pRank 3 E' →
      Subgroup.normalizer (E' : Set G) ≤ M :=
    fun E' hE' hr => (normalizer_le_glbCore hE' hr).trans h.uniq.clause_d
  have hcore : GLAPPrimeCoreOf 3 (Cg u) ≤ M := le_sup_left.trans (h.uniq.clause_a u huB hu1)
  have eK : barOf 3 Kc ≃* ↥(barX 3 (Cg u) Kc) := quotEquivBarX hp hKc.1 hKc.2.1
  have hKt : IsComponentOf (barX 3 (Cg u) Kc) ⊤ :=
    Lemma1314.isComponentOf_barX_of_glaPComponent hKc
  have hperf : commutator ↥(barX 3 (Cg u) Kc) = ⊤ := hKt.2.2.1
  have hBtel : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
  have hcen1 : CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
      Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) = 1 :=
    le_antisymm hcen (InputsSeitz6.one_le_pRank_cen_bar hBel huB hu1 Kc)
  have hZp : IsPGroup 3 ↥(Subgroup.center ↥(barX 3 (Cg u) Kc)) :=
    Inputs245b.isPGroup_center_of_component hp (glaPPrimeCore_quotient_eq_bot hp) hKt
  have hZne : Subgroup.center ↥(barX 3 (Cg u) Kc) ≠ ⊥ := center_ne_bot_of_mulEquiv eK hZ
  have eZ : ↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc) ≃*
      (TauCeti.CFSGIndex.lie i).Group := (Lemma1315b.centerQuotEquiv eK.symm).trans e
  obtain ⟨i1, hv⟩ := i
  simp only at hiq
  subst hiq
  have hq8 : q.p ^ q.exponent = 8 := by rw [hq.1, hq.2]; norm_num
  have hZ3 : Nat.card ↥(Subgroup.center ↥(barX 3 (Cg u) Kc)) = 3 :=
    CFSG.HardMathSupport.Lang.E6Descent.card_center_eq_three_E6 hGA hKt hZp hZne
      (Or.inr ⟨q, hv, ⟨eZ⟩, by rw [TauCeti.PrimePower.card_def, hq8]; norm_num⟩)
  obtain ⟨Kf, fK, σ, hKf, hσ, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite Kf := Nat.finite_of_card_ne_zero (by rw [hKf]; positivity)
  have hKf8 : Nat.card Kf = 8 ^ 2 := by rw [hKf, hq8]
  have hσ8 : ∀ c, σ c = c ^ 8 := fun c => by rw [hσ, hq8]
  have h2Kf : ringChar Kf = 2 :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.ringChar_eq_of_card_pow (f := 3) Nat.prime_two
      (by norm_num) Kf (by rw [hKf8]; norm_num)
  obtain ⟨e'⟩ : Nonempty ((↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc)) ≃*
      ↥(twistedE6RootGroup Kf σ)) := ⟨eZ.trans eC⟩
  obtain ⟨hle, -, -⟩ := hhigh Kf σ e' hσ hKf
  set A' : Subgroup (MulAut ↥(twistedE6RootGroup Kf σ)) :=
    (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)).map (MulAut.congr e').toMonoidHom with hA'
  have hAel : IsElemAbelian 3 (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isElemAbelian_autImage hBtel
  have hA'el : IsElemAbelian 3 A' := hAel.map _
  have hA'card : Nat.card A' = 3 ^ (CFSG.Open.pRank 3 B - 1) := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.congr e').injective, hcard]
  have hA'ni : ¬ A' ≤ twistedE6Inn Kf σ := by
    intro hA'I
    apply hni
    have h1 : autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≤
        (MulAut.conj : (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc)) →* _).range := by
      intro φ hφ
      have h2 : MulAut.congr e' φ ∈ (MulAut.conj : ↥(twistedE6RootGroup Kf σ) →* _).range :=
        hA'I ⟨φ, hφ, rfl⟩
      rw [← CFSG.LieType.SeitzGeneration.map_range_conj_congr e'] at h2
      obtain ⟨ψ, hψ, hψφ⟩ := h2
      rw [(MulAut.congr e').injective hψφ] at hψ
      exact hψ
    rintro α ⟨n, hn, rfl⟩
    have hqc : CFSG.LocalAnalysis.GLTheoremB.quotientCenterAut' ↥(barX 3 (Cg u) Kc)
        ((barX 3 (Cg u) Kc).normalizerMonoidHom n) = actHom (barX 3 (Cg u) Kc) n := by
      ext s
      induction s using QuotientGroup.induction_on with
      | H k => rfl
    have h3 : CFSG.LocalAnalysis.GLTheoremB.quotientCenterAut' ↥(barX 3 (Cg u) Kc)
        ((barX 3 (Cg u) Kc).normalizerMonoidHom n) ∈
          CFSG.HardMathSupport.Solomon.LocalBalance.innerAut
            (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc)) := by
      rw [hqc]
      exact h1 ⟨n, Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_subgroupOf.1 hn, n.2⟩, rfl⟩
    exact Inputs123b.mem_innerAut_of_quotientCenterAut' hperf h3
  obtain ⟨x, hxA', hxI⟩ := Set.not_subset.1 hA'ni
  haveI : Finite ↥A' := Nat.finite_of_card_ne_zero (by rw [hA'card]; positivity)
  have hx3 : x ^ 3 = 1 := hA'el.2 x hxA'
  have hx1 : x ≠ 1 := fun h1 => hxI (h1 ▸ (twistedE6Inn Kf σ).one_mem)
  have hxo : orderOf (⟨x, hxA'⟩ : ↥A') = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hx3)) (fun h1 => hx1 (congrArg Subtype.val h1))
  have h27 : 3 ^ 3 ∣ Nat.card ↥A' := by
    rw [hA'card]; exact pow_dvd_pow 3 (by omega)
  obtain ⟨A₀', hA₀'c, hxA₀'⟩ := Sylow.exists_subgroup_card_pow_prime_le 3 h27
    (Subgroup.zpowers (⟨x, hxA'⟩ : ↥A')) (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
    (by norm_num)
  set A₀ : Subgroup (MulAut ↥(twistedE6RootGroup Kf σ)) := A₀'.map A'.subtype with hA₀
  have hA₀A' : A₀ ≤ A' := Subgroup.map_subtype_le A₀'
  have hA₀c : Nat.card A₀ = 3 ^ 3 := by
    rw [hA₀, Subgroup.card_map_of_injective A'.subtype_injective, hA₀'c]
  have hxA₀ : x ∈ A₀ := ⟨⟨x, hxA'⟩, hxA₀' (Subgroup.mem_zpowers _), rfl⟩
  have hA₀el : IsElemAbelian 3 A₀ := hA'el.mono hA₀A'
  have hA₀D : A₀ ≤ twistedE6Inn Kf σ ⊔ twistedE6Diag Kf σ := hA₀A'.trans hle
  have hA₀ni : ¬ A₀ ≤ twistedE6Inn Kf σ := fun h1 => hxI (h1 hxA₀)
  have hA₀R : ¬ CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6NormalizesR Kf σ A₀ := by
    rintro ⟨Rr, hR1, hRp, hRE⟩
    rw [h2Kf] at hRp
    exact Claims1310s.not_noPlaneTwoSub_of_congr e' hno hA₀A' (by rw [hA₀c]; norm_num) hR1 hRp
      (fun φ hφ v hv => by rw [← hRE φ hφ]; exact ⟨v, hv, rfl⟩)
  have hgen := hD Kf σ 8 (by rw [h2Kf]; norm_num) hσ8 hKf8 (by norm_num) (by norm_num) A₀ hA₀el hA₀c
    hA₀D hA₀ni hA₀R
  have hgenS := closure_fixed_eq_top_of_seitzHyperGamma e' hgen
  refine Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc
    ((le_gammaPrime_of_fixed_center_three (k := 2) hperf hBtel hZ3 _ ?_ hgenS).trans
      (Claims1310r.gammaPrimeIn_le_glbCore le_rfl _ _))
  rintro P ⟨F, hFA₀, hFi, rfl⟩
  have hF9 : Nat.card F = 3 ^ 2 := by
    have h1 := Subgroup.relIndex_mul_card F A₀
    rw [inf_of_le_left hFA₀, hFi, hA₀c] at h1
    norm_num at h1 ⊢
    omega
  have hPA : F.map (MulAut.congr e').symm.toMonoidHom ≤
      autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) := by
    rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨φ, hφ, hφψ⟩ := hA₀A' (hFA₀ hψ)
    rw [← hφψ]
    show (MulAut.congr e').symm ((MulAut.congr e') φ) ∈ _
    rw [MulEquiv.symm_apply_apply]
    exact hφ
  rw [pRank_actPre hp hBtel hperf hPA (r := 2)
    (by rw [Subgroup.card_map_of_injective (MulAut.congr e').symm.injective, hF9]), hcen1]

theorem false_of_twE6Two (hX : Rank3CuResExcSeven)
    {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139b : Prop139b p M D) {U : Subgroup G}
    (hU : IsU1312 p B M D L0 d U) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) {Kc : Subgroup G}
    (hKc : GLAPComponent 3 (Cg u) Kc) (hN : B ≤ Subgroup.normalizer (Kc : Set G))
    (hcen : CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
      Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ 1)
    (i : TauCeti.ValidLieTypeIndex)
    (e : barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc) ≃* (TauCeti.CFSGIndex.lie i).Group)
    {q : TauCeti.PrimePower} (hq : IsTwoPow q 1) (hiq : i.1 = .twistedE6 q)
    (hno : Claims1310r.NoPlaneTwoSub (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc))) : False := by
  classical
  obtain ⟨hcard, -⟩ := Claims1310r.card_autImage_eq h h139b hU hu hu1 hKc hN hcen
  obtain ⟨hp3, -⟩ := h139b
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hBel : IsElemAbelian 3 B := h.bOne.1.1
  have huB : u ∈ B := hU.1.1 hu
  have eK : barOf 3 Kc ≃* ↥(barX 3 (Cg u) Kc) := quotEquivBarX hp hKc.1 hKc.2.1
  have hKt : IsComponentOf (barX 3 (Cg u) Kc) ⊤ :=
    Lemma1314.isComponentOf_barX_of_glaPComponent hKc
  have hBtel : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
  have eZ : ↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc) ≃*
      (TauCeti.CFSGIndex.lie i).Group := (Lemma1315b.centerQuotEquiv eK.symm).trans e
  have hm5 : 5 ≤ CFSG.Open.pRank 3 B := by
    obtain ⟨-, Ub, Q, hUK, hU1, hU2, hQK, hQel, hQcard, hQN, hQC⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.bal209TwoParabolic_holds
        (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)) (barX 3 (Cg u) Kc) hKt.2.2
        ⟨i, by rw [hiq]; exact hq, ⟨eZ⟩⟩
    have hDel : IsElemAbelian 3 (barX 3 (Cg u) B ⊓
        Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
          Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) := hBtel.mono inf_le_left
    have hc1 := InputsSeitz6.one_le_pRank_cen_bar hBel huB hu1 Kc
    have hQD : ∀ a ∈ Q, ∀ b ∈ barX 3 (Cg u) B ⊓
        Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
          Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))), a * b = b * a := fun a ha b hb =>
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 a (hQK ha)
    have hQDbot : Q ⊓ (barX 3 (Cg u) B ⊓
        Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
          Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) = ⊥ := by
      rw [eq_bot_iff, ← hQC]
      exact inf_le_inf_left Q inf_le_right
    have hQDel := IsElemAbelian.sup_of_commute hQel hDel hQD
    have hQDc : Nat.card ↥(Q ⊔ (barX 3 (Cg u) B ⊓
        Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
          Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))))) =
        3 ^ (4 + CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
          Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
            Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))))) := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.i224_card_sup hQD hQDbot, hQcard,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoAux.card_eq_pow_pRank hp hDel, pow_add]
    have hQDN : Q ⊔ (barX 3 (Cg u) B ⊓
        Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
          Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ Subgroup.normalizer (Ub : Set _) :=
      sup_le hQN fun y hy =>
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoAux.mem_normalizer_of_mem_centralizer hUK
          (Subgroup.mem_inf.1 hy).2
    have hrk := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoAux.le_glaTwoLocalRank_of_elemAb
      hp hU1 hU2 hQDN hQDel hQDc
    have hrk2 := Claims1310r.twoLocalRank_quot_le h.standing (Cg u)
    have hBm : CFSG.Open.pRank 3 B = m := Claims1310.pRank_B_eq h
    omega
  obtain ⟨i1, hv⟩ := i
  simp only at hiq
  subst hiq
  have hq2 : q.p ^ q.exponent = 2 := by rw [hq.1, hq.2]; norm_num
  obtain ⟨Kf, fK, σ, hKf, hσ, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite Kf := Nat.finite_of_card_ne_zero (by rw [hKf]; positivity)
  obtain ⟨e'⟩ : Nonempty ((↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc)) ≃*
      ↥(twistedE6RootGroup Kf σ)) := ⟨eZ.trans eC⟩
  set A' : Subgroup (MulAut ↥(twistedE6RootGroup Kf σ)) :=
    (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)).map (MulAut.congr e').toMonoidHom with hA'
  have hAel : IsElemAbelian 3 (autImage (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isElemAbelian_autImage hBtel
  have hA'el : IsElemAbelian 3 A' := hAel.map _
  have hA'card : Nat.card A' = 3 ^ (CFSG.Open.pRank 3 B - 1) := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.congr e').injective, hcard]
  haveI : Finite ↥A' := Nat.finite_of_card_ne_zero (by rw [hA'card]; positivity)
  have h81 : 3 ^ 4 ∣ Nat.card ↥A' := by
    rw [hA'card]; exact pow_dvd_pow 3 (by omega)
  obtain ⟨D₀, hD₀c, -⟩ := Sylow.exists_subgroup_card_pow_prime_le 3 h81 (⊥ : Subgroup ↥A') (n := 0)
    (by rw [Subgroup.card_bot, pow_zero]) (by norm_num)
  obtain ⟨F, hFD, hF9, V, hV1, hV2, hVF⟩ := hX Kf σ (by rw [hKf, hq2]) (fun c => by rw [hσ, hq2])
    (D₀.map A'.subtype) (hA'el.mono (Subgroup.map_subtype_le D₀))
    (by rw [Subgroup.card_map_of_injective A'.subtype_injective, hD₀c])
  exact Claims1310s.not_noPlaneTwoSub_of_congr e' hno (hFD.trans (Subgroup.map_subtype_le D₀)) hF9 hV1 hV2
    hVF

theorem rank3CuResExcSix_of_seven (hGA : GriessMultipliersAllModels)
    (hD : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDefs.TwE6DiagNonParCubes)
    (hX : Rank3CuResExcSeven) : Claims1310s.Rank3CuResExcSix := by
  intro G _ _ m p B M E A D T R L0 d h h139b U hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal hZ htype
  obtain ⟨i, ⟨e⟩, hcase⟩ := htype
  rcases hcase with ⟨q, hq, hiq, hno, -⟩ | ⟨q, hq, hiq, hno, hni, hhigh⟩
  · exact (false_of_twE6Two hX h h139b hU hu hu1 hKc hN hcen i e hq hiq hno).elim
  · exact le_M_of_twE6Eight hGA hD h h139b hU hu hu1 hKc hN hcen hZ i e hq hiq hno hni hhigh

section NotAll24


theorem rank3CuResExcSix_of_notAll24 (hGA : GriessMultipliersAllModels)
    (h2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hNot : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.TwE6NotAll24Gen)
    (hX : Rank3CuResExcSeven) : Claims1310s.Rank3CuResExcSix :=
  rank3CuResExcSix_of_seven hGA
    (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.twE6DiagNonParCubes_of_core h2
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.twE6ThreeA2LineStmt_holds
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.twE6ThreeA2Conj_holds
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.twE6ThreeLayerGen_holds
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.twE6ThreeTorusGen_holds
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.twE6ThreeCompGen_holds hNot) hX

end NotAll24

end Cases

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310t

end
