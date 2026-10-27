module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynO
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
import all CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265C.DynE

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GField

section Groups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.CanonTriL (isComponentOf_transport
  mem_innAutDerived_of_innDiagKind_exc)


theorem tagLie_adjointE_three {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] (hK2 : ringChar K = 2) (hK3 : Nat.card K % 3 = 2)
    {β : MulAut ↥(adjointGroup τ K)} (hβmem : β ∈ innAutDerived ↥(adjointGroup τ K))
    (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) {J : Subgroup ↥(adjointGroup τ K)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    TagLieType IsADETag 2 ↥J := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨h, hh, hβh, hp1, hh1⟩ :=
    exists_inndiag_of_mem_innAutDerived_E hτ hp β hβmem hβ3 hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : 3 ≠ ringChar K := by rw [hK2]; exact hp2
  have hpK : ¬ 3 ∣ Nat.card K := fun h' =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow (hK ▸ h')))
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ f.pos hp hp2 hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt τ 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with rfl | rfl | rfl <;> simp) hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    single_edge_perfect τ K (by rcases hτ with rfl | rfl | rfl <;> simp)
  obtain ⟨S, a, ι, hSq, ⟨Fr, hFr, hΦ⟩, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime (τ := τ) (Or.inr (Or.inr hτ)) hp hpK hp₀ hp₀K hq₀'
      hmon hperf β h (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (by rw [hℓL]; exact hpℓ.symm)
  have hsmall : τ = .G2 → 5 ≤ 3 ∨ 4 ≤ S.D.q := fun h' =>
    absurd h' (by rcases hτ with rfl | rfl | rfl <;> decide)
  have hTame := langSetup_hTame_of_prime S hp hpL hsmall hT hap h1
  obtain ⟨i, hqs, hJR⟩ := components_of_langSetup S hp ι hinj hrange β hconj hT hap h1 hTame hJ
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have hch : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
  have hFr' : ∀ c, Fr c = c ^ S.D.q := fun c => by rw [hSq]; exact hFr c
  have hNG := tagLie_rationalComponent_untw hτ S hFr' hΦ (by rw [hSq]; exact hK3) hT hap h1 i hqs
  rw [hch] at hNG
  exact hNG.of_mulEquiv eJ.symm

theorem tagLie_of_adjointEquiv_three {S : Type} [Group S] [Finite S] {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 1) (ψ : S ≃* ↥(adjointGroup τ K)) {β : MulAut S}
    (hβmem : β ∈ innAutDerived S) (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    TagLieType IsADETag 2 ↥J := by
  have hK2 : ringChar K = 2 := by
    haveI := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
    exact ringChar.eq K 2
  have hβ'mem : MulAut.congr ψ β ∈ innAutDerived _ := (mem_innAutDerived_congr ψ).2 hβmem
  have hβ'3 : (MulAut.congr ψ β) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hβ'1 : MulAut.congr ψ β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr ψ).injective (by rw [h, map_one]))
  have hJG := tagLie_adjointE_three hτ hK2 (by rw [hK]; norm_num) hβ'mem hβ'3 hβ'1
    (isComponentOf_transport ψ β hJ)
  exact hJG.of_mulEquiv (J.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm

theorem tagLie_E_three {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hin : InnDiagKind S labL β) (hβ3 : β ^ 3 = 1)
    (hβ1 : β ≠ 1) (ht : labL.tag = .E6 ∨ labL.tag = .E7 ∨ labL.tag = .E8) (hn1 : labL.n = 1)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    TagLieType IsADETag 2 ↥J := by
  classical
  have hS : HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hβmem : β ∈ innAutDerived S := mem_innAutDerived_of_innDiagKind_exc hcen
    (Or.inr (ht.imp id (Or.imp id Or.inl))) hin
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  obtain ⟨t, r, n⟩ := labL
  simp only at ht hn1
  subst hn1
  rcases ht with rfl | rfl | rfl
  · have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .E6 0 2 1 := hM
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ :=
      CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
    have hZ : Subgroup.center ↥(adjointGroup .E6 K) = ⊥ := center_adjointGroup_eq_bot
    exact tagLie_of_adjointEquiv_three (Or.inl rfl) hK
      ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
        (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)))
      hβmem hβ3 hβ1 hJ
  · have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .E7 0 2 1 := hM
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ :=
      CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
    have hZ : Subgroup.center ↥(adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot
    exact tagLie_of_adjointEquiv_three (Or.inr (Or.inl rfl)) hK
      ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
        (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)))
      hβmem hβ3 hβ1 hJ
  · have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .E8 0 2 1 := hM
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ :=
      CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
    have hZ : Subgroup.center ↥(adjointGroup .E8 K) = ⊥ := center_adjointGroup_eq_bot
    exact tagLie_of_adjointEquiv_three (Or.inr (Or.inr rfl)) hK
      ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
        (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)))
      hβmem hβ3 hβ1 hJ

theorem tagLie_twE6_of_inndiag {K : Type} [Field K] [Finite K] {q : TauCeti.PrimePower}
    (hK : Nat.card K = (q.p ^ q.exponent) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (hq2 : q.p = 2) {h : ↥(twistedE6InndiagGL K σ)} (hp1 : h ^ p = 1)
    (hh1 : h ≠ 1)
    {J : Subgroup ↥(twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (twistedE6InndiagConj K σ h))) :
    TagLieType (fun t => IsADETag t ∨ t = .trialityD4) 2 ↥J := by
  classical
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_setup_prime q.prime_p
      q.exponent_pos hp hp2 hpq
  have hmon : MonomialToralAt Tag.E6 p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_exc
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E6_five
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E7_five
      (by simp) hp hp2
  obtain ⟨LS, a, ι, _hSq, hΦ, hT, hap, h1, hinj, hrange, hconj⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_of_inndiag_twE6_of_prime
      q.prime_p q.exponent_pos hK σ hσ hp hpq hp₀ hp₀ℓ hq₀ hmon (twistedE6InndiagConj K σ h)
      (h : ModGL TwistTag.E6.tag K) h.2 (twistedE6InndiagConj_apply h)
      (by rw [← Subgroup.coe_pow, hp1]; rfl) (fun h' => hh1 (Subtype.ext h'))
  have hTame :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime LS hp
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.natCast_ne_zero_algebraicClosure_of_ne
        q.prime_p hp hK hpq) (fun h => absurd h (by decide)) hT hap h1
  obtain ⟨i, hqi, hJR⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup
    LS hp ι hinj hrange _ hconj hT hap h1 hTame hJ
  let eJ : ↥J ≃* ↥(rationalComponent LS.ρ LS.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have hℓL : ringChar (AlgebraicClosure K) = q.p := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure]
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow
      (n := q.exponent * 2) q.prime_p (by have := q.exponent_pos; omega)
      (by rw [hK, ← pow_mul])
  have hNG := tagLie_rationalComponent_E6 LS hp hT hap h1 i hqi
  rw [hℓL, hq2] at hNG
  exact hNG.of_mulEquiv eJ.symm

theorem tagLie_twE6 {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hin : InnDiagKind S labL β) (hβp : β ^ p = 1) (hβ1 : β ≠ 1) (ht : labL.tag = .twE6)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    TagLieType (fun t => IsADETag t ∨ t = .trialityD4) 2 ↥J := by
  classical
  have hS : HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hβmem : β ∈ innAutDerived S :=
    mem_innAutDerived_of_innDiagKind_exc hcen (Or.inr (Or.inr (Or.inr (Or.inr ht)))) hin
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  obtain ⟨t, r, n⟩ := labL
  simp only at ht
  subst ht
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .twistedE6 0 2 n := hM
  have hn : 1 ≤ n := hLM.admissible.2.1
  obtain ⟨-, K₀, _, _, hK₀, σ₀, hσ₀, ⟨e₀⟩⟩ :=
    CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  have hq : q.card = 2 ^ n := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := TauCeti.LieTypeIndex.valid_twistedE6 q
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K₀ (by rw [hK₀, hq])
    σ₀ (fun x => by rw [hq]; exact hσ₀ x)
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  let ψ : S ≃* ↥(twistedE6RootGroup K σ) :=
    ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans e₀).trans
      (b.trans eK)
  have hβ : MulAut.congr ψ β ∈ innAutDerived ↥(twistedE6RootGroup K σ) :=
    (mem_innAutDerived_congr ψ).2 hβmem
  have hβ'p : (MulAut.congr ψ β) ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hβ'1 : MulAut.congr ψ β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr ψ).injective (by rw [h, map_one]))
  have hJ' := isComponentOf_transport ψ β hJ
  have hpq : p ≠ q.p := hp2
  obtain ⟨h, hh, hp1, hh1⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I141F.Exc.exists_twE6Inndiag_of_mem_innAutDerived (σ := σ) hK
      hσ hβ hβ'p hβ'1
  rw [← hh] at hJ'
  have hNG := tagLie_twE6_of_inndiag (σ := σ) hK hσ hp hp2 hpq rfl hp1 hh1 hJ'
  exact hNG.of_mulEquiv (J.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm

end Groups

section Separation


private theorem tag_eq_of_exc_models {X : Type} [Group X] [Finite X]
    {l₁ l₂ : CFSG.Assembly.LargeEvenLabel} (hl₁ : CFSG.Assembly.LargeEvenInLambda2 l₁)
    (hl₂ : CFSG.Assembly.LargeEvenInLambda2 l₂) (hE₁ : IsExcLab l₁) (hE₂ : IsExcLab l₂)
    (hM₁ : CFSG.StandardType.MarkedModel l₁ (X ⧸ Subgroup.center X))
    (hM₂ : CFSG.StandardType.MarkedModel l₂ (X ⧸ Subgroup.center X)) : l₁.tag = l₂.tag :=
  congrArg CFSG.Assembly.LargeEvenLabel.tag (exc_exc_case hl₁ hl₂ hE₁ hE₂ hM₁ hM₂)

theorem tag_eq_of_target {X : Type} [Group X] [Finite X] {t T : StatedLieTag} {r e : ℕ}
    (ht : IsADETag t ∨ t = .trialityD4)
    (hm : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t r 2 e)
    (hT : T = .F4 ∨ T = .Tits ∨ T = .twistedE6 ∨ T = .trialityD4)
    (hM : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) T 0 2 1) : t = T := by
  have he : 1 ≤ e := hm.admissible.2.1
  have hcls : (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus) → t = T :=
    fun hc => (S265C.DynO.false_of_classicalOr360 (Or.inl ⟨t, r, e, hc, hm⟩) hT hM).elim
  obtain ⟨lT, hlT, hET, hMT, htT⟩ : ∃ lT : CFSG.Assembly.LargeEvenLabel,
      CFSG.Assembly.LargeEvenInLambda2 lT ∧ IsExcLab lT ∧
        CFSG.StandardType.MarkedModel lT (X ⧸ Subgroup.center X) ∧
        ((T = .F4 ∧ lT.tag = .F4) ∨ (T = .Tits ∧ lT.tag = .twF4der) ∨
          (T = .twistedE6 ∧ lT.tag = .twE6) ∨ (T = .trialityD4 ∧ lT.tag = .triD4)) := by
    rcases hT with rfl | rfl | rfl | rfl
    · exact ⟨⟨.F4, 0, 1⟩, by simp [CFSG.Assembly.LargeEvenInLambda2], by simp [IsExcLab], hM,
        Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨⟨.twF4der, 0, 1⟩, by simp [CFSG.Assembly.LargeEvenInLambda2], by simp [IsExcLab],
        hM, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨⟨.twE6, 0, 1⟩, by simp [CFSG.Assembly.LargeEvenInLambda2], by simp [IsExcLab], hM,
        Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨⟨.triD4, 0, 1⟩, by simp [CFSG.Assembly.LargeEvenInLambda2], by simp [IsExcLab], hM,
        Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  have hexc : ∀ u : CFSG.Assembly.LargeEvenLieTag,
      (u = .E6 ∨ u = .E7 ∨ u = .E8 ∨ u = .twE6 ∨ u = .triD4) →
      CFSG.StandardType.MarkedModel ⟨u, 0, e⟩ (X ⧸ Subgroup.center X) → u = lT.tag := by
    intro u hu hMu
    refine tag_eq_of_exc_models (l₁ := ⟨u, 0, e⟩) ?_ hlT ?_ hET hMu hMT
    · rcases hu with rfl | rfl | rfl | rfl | rfl <;>
        simp [CFSG.Assembly.LargeEvenInLambda2, he]
    · rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp [IsExcLab]
  have hr0 : t ≠ .PSL → t ≠ .PSU → t ≠ .POmegaPlus → t ≠ .POmegaMinus → r = 0 := by
    intro h1 h2 h3 h4
    rcases ht with ht | rfl
    · rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl h1
      · exact absurd rfl h2
      · exact absurd rfl h3
      · exact absurd rfl h4
      · exact hm.admissible.2.2
      · exact hm.admissible.2.2
      · exact hm.admissible.2.2
      · exact hm.admissible.2.2
    · exact hm.admissible.2.2
  rcases ht with ht | rfl
  · rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcls (Or.inl rfl)
    · exact hcls (Or.inr (Or.inl rfl))
    · exact hcls (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact hcls (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · obtain rfl := hr0 (by decide) (by decide) (by decide) (by decide)
      have h := hexc .E6 (Or.inl rfl) hm
      rcases htT with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ <;>
        exact absurd (h.trans h') (by decide)
    · obtain rfl := hr0 (by decide) (by decide) (by decide) (by decide)
      have h := hexc .E7 (Or.inr (Or.inl rfl)) hm
      rcases htT with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ <;>
        exact absurd (h.trans h') (by decide)
    · obtain rfl := hr0 (by decide) (by decide) (by decide) (by decide)
      have h := hexc .E8 (Or.inr (Or.inr (Or.inl rfl))) hm
      rcases htT with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ <;>
        exact absurd (h.trans h') (by decide)
    · obtain rfl := hr0 (by decide) (by decide) (by decide) (by decide)
      have h := hexc .twE6 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hm
      rcases htT with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩
      · exact absurd (h.trans h') (by decide)
      · exact absurd (h.trans h') (by decide)
      · rfl
      · exact absurd (h.trans h') (by decide)
  · obtain rfl := hr0 (by decide) (by decide) (by decide) (by decide)
    have h := hexc .triD4 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hm
    rcases htT with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩
    · exact absurd (h.trans h') (by decide)
    · exact absurd (h.trans h') (by decide)
    · exact absurd (h.trans h') (by decide)
    · rfl

end Separation

section Catalogue


theorem catalogIs_E7two_of_hasLabel {S : Type} [Group S] (hcen : Subgroup.center S = ⊥)
    {lab : GLALabel} (h : HasLabel S (· = lab)) (ht : lab.tag = .E7) (hn : lab.n = 1) :
    catalogIs S isE7TwoIdx := by
  obtain ⟨t, r, n⟩ := lab
  simp only at ht hn
  subst ht hn
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .E7 0 2 1 :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel h
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
  let q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, one_pos⟩
  have hq : q.card = 2 ^ 1 := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.E7 q).Valid := TauCeti.LieTypeIndex.valid_E7 q
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv K (by rw [hK, hq])
  exact ⟨.lie ⟨.E7 q, hv⟩, by simp [isE7TwoIdx, onLie, q],
    ⟨(CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans (eK.trans b)⟩⟩

theorem catalogIs_E8two_of_hasLabel {S : Type} [Group S] (hcen : Subgroup.center S = ⊥)
    {lab : GLALabel} (h : HasLabel S (· = lab)) (ht : lab.tag = .E8) (hn : lab.n = 1) :
    catalogIs S isE8TwoIdx := by
  obtain ⟨t, r, n⟩ := lab
  simp only at ht hn
  subst ht hn
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .E8 0 2 1 :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel h
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
  let q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, one_pos⟩
  have hq : q.card = 2 ^ 1 := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.E8 q).Valid := by simp
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv K (by rw [hK, hq])
  exact ⟨.lie ⟨.E8 q, hv⟩, by simp [isE8TwoIdx, onLie, q],
    ⟨(CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans (eK.trans b)⟩⟩

theorem catalogIs_TE6two_of_hasLabel {S : Type} [Group S] (hcen : Subgroup.center S = ⊥)
    {lab : GLALabel} (h : HasLabel S (· = lab)) (ht : lab.tag = .twE6) (hn : lab.n = 1) :
    catalogIs S S9.isTE6two := by
  obtain ⟨t, r, n⟩ := lab
  simp only at ht hn
  subst ht hn
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .twistedE6 0 2 1 :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel h
  obtain ⟨-, K₀, _, _, hK₀, σ₀, hσ₀, ⟨e₀⟩⟩ :=
    CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
  let q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, one_pos⟩
  have hq : q.card = 2 ^ 1 := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := TauCeti.LieTypeIndex.valid_twistedE6 q
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K₀ (by rw [hK₀, hq])
    σ₀ (fun x => by rw [hq]; exact hσ₀ x)
  exact ⟨.lie ⟨.twistedE6 q, hv⟩, by simp [S9.isTE6two, onLie, q],
    ⟨(CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans (e₀.trans b)⟩⟩

end Catalogue

section Main

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)


theorem target_tag_of_isELabel {S : Type} [Group S] [Finite S] {labL : GLALabel}
    {β : MulAut S} (hcen : Subgroup.center S = ⊥) (hin : InnDiagKind S labL β)
    (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) (hE : IsELabel labL) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) {T : StatedLieTag}
    (hT : T = .F4 ∨ T = .Tits ∨ T = .twistedE6 ∨ T = .trialityD4)
    (hM : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) T 0 2 1) :
    labL.n = 1 ∧ (T = .twistedE6 ∨ (T = .trialityD4 ∧ labL.tag = .twE6)) := by
  have hnd : labL.tag ≠ .B2der ∧ labL.tag ≠ .G2der ∧ labL.tag ≠ .twF4der := by
    rcases hE with h | h | h | h <;> rw [h] <;> exact ⟨by decide, by decide, by decide⟩
  have hn1 := S265C.DynO.n_eq_one_of_component_over_two hcen hin hβ3 hβ1 hnd hJ hM
  refine ⟨hn1, ?_⟩
  by_cases htw : labL.tag = .twE6
  · obtain ⟨t, r, e, ht, hm⟩ :=
      tagLie_twE6 Nat.prime_three (by norm_num) hcen hin hβ3 hβ1 htw hJ
    have hteq := tag_eq_of_target ht hm hT hM
    subst hteq
    rcases ht with ht | ht
    · rcases ht with h | h | h | h | h | h | h | h <;>
        rcases hT with h' | h' | h' | h' <;>
        first
        | exact Or.inl h'
        | exact absurd (h.symm.trans h') (by decide)
    · exact Or.inr ⟨ht, htw⟩
  · have hE' : labL.tag = .E6 ∨ labL.tag = .E7 ∨ labL.tag = .E8 := by
      rcases hE with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd h htw
    obtain ⟨t, r, e, ht, hm⟩ := tagLie_E_three hcen hin hβ3 hβ1 hE' hn1 hJ
    have hteq := tag_eq_of_target (Or.inl ht) hm hT hM
    subst hteq
    rcases ht with h | h | h | h | h | h | h | h <;>
      rcases hT with h' | h' | h' | h' <;>
      first
      | exact Or.inl h'
      | exact absurd (h.symm.trans h') (by decide)

theorem dynCThreeS_E : DynCThreeS IsELabel := by
  intro S _ _ labL β hcen hin hβ3 hβ1 hE J hJ
  have hS : HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have key := fun {T : StatedLieTag} hT hM =>
    target_tag_of_isELabel (T := T) hcen hin hβ3 hβ1 hE hJ hT hM
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨-, h' | ⟨h', -⟩⟩ := key (Or.inl rfl) (S265C.DynO.lieModel_of_isF4two h) <;>
      exact absurd h' (by decide)
  · obtain ⟨-, h' | ⟨h', -⟩⟩ := key (Or.inr (Or.inl rfl)) (S265C.DynO.lieModel_of_isTitsIdx h) <;>
      exact absurd h' (by decide)
  · obtain ⟨hn1, -⟩ := key (Or.inr (Or.inr (Or.inl rfl))) (S265C.DynO.lieModel_of_isTE6two h)
    have hJc : Nat.card (↥J ⧸ Subgroup.center ↥J) = 76532479683774853939200 := by
      rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder (S265C.DynO.lieModel_of_isTE6two h)]
      decide
    have hdvd : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card S :=
      (Subgroup.index_dvd_card _).trans (Subgroup.card_subgroup_dvd_card J)
    have hlt : Nat.card (↥J ⧸ Subgroup.center ↥J) < Nat.card S := by
      calc Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card ↥J :=
            Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
        _ ≤ Nat.card ↥(fixSubgroup β) := Subgroup.card_le_of_le hJ.1
        _ < Nat.card S := CanonTriL.card_fixSubgroup_lt hβ1
    rcases hE with ht | ht | ht | ht
    · exfalso
      obtain ⟨tag, rank, n⟩ := labL
      simp only at ht hn1
      subst ht hn1
      have hc := CanonTriL.card_of_label_char_two hcen hS rfl
      simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
        CFSG.StandardType.markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hc
      rw [hJc, hc] at hdvd
      exact absurd hdvd (by decide)
    · exact (catalogIs_E7two_of_hasLabel hcen hS ht hn1).elim fun i hi => ⟨i, Or.inl hi.1, hi.2⟩
    · exact (catalogIs_E8two_of_hasLabel hcen hS ht hn1).elim fun i hi => ⟨i, Or.inr hi.1, hi.2⟩
    · exfalso
      obtain ⟨tag, rank, n⟩ := labL
      simp only at ht hn1
      subst ht hn1
      have hc := CanonTriL.card_of_label_char_two hcen hS rfl
      simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
        CFSG.StandardType.markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hc
      rw [hJc, hc] at hlt
      exact absurd hlt (by decide)
  · obtain ⟨hn1, h' | ⟨-, htw⟩⟩ :=
      key (Or.inr (Or.inr (Or.inr rfl))) (S265C.DynO.lieModel_of_isTD4two h)
    · exact absurd h' (by decide)
    · exact catalogIs_TE6two_of_hasLabel hcen hS htw hn1

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265C.DynE

end
