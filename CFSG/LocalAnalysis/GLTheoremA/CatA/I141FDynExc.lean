module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynClassical
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriLHolds2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F.Exc

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.CanonTriL
open scoped MatrixGroups commutatorElement

theorem notG2_of_typeA_models {X : Type} [Group X] {ν f : ℕ}
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL ν 2 f ∨
      StatedClassicalModel (X ⧸ Subgroup.center X) .PSU ν 2 f) :
    NotG2LieType 2 X := by
  rcases h with h | h
  · exact ⟨.PSL, ν, f, by decide, Or.inl ⟨by decide, h⟩⟩
  · exact ⟨.PSU, ν, f, by decide, Or.inl ⟨by decide, h⟩⟩

theorem notG2_of_centerQuot_sp {X : Type} [Group X] {m k : ℕ} {K : Type} [Field K] [Finite K]
    (hm : 2 ≤ m) (hne : ¬(m = 2 ∧ Nat.card K = 2)) (hK : Nat.card K = 2 ^ k)
    (e : X ⧸ Subgroup.center X ≃* StatedProj (StatedSp m K)) : NotG2LieType 2 X := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hK
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h0
  have hne' : (m, 2 ^ k) ≠ (2, 2) := fun h2 =>
    hne ⟨(Prod.mk.inj h2).1, by rw [hK]; exact (Prod.mk.inj h2).2⟩
  have hAdm : StatedLieAdmissible .PSp m 2 k := ⟨Nat.prime_two, hk1, hm, hne'⟩
  have hClass : StatedClassicalModel (X ⧸ Subgroup.center X) .PSp m 2 k :=
    ⟨hAdm, ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩⟩
  exact ⟨.PSp, m, k, by decide, Or.inl ⟨by decide, hClass⟩⟩

theorem notG2_of_spCover {X : Type} [Group X] {m k : ℕ} {K : Type} [Field K] [Finite K]
    (hm : 2 ≤ m) (hne : ¬(m = 2 ∧ Nat.card K = 2)) (hK : Nat.card K = 2 ^ k)
    (g : StatedSp m K →* X) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (StatedSp m K)) : NotG2LieType 2 X := by
  haveI : Fintype K := Fintype.ofFinite K
  have hne' : (m, Fintype.card K) ≠ (2, 2) := fun h =>
    hne ⟨(Prod.mk.inj h).1, by rw [Nat.card_eq_fintype_card]; exact (Prod.mk.inj h).2⟩
  have hSpPerf : commutator (StatedSp m K) = ⊤ := (spFactorFacts_holds K m hm hne').perfect
  obtain ⟨e₁⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hSpPerf g hg hker
  have hchar : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  obtain ⟨e₂⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp
    (s := m) hm hne hchar (MulEquiv.refl _)
  exact notG2_of_centerQuot_sp hm hne hK (e₁.trans e₂)

theorem notG2_adjointE
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] (hK2 : ringChar K = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut ↥(adjointGroup τ K)} (hβmem : β ∈ innAutDerived ↥(adjointGroup τ K))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) {J : Subgroup ↥(adjointGroup τ K)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    NotG2LieType 2 ↥J := by
  classical
  obtain ⟨h, _hh, hβh, hp1, hh1⟩ :=
    exists_inndiag_of_mem_innAutDerived_E hτ hp β hβmem hβp hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : p ≠ ringChar K := by rw [hK2]; exact hp2
  have hpK : ¬ p ∣ Nat.card K := fun h' =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow (hK ▸ h')))
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ f.pos hp hp2 hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with rfl | rfl | rfl <;> simp) hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    single_edge_perfect τ K (by rcases hτ with rfl | rfl | rfl <;> simp)
  obtain ⟨S, a, ι, _hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime (τ := τ) (Or.inr (Or.inr hτ)) hp hpK hp₀ hp₀K hq₀'
      hmon hperf β h (baseChange_mem_adjointGroup_of_mem_inndiag _hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (by rw [hℓL]; exact hpℓ.symm)
  have hsmall : τ = .G2 → 5 ≤ p ∨ 4 ≤ S.D.q := fun h' =>
    absurd h' (by rcases hτ with rfl | rfl | rfl <;> decide)
  have hTame := langSetup_hTame_of_prime S hp hpL hsmall hT hap h1
  obtain ⟨i, hqs, hJR⟩ := components_of_langSetup S hp ι hinj hrange β hconj hT hap h1 hTame hJ
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have hch : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
  have hNG := notG2_rationalComponent_E hτ S hp hT hap h1 i hqs
  rw [hch] at hNG
  exact hNG.of_mulEquiv eJ.symm

theorem notG2_of_adjointEquiv
    {S : Type} [Group S] [Finite S] {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (ψ : S ≃* ↥(adjointGroup τ K)) {β : MulAut S}
    (hβmem : β ∈ innAutDerived S) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    NotG2LieType 2 ↥J := by
  have hK2 : ringChar K = 2 := by
    haveI := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
    exact ringChar.eq K 2
  have hβ'mem : MulAut.congr ψ β ∈ innAutDerived _ := (mem_innAutDerived_congr ψ).2 hβmem
  have hβ'p : (MulAut.congr ψ β) ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hβ'1 : MulAut.congr ψ β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr ψ).injective (by rw [h, map_one]))
  have hJG := notG2_adjointE hτ hK2 hp hp2 hβ'mem hβ'p hβ'1 (isComponentOf_transport ψ β hJ)
  exact hJG.of_mulEquiv (J.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm

theorem notG2_E
    {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) (ht : labL.tag = .E6 ∨ labL.tag = .E7 ∨ labL.tag = .E8) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    NotG2LieType 2 ↥J := by
  classical
  have hS : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hβmem : β ∈ innAutDerived S := mem_innAutDerived_of_innDiagKind_exc hcen
    (Or.inr (ht.imp id (Or.imp id Or.inl))) hin
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  obtain ⟨t, r, n⟩ := labL
  simp only at ht
  rcases ht with rfl | rfl | rfl
  · have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .E6 0 2 n := hM
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ :=
      CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
    have hZ : Subgroup.center ↥(adjointGroup .E6 K) = ⊥ := center_adjointGroup_eq_bot
    exact notG2_of_adjointEquiv (Or.inl rfl) hK
      ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
        (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)))
      hβmem hp hp2 hβp hβ1 hJ
  · have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .E7 0 2 n := hM
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ :=
      CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
    have hZ : Subgroup.center ↥(adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot
    exact notG2_of_adjointEquiv (Or.inr (Or.inl rfl)) hK
      ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
        (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)))
      hβmem hp hp2 hβp hβ1 hJ
  · have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .E8 0 2 n := hM
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ :=
      CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
    have hZ : Subgroup.center ↥(adjointGroup .E8 K) = ⊥ := center_adjointGroup_eq_bot
    exact notG2_of_adjointEquiv (Or.inr (Or.inr rfl)) hK
      ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
        (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)))
      hβmem hp hp2 hβp hβ1 hJ

theorem exists_twE6Inndiag_of_mem_innAutDerived
    {K : Type} [Field K] [Finite K] {q : TauCeti.PrimePower}
    (hK : Nat.card K = (q.p ^ q.exponent) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent)) {p : ℕ}
    {β : MulAut ↥(twistedE6RootGroup K σ)}
    (hβmem : β ∈ innAutDerived ↥(twistedE6RootGroup K σ))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) :
    ∃ h : ↥(twistedE6InndiagGL K σ),
      twistedE6InndiagConj K σ h = β ∧ h ^ p = 1 ∧ h ≠ 1 := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ
      hσ
  have hKf : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  have hcyc : IsCyclic (RingAut K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic q.prime_p K hKf).2
  have hΘ : innAutDerived ↥(twistedE6RootGroup K σ) ≤ Θ.ker := by
    refine sup_le ?_ ?_
    · rw [hker]
      exact le_sup_left
    · rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcyc.isMulCommutative.is_comm.comm _ _
  have hmem : β ∈ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj, ← hker]
    exact hΘ hβmem
  obtain ⟨h, hh⟩ := hmem
  refine ⟨h, hh, ?_, ?_⟩
  · exact twistedE6InndiagConj_injective q.prime_p q.exponent_pos hK σ hσ
      (by rw [map_pow, hh, hβp, map_one])
  · exact fun h' => hβ1 (by rw [← hh, h', map_one])

theorem notG2_twE6_of_inndiag
    {K : Type} [Field K] [Finite K] {q : TauCeti.PrimePower}
    (hK : Nat.card K = (q.p ^ q.exponent) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (hq2 : q.p = 2) {h : ↥(twistedE6InndiagGL K σ)} (hp1 : h ^ p = 1)
    (hh1 : h ≠ 1)
    {J : Subgroup ↥(twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (twistedE6InndiagConj K σ h))) :
    NotG2LieType 2 ↥J := by
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
  have hNG := notG2_rationalComponent_E6 LS hp hT hap h1 i hqi
  rw [hℓL, hq2] at hNG
  exact hNG.of_mulEquiv eJ.symm

theorem notG2_twE6
    {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) (ht : labL.tag = .twE6) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    NotG2LieType 2 ↥J := by
  classical
  have hS : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel S (· = labL) :=
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
    exists_twE6Inndiag_of_mem_innAutDerived (σ := σ) hK hσ hβ hβ'p hβ'1
  rw [← hh] at hJ'
  have hNG := notG2_twE6_of_inndiag (σ := σ) hK hσ hp hp2 hpq rfl hp1 hh1 hJ'
  exact hNG.of_mulEquiv (J.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm

theorem notG2_f4_class_nonA
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) (hch : ringChar L = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit Tag.F4 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    NotG2LieType 2 ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
      Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 360 := by
  classical
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases f4_nonA_casesP2 hp hp2' S hpL hTp h1 i hnonA with ⟨v, hroots, -, -⟩ |
      ⟨v, J, hJ, hroots, -, -⟩
  · by_cases hQ : 3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
    · obtain ⟨K', hfin, hne, g, hg, hker⟩ := exists_spCover_of_spRange S hT i hinner (m := 2) le_rfl
        (fun K' hfin hcardK' => by
          haveI := hfin
          obtain ⟨k, hk⟩ := card_subfield_eq_two_pow hch K'
          have h3 : 3 ≤ Nat.card ↥K' := hcardK' ▸ hQ
          have h4 : 4 ≤ Nat.card ↥K' := by
            rw [hk] at h3 ⊢
            rcases Nat.lt_or_ge k 2 with hk2 | hk2
            · interval_cases k <;> omega
            · calc 4 = 2 ^ 2 := by norm_num
                _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
          haveI : CharP ↥K' 2 := ringChar.of_eq (by rw [ringChar_subfield' K', hch])
          refine ⟨fun h => by omega, ?_⟩
          obtain ⟨Ψ, hΨker, hΨrange⟩ := spRange_f4_B2 h4
          rw [CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4)
            (J := f4LeviB2) ↥K'] at hΨrange
          obtain ⟨Ψ', h', hr'⟩ := spRange_rootSpan_smul v (fun α hα => hα.1) hΨker hΨrange
          refine ⟨Ψ', h', ?_⟩
          rw [hr']
          show _ = rootSpan Tag.F4 ↥K' (componentRoots (rootCharHom a) i)
          rw [hroots])
      haveI := hfin
      obtain ⟨k, hk⟩ := card_subfield_eq_two_pow hch K'
      exact Or.inl (notG2_of_spCover le_rfl hne hk g hg hker)
    · obtain ⟨K', hfin, hK2, ⟨eR⟩⟩ :=
        exists_sp42_equiv_rationalComponent S hT i v hroots hinner (not_le.1 hQ) hqs
      haveI := hfin
      exact Or.inr (CFSG.LocalAnalysis.GLTheoremA.I141F.Cls.card_quot_center_eq_360_of_sp42
        hK2 eR)
  · obtain ⟨K', hfin, hne, g, hg, hker⟩ := exists_spCover_of_spRange S hT i hinner (m := 3)
      (by norm_num) (fun K' hfin hcardK' => by
        haveI := hfin
        obtain ⟨k, hk⟩ := card_subfield_eq_two_pow hch K'
        have hk0 : 0 < k := by
          rcases Nat.eq_zero_or_pos k with h0 | h0
          · have : 1 < Nat.card ↥K' := Finite.one_lt_card
            rw [hk, h0] at this
            norm_num at this
          · exact h0
        refine ⟨fun h => by omega, ?_⟩
        obtain ⟨Ψ, hΨker, hΨrange⟩ := spRange_f4_levi hJ hk0 hk
        rw [CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4)
          (J := J) ↥K'] at hΨrange
        obtain ⟨Ψ', h', hr'⟩ := spRange_rootSpan_smul v (fun α hα => hα.1) hΨker hΨrange
        refine ⟨Ψ', h', ?_⟩
        rw [hr']
        show _ = rootSpan Tag.F4 ↥K' (componentRoots (rootCharHom a) i)
        rw [hroots])
    haveI := hfin
    obtain ⟨k, hk⟩ := card_subfield_eq_two_pow hch K'
    exact Or.inl (notG2_of_spCover (by norm_num) hne hk g hg hker)

theorem notG2_or_card360_adjointF4
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut ↥(adjointGroup .F4 K)} (hβmem : β ∈ innAutDerived ↥(adjointGroup .F4 K))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) {J : Subgroup ↥(adjointGroup .F4 K)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    NotG2LieType 2 ↥J ∨ Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
  classical
  obtain ⟨h, hh, hβh, hp1, hh1⟩ := exists_inndiag_of_mem_innAutDerived_F4 β hβmem hβp hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : p ≠ ringChar K := by rw [hK2]; exact hp2
  have hpK : ¬ p ∣ Nat.card K := fun h' =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow (hK ▸ h')))
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ f.pos hp hp2 hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt .F4 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  have hperf : commutator ↥(adjointGroup .F4 K) = ⊤ := single_edge_perfect .F4 K (by simp)
  obtain ⟨S, a, ι, _hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime (τ := .F4) (Or.inr (Or.inl rfl)) hp hpK hp₀ hp₀K hq₀'
      hmon hperf β h (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (by rw [hℓL]; exact hpℓ.symm)
  have hsmall : Tag.F4 = .G2 → 5 ≤ p ∨ 4 ≤ S.D.q := fun h => absurd h (by decide)
  have hTame := langSetup_hTame_of_prime S hp hpL hsmall hT hap h1
  obtain ⟨i, hqs, hJR⟩ := components_of_langSetup S hp ι hinj hrange β hconj hT hap h1 hTame hJ
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  have hch : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · obtain ⟨ν, f', -, -, -, hmodel⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.RationalModel.rationalComponent_typeA_model S hp hT hap h1 i hA
        hqs
    rw [hch] at hmodel
    exact Or.inl ((notG2_of_typeA_models hmodel).of_mulEquiv eJ.symm)
  · by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · rcases notG2_f4_class_nonA S hch hp hp2 hT hap h1 i hA hinner hqs with h | h
      · exact Or.inl (h.of_mulEquiv eJ.symm)
      · exact Or.inr (by
          calc Nat.card (↥J ⧸ Subgroup.center ↥J) =
                Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
                  Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
                Nat.card_congr
                  (QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)).toEquiv
            _ = 360 := h)
    · have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
      rcases f4_nonA_casesP hp hp2' S hpL hTp h1 i hA with ⟨hr, hn⟩ | ⟨_, _, -, -, hr, hn⟩
      · exact (hinner (twistInner_of_shape S hT i 2 8 hr hn (by omega) (by omega) (by omega)
          (by omega))).elim
      · exact (hinner (twistInner_of_shape S hT i 3 18 hr hn (by omega) (by omega) (by omega)
          (by omega))).elim

theorem notG2_or_card360_F4
    {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) (ht : labL.tag = .F4) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    NotG2LieType 2 ↥J ∨ Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
  classical
  have hS : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hβmem : β ∈ innAutDerived S := mem_innAutDerived_of_innDiagKind_exc hcen (Or.inl ht) hin
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  obtain ⟨t, r, n⟩ := labL
  simp only at ht
  subst ht
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .F4 0 2 n := hM
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ :=
    CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
  have hZ : Subgroup.center ↥(adjointGroup .F4 K) = ⊥ := center_adjointGroup_eq_bot
  let ψ : S ≃* ↥(adjointGroup .F4 K) :=
    (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans
      (e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
  have hK2 : ringChar K = 2 := by
    haveI := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
    exact ringChar.eq K 2
  have hβ'mem : MulAut.congr ψ β ∈ innAutDerived _ := (mem_innAutDerived_congr ψ).2 hβmem
  have hβ'p : (MulAut.congr ψ β) ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hβ'1 : MulAut.congr ψ β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr ψ).injective (by rw [h, map_one]))
  have hNG := notG2_or_card360_adjointF4 hK2 hp hp2 hβ'mem hβ'p hβ'1
    (isComponentOf_transport ψ β hJ)
  let eJm : ↥J ≃* ↥(J.map ψ.toMonoidHom) :=
    J.equivMapOfInjective ψ.toMonoidHom ψ.injective
  rcases hNG with h | h
  · exact Or.inl (h.of_mulEquiv eJm.symm)
  · exact Or.inr (by
      calc Nat.card (↥J ⧸ Subgroup.center ↥J) =
            Nat.card (↥(J.map ψ.toMonoidHom) ⧸ Subgroup.center ↥(J.map ψ.toMonoidHom)) :=
            Nat.card_congr (QuotientGroup.congr _ _ eJm (Subgroup.map_center_eq eJm)).toEquiv
        _ = 360 := h)

theorem compType_E
    {S : Type} [Group S] [Finite S] {labL : GLALabel}
    {β : MulAut S} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) (ht : labL.tag = .E6 ∨ labL.tag = .E7 ∨ labL.tag = .E8)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    (∃ (t : StatedLieTag) (r e : ℕ),
        CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t r 2 e) ∨
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
  obtain ⟨t, r, e, -, hM⟩ := notG2_E hp hp2 hcen hin hβp hβ1 ht hJ
  exact Or.inl ⟨t, r, e, hM⟩

theorem compType_twE6
    {S : Type} [Group S] [Finite S] {labL : GLALabel}
    {β : MulAut S} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) (ht : labL.tag = .twE6)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    (∃ (t : StatedLieTag) (r e : ℕ),
        CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t r 2 e) ∨
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
  obtain ⟨t, r, e, -, hM⟩ := notG2_twE6 hp hp2 hcen hin hβp hβ1 ht hJ
  exact Or.inl ⟨t, r, e, hM⟩

theorem compType_F4
    {S : Type} [Group S] [Finite S] {labL : GLALabel}
    {β : MulAut S} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) (ht : labL.tag = .F4)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    (∃ (t : StatedLieTag) (r e : ℕ),
        CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t r 2 e) ∨
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
  rcases notG2_or_card360_F4 hp hp2 hcen hin hβp hβ1 ht hJ with h | h
  · obtain ⟨t, r, e, -, hM⟩ := h
    exact Or.inl ⟨t, r, e, hM⟩
  · exact Or.inr h

end CFSG.LocalAnalysis.GLTheoremA.I141F.Exc
