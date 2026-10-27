module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriLHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExcTw
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
public import CFSG.LieType.ChevTwo.OppositeFixedExcReeModel
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutReeF4
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutTriD4
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadical
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F.Tri

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.StandardType (GGInndiagCommEq ggInndiag ggInndiagComm GGInndiagCommExclLabel
  GGInndiagCommProvedLabel GGInndiagCommRestInput LargeEvenSimpleGuard)

theorem mem_innAutDerived_of_innDiagKind_of_not_derived
    {S : Type} [Group S] [Finite S] {lab : GLALabel}
    {α : MulAut S} (hcen : Subgroup.center S = ⊥)
    (hnd : lab.tag ≠ .B2der ∧ lab.tag ≠ .G2der ∧ lab.tag ≠ .twF4der)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S lab α) :
    α ∈ innAutDerived S := by
  by_cases hF : FamOrth lab
  · obtain ⟨-, a, ha⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthMark.innDiagKind_orth_data hcen hF hin
    exact inner_le_innAutDerived S ⟨a, ha⟩
  obtain ⟨-, lab', hlam, hraw⟩ := hin
  obtain ⟨_, _, _, _, -, -, -, hlab, -⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst lab'
  have hnd' : ¬ CFSG.LocalAnalysis.GLTheoremA.MI.DerivedLab lab := by
    rintro (h | h)
    · exact hnd.2.1 h
    · exact hnd.2.2 h
  have hne : ¬ GGInndiagCommExclLabel lab := by
    rintro (⟨ht, hr⟩ | h)
    · exact hF (Or.inl ⟨ht, by omega⟩)
    · exact hnd.1 h
  have hall : CFSG.StandardType.LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
    by_cases hp : GGInndiagCommProvedLabel lab
    · exact CFSG.StandardType.largeEvenLabelAll_inndiagComm_proved hlam hp
    · exact CFSG.StandardType.ggInndiagCommRestInput_holds lab hlam hne hp
  have h2 := (CFSG.LocalAnalysis.GLTheoremA.MI.canonAll_iff_legacyAll hlam hnd' _).2 hall _ hraw
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, -, u, hu, hind⟩, hEq⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists h2
  have hu' : u ∈ ggInndiagComm R := by
    rw [← hEq hs hna]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure hu)
  let e : S ≃* R := (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans θ
  have he : ∀ s, e s = θ (QuotientGroup.mk s) := fun s => by
    show θ ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm s) = _
    congr 1
    rw [MulEquiv.symm_apply_eq, CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot_mk]
  have hconj : MulAut.congr e α = u := by
    ext r
    obtain ⟨s, rfl⟩ := e.surjective r
    show e (α (e.symm (e s))) = u (e s)
    rw [MulEquiv.symm_apply_apply, he, he]
    exact (hind s (α s) rfl).symm
  rw [← mem_innAutDerived_congr e, hconj]
  exact hu'

open CFSG.LocalAnalysis.GLTheoremA.CanonTriL (NotG2LieType)

section TrialityModel

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie
  CFSG.LocalAnalysis.GLTheoremA.RationalModel
open scoped MatrixGroups

theorem notG2_trialityModel
    {q : TauCeti.PrimePower} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (q.p ^ q.exponent) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent)) (hq2 : q.p = 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    {β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hβmem : β ∈ innAutDerived ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1)
    {J : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) : NotG2LieType 2 ↥J := by
  classical
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hpq : p ≠ q.p := by rw [hq2]; exact hp2
  have hβinn : β ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range :=
    sup_le le_rfl (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outtrid4_commutator_le_range
      q.prime_p q.exponent_pos hK σ hσ) hβmem
  obtain ⟨x, rfl⟩ := hβinn
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective
  have hxp : x ^ p = 1 :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ (by rw [map_pow, hβp, map_one])
  have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  have hmon : MonomialToralAt Tag.D4 p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact monomialToralAt_three_of_block a2BlockToral_D4
    · exact monomialToralAt_of_not_dvd hp
        (CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 hp
          (by have := hp.two_le; omega))
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime q.prime_p q.exponent_pos hp hp2 hpq
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_triD4_of_prime q.prime_p q.exponent_pos hK σ hσ hp hpq hp₀ hp₀ℓ
      hq₀ hmon x hxp hx1
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne q.prime_p hp hK hpq
  have hTame := langSetup_hTame_of_prime S hp hpL (fun h => absurd h (by decide)) hT hap h1
  obtain ⟨i, hqs, hJR⟩ :=
    components_of_langSetup S hp ι hinj hrange (MulAut.conj x) hconj hT hap h1 hTame hJ
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hA := typeAShape_d4Class S hp hpL hTp h1 i
  have hAC : ringChar (AlgebraicClosure K) = 2 := by
    rw [ringChar_algebraicClosure, ← hq2]
    exact ringChar_eq_of_card_eq_pow (n := q.exponent * 3) q.prime_p
      (by have := q.exponent_pos; omega) (by rw [hK, ← pow_mul])
  have hnot : NotG2LieType (ringChar (AlgebraicClosure K))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    CFSG.LocalAnalysis.GLTheoremA.CanonTriL.notG2_rationalComponent_typeA S hp hT hap h1 i hA hqs
  rw [hAC] at hnot
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  exact hnot.of_mulEquiv eJ.symm

end TrialityModel

section ComponentTypes

open CFSG.LocalAnalysis.GLTheoremA.CanonTriL (NotG2LieType)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie
  CFSG.LocalAnalysis.GLTheoremA.RationalModel
  CFSG.LieType.Ree
open scoped MatrixGroups

theorem compType_triD4
    {S : Type} [Group S] [Finite S] {labL : GLALabel}
    {β : MulAut S} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) (ht : labL.tag = .triD4)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    (∃ (t : StatedLieTag) (r e : ℕ),
        CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t r 2 e) ∨
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
  classical
  have hnd : labL.tag ≠ .B2der ∧ labL.tag ≠ .G2der ∧ labL.tag ≠ .twF4der := by
    rw [ht]
    exact ⟨by decide, by decide, by decide⟩
  have hS : HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hβmem : β ∈ innAutDerived S :=
    mem_innAutDerived_of_innDiagKind_of_not_derived hcen hnd hin
  have hlam := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.lambda2_of_hasLabel hS
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  obtain ⟨t, r, n⟩ := labL
  simp only at ht
  subst ht
  have hn1 : 1 ≤ n := by
    rw [CFSG.Assembly.LargeEvenInLambda2] at hlam
    exact hlam.1
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .trialityD4 0 2 n := hM
  have hce := CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
  obtain ⟨-, K₀, _, _, hK₀, σ₀, hσ₀, ⟨e₀⟩⟩ := hce
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  have hq : q.card = 2 ^ n := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid := by simp
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv K₀ (by rw [hK₀, hq])
    σ₀ (fun x => by rw [hq]; exact hσ₀ x)
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  let ψ : S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans e₀).trans
      (b.trans eK)
  have hβ'mem : MulAut.congr ψ β ∈ innAutDerived _ := (mem_innAutDerived_congr ψ).2 hβmem
  have hβ'p : (MulAut.congr ψ β) ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hβ'1 : MulAut.congr ψ β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr ψ).injective (by rw [h, map_one]))
  let ψh : S →* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := ψ.toMonoidHom
  have hJ' : CFSG.Open.IsComponentOf (J.map ψh) (fixSubgroup (MulAut.congr ψ β)) :=
    CFSG.LocalAnalysis.GLTheoremA.CanonTriL.isComponentOf_transport ψ β hJ
  have hnot : NotG2LieType 2 ↥(J.map ψh) :=
    notG2_trialityModel hK σ hσ rfl hp hp2 hβ'mem hβ'p hβ'1 hJ'
  let eJ : ↥(J.map ψh) ≃* ↥J := (J.equivMapOfInjective ψh ψ.injective).symm
  obtain ⟨t, r, e, -, hm⟩ := hnot.of_mulEquiv eJ
  exact Or.inl ⟨t, r, e, hm⟩

theorem exists_lieCharTwo_of_compRelC_reeF4 {a : ℕ} (ha : 1 ≤ a) {i : TauCeti.CFSGIndex}
    (h : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compRelC (.reeF4 a) i) :
    ∃ e : TauCeti.ValidLieTypeIndex, i = .lie e ∧ e.1.characteristic = 2 := by
  have hfs : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize (.reeF4 a) = 2 ^ (2 * a + 1) :=
    rfl
  have hge : 8 ≤ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize (.reeF4 a) := by
    rw [hfs]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdvd : 2 ∣ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize (.reeF4 a) := by
    rw [hfs]
    exact dvd_pow_self 2 (by omega)
  cases i with
  | lie e =>
    have h' : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compRel (.reeF4 a) e.1 := h
    simp only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compRel] at h'
    refine ⟨e, rfl, ?_⟩
    rcases h' with ⟨hch, -⟩ | ⟨h2, -⟩ | ⟨h3, -⟩
    · simpa using hch
    · omega
    · omega
  | alternating n hn =>
    exfalso
    rcases h with ⟨-, hf⟩ | ⟨-, hf⟩ | ⟨-, hf⟩
    · rcases hf with hf | hf | hf <;> omega
    · rcases hf with hf | hf | hf <;> omega
    · omega
  | cyclic n hn => simp only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compRelC] at h
  | sporadic s => simp only [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compRelC] at h

theorem compType_twF4
    {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hin : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β) (hβp : β ^ p = 1)
    (hβ1 : β ≠ 1) (ht : labL.tag = .twF4)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    (∃ (t : StatedLieTag) (r e : ℕ),
        CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t r 2 e) ∨
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
  classical
  have hnd : labL.tag ≠ .B2der ∧ labL.tag ≠ .G2der ∧ labL.tag ≠ .twF4der := by
    rw [ht]
    exact ⟨by decide, by decide, by decide⟩
  have hS : HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hlam := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.lambda2_of_hasLabel hS
  have hβmem : β ∈ innAutDerived S :=
    mem_innAutDerived_of_innDiagKind_of_not_derived hcen hnd hin
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  obtain ⟨t, r, n⟩ := labL
  simp only [LargeEvenInLambda2] at hlam
  simp only at ht
  subst ht
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .twistedF4 0 2 n := hM
  obtain ⟨-, -, hnodd, hn3⟩ := hlam
  obtain ⟨a, rfl⟩ := hnodd
  have ha1 : 1 ≤ a := by omega
  have hR : CFSG.Blueprint.ReeTitsModel (S ⧸ Subgroup.center S) .twistedF4 2 (2 * a + 1) :=
    (hLM.reeTitsModel (by decide)).2
  obtain ⟨K, _, _, _, hK, ⟨e₁⟩⟩ :=
    CFSG.LieType.ChevTwo.Semi.exists_mulEquiv_reeGamma ha1 hR
  have hinn : innAutDerived ↥(ReeTag.F4.reeGamma K a) ≤ inner ↥(ReeTag.F4.reeGamma K a) :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.innAutDerived_le_inner_excTw_of_mulEquiv e₁
      (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outreef4_innAutDerived_le_inner hR)
  have hΓ : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.CompIdxAt p (.reeF4 a)
      ↥(ReeTag.F4.reeGamma K a) :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compIdxAt_reeGamma_F4_excTw ha1 hK hinn hp hp2
  have hSidx : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.CompIdxAt p (.reeF4 a) S :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.compIdxAt_of_mulEquiv
      ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).symm.trans e₁).symm hΓ
  obtain ⟨i, ⟨φ⟩, hrel⟩ := hSidx β hβmem hβp hβ1 J hJ
  obtain ⟨e, rfl, hchar⟩ := exists_lieCharTwo_of_compRelC_reeF4 ha1 hrel
  obtain ⟨t, n', p', f, hp', hm⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.exists_lieModel_char e
  have hp'2 : p' = 2 := hp'.trans hchar
  have hm2 : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie e).Group t n' 2 f := by
    rw [← hp'2]
    exact hm
  have hb : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie e).Group t n' 2 f :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hm2
  exact Or.inl ⟨t, n', f, CFSG.Blueprint.LieModel.of_mulEquiv φ.symm hb⟩

end ComponentTypes

end CFSG.LocalAnalysis.GLTheoremA.I141F.Tri

end
