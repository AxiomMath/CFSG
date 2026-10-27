module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResAll
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocal
import CFSG.SignalizerFunctorTheorem.CatalogBridge.DicksonNonLocal
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA.MI CFSG.LocalAnalysis.GLTheoremA.FR
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def NLWitness {R : Type} [Group R] (f : MulAut R) : Prop :=
  ∃ Dc : Subgroup R, Dc ≤ fixSub f ∧ IsSimpleGroup ↥Dc ∧ (∃ x y : ↥Dc, x * y ≠ y * x) ∧
    ∀ U : Subgroup R, U ≠ ⊥ → IsPGroup 2 U → ¬ (Dc ≤ Subgroup.normalizer (U : Set R))

theorem fpFixSub_eq_fixSub {R : Type} [Group R] (f : MulAut R) : FP.fixSub f = fixSub f := by
  ext x
  exact Iff.rfl

theorem commutator_eq_self_of_simple {R : Type} [Group R] {D : Subgroup R} (hs : IsSimpleGroup ↥D)
    (hna : ∃ x y : ↥D, x * y ≠ y * x) : ⁅D, D⁆ = D := by
  have hcomm : commutator ↥D = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥D) with h0 | h0
    · exfalso
      obtain ⟨x, y, hxy⟩ := hna
      apply hxy
      have hmem : ⁅x, y⁆ ∈ commutator ↥D :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact h0
  exact (Subgroup.isPerfect_iff).1 (Group.isPerfect_def.2 hcomm)

theorem primeCoreOf_eq_bot_of_simple {p : ℕ} (hp : p.Prime) {R : Type} [Group R] [Finite R]
    {C J : Subgroup R} (hJ : GLAPComponent p C J) (hs : IsSimpleGroup ↥J) :
    GLAPPrimeCoreOf p J = ⊥ := by
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hJ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥J) with h0 | h0
  · unfold GLAPPrimeCoreOf
    rw [h0, Subgroup.map_bot]
  · exfalso
    haveI : Subsingleton (↥J ⧸ (⊤ : Subgroup ↥J)) := QuotientGroup.subsingleton_quotient_top
    haveI : Subsingleton (PQuot p J) :=
      (QuotientGroup.quotientMulEquivOfEq h0).toEquiv.subsingleton
    haveI : Subsingleton (PQuot p J ⧸ Subgroup.center (PQuot p J)) :=
      QuotientGroup.mk_surjective.subsingleton
    haveI := hq.2
    exact not_subsingleton (PQuot p J ⧸ Subgroup.center (PQuot p J)) inferInstance

theorem noLocalTwo_of_coreSub {p : ℕ} (hp : p.Prime) {R : Type} [Group R] [Finite R] {f : MulAut R}
    (hcore : CoreSub (FP.fixSub f)) (hW : NLWitness f) : NoLocalTwo p f := by
  intro J J₀ hJ hJ₀ hcov U hU hU2 hN
  obtain ⟨E, hEC, hE, -, hperf, -, -⟩ := hcore
  rw [fpFixSub_eq_fixSub] at hEC hperf
  have hJE : J = E := eq_core_of_glaPComponent (p := p) hE hEC hperf hJ
  subst hJE
  have hbot := primeCoreOf_eq_bot_of_simple hp hJ hE
  rw [hbot, sup_bot_eq] at hcov
  subst hcov
  obtain ⟨Dc, hDcC, hDcs, hDcna, hDcU⟩ := hW
  have hperfDc : ⁅Dc, Dc⁆ = Dc := commutator_eq_self_of_simple hDcs hDcna
  exact hDcU U hU hU2 ((hperf Dc hDcC hperfDc).trans hN)

theorem isSolvable_of_isPGroup_two {X : Type} [Group X] [Finite X] {U : Subgroup X}
    (hU : IsPGroup 2 U) : Group.IsSolvable ↥U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hU.isNilpotent
  infer_instance

theorem nlWitness_of_nonLocalized {R P : Type} [Group R] [Group P] [Finite P] (e : R ≃* P)
    {f : MulAut R} {D : Subgroup P} (hs : IsSimpleGroup ↥D) (hna : ∃ x y : ↥D, x * y ≠ y * x)
    (hNL : CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalized D)
    (hfix : D.map e.symm.toMonoidHom ≤ fixSub f) : NLWitness f := by
  have eD := D.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  refine ⟨D.map e.symm.toMonoidHom, hfix, (MulEquiv.isSimpleGroup_congr eD).1 hs, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hna
    exact ⟨eD x, eD y, fun h => hxy (eD.injective (by rw [map_mul, map_mul]; exact h))⟩
  · intro U hU hU2 hN
    haveI : Finite R := Finite.of_equiv _ e.symm.toEquiv
    have hU' : U.map e.toMonoidHom ≠ ⊥ := fun hbot =>
      hU ((Subgroup.map_eq_bot_iff_of_injective U e.injective).1 hbot)
    have hsolv : Group.IsSolvable ↥(U.map e.toMonoidHom) :=
      isSolvable_of_isPGroup_two (hU2.map e.toMonoidHom)
    refine hNL _ hU' hsolv ?_
    have h1 := map_le_normalizer_map e hN
    have h2 : (D.map e.symm.toMonoidHom).map e.toMonoidHom = D := by
      ext x
      simp only [Subgroup.mem_map]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
    rwa [h2] at h1

theorem not_isSolvable_of_cover {p : ℕ} (hp : p.Prime) {R : Type} [Group R] [Finite R]
    {C J J₀ : Subgroup R} (hJ : GLAPComponent p C J) (hJ₀ : J₀ ≤ J)
    (hcov : J₀ ⊔ GLAPPrimeCoreOf p J = J) : ¬ Group.IsSolvable ↥J₀ := by
  intro hsol
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hJ
  set N : Subgroup ↥J := GLAPPrimeCore p ↥J with hNdef
  let g : ↥J₀ →* PQuot p J := (QuotientGroup.mk' N).comp (Subgroup.inclusion hJ₀)
  have hsup : (J₀.subgroupOf J) ⊔ N = ⊤ := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJ₀, Subgroup.map_top,
      Subgroup.range_subtype]
    exact hcov
  have hrange : g.range = ⊤ := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    have h1 : ((J₀.subgroupOf J) ⊔ N).map (QuotientGroup.mk' N) = ⊤ := by
      rw [hsup, Subgroup.map_top, MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective N
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h1
  have hg : Function.Surjective g := MonoidHom.range_eq_top.1 hrange
  haveI := Group.isSolvable_of_surjective hg
  haveI : Group.IsPerfect (PQuot p J) := Group.isPerfect_def.2 hq.1
  haveI : Nontrivial (PQuot p J) := by
    haveI := hq.2
    by_contra h
    haveI : Subsingleton (PQuot p J) := not_nontrivial_iff_subsingleton.1 h
    haveI : Subsingleton (PQuot p J ⧸ Subgroup.center (PQuot p J)) :=
      QuotientGroup.mk_surjective.subsingleton
    exact not_subsingleton (PQuot p J ⧸ Subgroup.center (PQuot p J)) inferInstance
  exact Group.IsPerfect.not_isSolvable (PQuot p J) inferInstance

theorem noLocalTwo_of_psl2 {p : ℕ} (hp : p.Prime) {R K : Type} [Group R]
    [Finite R] [Field K] [Finite K] (e : R ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (β : MulAut R) : NoLocalTwo p β := by
  intro J J₀ hJ hJ₀ hcov U hU hU2 hN
  have hns := not_isSolvable_of_cover hp hJ hJ₀ hcov
  let C : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := J₀.map e.toMonoidHom
  have hCns : ¬ Group.IsSolvable ↥C := fun h => by
    haveI := h
    exact hns (Group.isSolvable_of_isSolvable_injective
      (f := (J₀.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
      (J₀.equivMapOfInjective e.toMonoidHom e.injective).injective)
  have hNL := CFSG.SignalizerFunctorTheorem.CatalogBridge.nonLocalized_of_not_isSolvable_psl2 C hCns
  have hU' : U.map e.toMonoidHom ≠ ⊥ := fun hbot =>
    hU ((Subgroup.map_eq_bot_iff_of_injective U e.injective).1 hbot)
  exact hNL _ hU' (isSolvable_of_isPGroup_two (hU2.map e.toMonoidHom))
    (map_le_normalizer_map e hN)

section Body

set_option linter.unusedSectionVars false


theorem coreSub_of_body {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hexc : ¬ (lab.tag = .twF4 ∧ lab.n = p)) {R : Type} [Group R]
    [Finite R] {I F : Set (MulAut R)} (hbody : SubfieldBody p lab R I F) {f : MulAut R} (hf : f ∈ F)
    (hord : orderOf f = p) (hT : ∃ T : Subgroup R, T ≤ FP.fixSub f ∧ ⁅T, T⁆ = T ∧ T ≠ ⊥) :
    CoreSub (FP.fixSub f) := by
  obtain ⟨hpn, D, hD, hdat⟩ := hbody f hf hord
  obtain ⟨T, hTC, hTp, hTne⟩ := hT
  have hTD : T ≤ D := hTp ▸ (Subgroup.commutator_mono hTC hTC).trans hD.2.1
  have hna := exists_noncomm_of_perfect hTD hTp hTne
  rcases hdat with hdat | hexc'
  · by_cases hΛ : LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩
    · have hG : lab.tag ≠ .G2der := by
        intro h
        obtain ⟨t, r, n⟩ := lab
        dsimp only at h hpn hlab
        subst h
        have : n = 1 := hlab.2.2
        rw [this] at hpn
        exact hp.one_lt.ne' (Nat.dvd_one.1 hpn)
      have hQ : ∀ (R' : Type) [Group R'] (I' F' : Set (MulAut R')), Nonempty (↥D ≃* R') →
          ∃ a b : R', a * b ≠ b * a := fun R' _ I' F' ⟨e⟩ => by
        obtain ⟨x, y, h⟩ := hna
        exact ⟨e x, e y, fun h' => h (e.injective (by rw [map_mul, map_mul]; exact h'))⟩
      obtain ⟨R', _, I', F', ⟨e'⟩, hMR⟩ :=
        Canonical.largeEvenRawDatum_exists (Canonical.largeEvenRawDatum_markedModel hΛ hQ hdat)
      obtain ⟨hs, hch⟩ := simple_chev_of_markedModel (lab := ⟨lab.tag, lab.rank, lab.n / p⟩) hG
        (MarkedModel.of_mulEquiv e'.symm hMR)
      exact coreSub_of_subfield hD (datumCore_of_simple hs hna hch)
    · rcases Res.smallDatum_holds p lab ↥D hp hlab hpn hΛ hdat with hsol | hC
      · exact (false_of_perfect_solvable hTD hTp hTne hsol).elim
      · exact coreSub_of_subfield hD hC
  · rcases hexc' with ⟨htag, hn, hsol⟩ | ⟨htag, hn⟩
    · exact (false_of_perfect_solvable hTD hTp hTne hsol).elim
    · exact absurd ⟨htag, hn⟩ hexc

@[expose] def I2015NLWitnessAt (C : LargeEvenLabel → ℕ → Prop) (lab : LargeEvenLabel) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (lab.tag = .triD4 ∧ p = 3) → ¬ (lab.tag = .twF4 ∧ lab.n = p) →
    C lab p → CAll lab (LargeEvenSimpleGuard fun R _ I F =>
      SubfieldBody p lab R I F →
      ∀ f ∈ F, orderOf f = p → Finite R → (∃ J, GLAPComponent p (fixSub f) J) → NLWitness f)

theorem false_of_component_of_solvable {p : ℕ} {R : Type} [Group R] [Finite R] {f : MulAut R}
    {D : Subgroup R}
    (hD : SubfieldGrp f D) (hsol : Group.IsSolvable ↥D) {J : Subgroup R}
    (hJ : GLAPComponent p (fixSub f) J) : False := by
  have hJ' : GLAPComponent p (FP.fixSub f) J := by rw [fpFixSub_eq_fixSub]; exact hJ
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ'
  have hJD : J ≤ D := hperf ▸ (Subgroup.commutator_mono hJ'.1 hJ'.1).trans hD.2.1
  exact false_of_perfect_solvable hJD hperf (glaPComponent_ne_bot' hJ') hsol

theorem atLabelWhen_of_witness {C : LargeEvenLabel → ℕ → Prop} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hW : I2015NLWitnessAt C lab)
    (hexc : ∀ p, C lab p → ¬ (lab.tag = .twF4 ∧ lab.n = p)) : I2015NLAtLabelWhen C lab := by
  intro p hp hp2 h3 hC
  have h1 := canonSubfield hp hp2 hlab h3
  have h2 := hW p hp hp2 h3 (hexc p hC) hC
  refine (h1.and h2).mono ?_
  rintro R _ I F ⟨hbody, hwit⟩ hs hna f hf hord hfin
  by_cases hex : ∃ J, GLAPComponent p (fixSub f) J
  · obtain ⟨J, hJ⟩ := hex
    have hJ' : GLAPComponent p (FP.fixSub f) J := by rw [fpFixSub_eq_fixSub]; exact hJ
    have hT : ∃ T : Subgroup R, T ≤ FP.fixSub f ∧ ⁅T, T⁆ = T ∧ T ≠ ⊥ :=
      ⟨J, hJ'.1, glaPComponent_perfect hJ', glaPComponent_ne_bot' hJ'⟩
    have hcore := coreSub_of_body hp hlab (hexc p hC) (hbody hs hna) hf hord hT
    exact noLocalTwo_of_coreSub hp hcore (hwit hs hna (hbody hs hna) f hf hord hfin ⟨J, hJ⟩)
  · intro J _ hJ
    exact (hex ⟨J, hJ⟩).elim

end Body

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
