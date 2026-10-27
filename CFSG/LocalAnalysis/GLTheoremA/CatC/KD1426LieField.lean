module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieRank
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldPSU
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldGlue
public import CFSG.HardMathSupport.Solomon.Coordinator.InnDiagThreeLink
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
public import CFSG.LocalAnalysis.GLTheoremA.S4.CoverRecognition
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.GroupTheory.PLayer.Transport
public import CFSG.GroupTheory.PCore.SelfCentralizing
public import CFSG.Mathlib.Arithmetic.CubeModSix
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Struct
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.KD2027Aux
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.GLS.IVK
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

theorem catalogIs_statedProj_statedSL_three {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 6 = 1) :
    catalogIs (StatedProj (StatedSL 3 K)) (onLie k3Lie) := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : p.Prime := CharP.char_is_prime K p
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP K p := hchar
  obtain ⟨f, hpp, hKcard⟩ := FiniteField.card K p
  have hKcard' : Nat.card K = p ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hKcard
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hq6 : p ^ (f : ℕ) % 6 = 1 := by rwa [hKcard'] at hK
  have h2 : p ^ (f : ℕ) ≠ 2 := by
    intro h
    rw [h] at hq6
    norm_num at hq6
  obtain ⟨-, -, -, -, hcat⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.native_SL3_recognition p (f : ℕ) hp hf K hKcard'
  rw [if_neg h2] at hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  refine ⟨i, ?_, ⟨e⟩⟩
  cases i with
  | cyclic n hn => simp [onLie] at hi
  | alternating n hn => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie j =>
    obtain ⟨ld, hv⟩ := j
    revert hi
    cases ld with
    | A r q =>
      intro hi
      by_cases hr : r = 2
      · subst hr
        simp only [onLie] at hi
        have hq : q.card = p ^ (f : ℕ) := by simpa using hi
        have hq6' : q.card % 6 = 1 := by rw [hq]; exact hq6
        simpa [onLie, k3Lie] using hq6'
      · simp [onLie, hr] at hi
    | _ => intro hi; simp [onLie] at hi

theorem catalogIs_statedProj_statedSU_three {p f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p f K) (hq : p ^ f % 6 = 5) :
    catalogIs (StatedProj (StatedSU 3 (p ^ f) K)) (onLie k3Lie) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  let q : TauCeti.PrimePower := ⟨p, f, h.prime, by have := h.one_le; omega⟩
  have hq5 : q.card % 6 = 5 := by
    rw [TauCeti.PrimePower.card_def]
    dsimp only [q]
    exact hq
  have hK : Nat.card K = (p ^ f) ^ 2 := by
    rw [h.card]
    conv_rhs => rw [← pow_mul p f 2]
    rw [show 2 * f = f * 2 by omega]
  have hq2 : 2 < p ^ f := by omega
  obtain ⟨-, -, -, -, hcat⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.native_SU3_recognition p f h.prime h.one_le hq2 K hK
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  refine ⟨i, ?_, ⟨e⟩⟩
  cases i with
  | cyclic n hn => simp [onLie] at hi
  | alternating n hn => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie j =>
    obtain ⟨ld, hv⟩ := j
    revert hi
    cases ld with
    | twistedA r q =>
      intro hi
      by_cases hr : r = 2
      · subst hr
        simp only [onLie] at hi
        have hq6 : q.card % 6 = 5 := by rw [hi]; exact hq
        exact hq6
      · simp [onLie, hr] at hi
    | _ => intro hi; simp [onLie] at hi

theorem layer_of_field_automorphism {Y : Type} [Group Y] [Finite Y]
    (hcore : GLAPPrimeCore 3 Y = ⊥) (hZ : Subgroup.center Y = ⊥)
    {α φ γ : MulAut Y} (hαeq : α = γ * φ * γ⁻¹) (hdata : L3BFixData φ)
    {T : Subgroup Y} (hTcomm : ⁅l3bFix φ, l3bFix φ⁆ = T)
    (hTcat : catalogIs ↥T (onLie k3Lie)) :
    GLAPComponent 3 (fixSubgroup α) (GLAPLayer 3 (fixSubgroup α)) ∧
      catalogIs ↥(GLAPLayer 3 (fixSubgroup α)) (onLie k3Lie) := by
  classical
  have hdataα : L3BFixData α := by
    have hconj := L3BFixData.conj hdata γ
    rwa [← hαeq] at hconj
  let e : (Y ⧸ Subgroup.center Y) ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hψ : MulAut.congr e (centerDescend Y α) = α := by
    refine (forall_mk_eq_iff_congr_centerDescend e α α).1 fun y => ?_
    have hleft : e (QuotientGroup.mk (α y)) = α y := by
      rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
      exact QuotientGroup.kerLift_mk (φ := MonoidHom.id Y) (α y)
    have hright : e (QuotientGroup.mk y) = y := by
      rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
      exact QuotientGroup.kerLift_mk (φ := MonoidHom.id Y) y
    rw [hleft, hright]
  obtain ⟨-, L, hLle, hLq, hLmap, hLcomp, hLlay⟩ :=
    l3bf_core_layer (Y := Y) (P := Y) hcore e α hψ hdataα
  have hfixeq : Lemma53Ns.fixSub α = fixSubgroup α := rfl
  rw [hfixeq] at hLle hLcomp hLlay
  have hfker : (e.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center Y))).ker = ⊥ := by
    rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,
      QuotientGroup.ker_mk', hZ]
  have hfinj : Function.Injective
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))) :=
    (MonoidHom.ker_eq_bot_iff _).1 hfker
  have hcomm : ⁅l3bFix α, l3bFix α⁆ = T.map γ.toMonoidHom := by
    rw [hαeq, l3bFix_conj, ← Subgroup.map_commutator, hTcomm]
  have hLmap' : L.map (e.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center Y))) = T.map γ.toMonoidHom :=
    hLmap.trans hcomm
  have hcatTγ : catalogIs ↥(T.map γ.toMonoidHom) (onLie k3Lie) :=
    (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr
      (T.equivMapOfInjective γ.toMonoidHom γ.injective)).1 hTcat
  have eL : ↥L ≃* ↥(T.map γ.toMonoidHom) :=
    (L.equivMapOfInjective
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)))
      hfinj).trans (MulEquiv.subgroupCongr hLmap')
  have hcatL : catalogIs ↥L (onLie k3Lie) :=
    (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr eL).2 hcatTγ
  refine ⟨?_, ?_⟩
  · rw [hLlay]
    exact (hLcomp L).2 rfl
  · rw [hLlay]
    exact hcatL

theorem glaPComponent_fixSubgroup_of_not_mem_linearAutGroup {F : Type} [Field F] [Finite F]
    (hF : Nat.card F % 6 = 1) {α : MulAut (projectiveSL 3 F)} (hα : α ^ 3 = 1)
    (hD : α ∉ linearAutGroup 3 F) :
    GLAPComponent 3 (fixSubgroup α) (GLAPLayer 3 (fixSubgroup α)) ∧
      catalogIs ↥(GLAPLayer 3 (fixSubgroup α)) (onLie k3Lie) := by
  classical
  obtain ⟨σ, hσ3, H, hαeq⟩ :=
    linear_order_three_field_descent (n := 3) (by norm_num) α hα hD
  have hZ : Subgroup.center (projectiveSL 3 F) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 3) (k := F) (by norm_num)
  have hsimple : IsSimpleGroup (projectiveSL 3 F) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (n := 3) (K := F)
      (by norm_num)
  have h3dvd : 3 ∣ Nat.card (projectiveSL 3 F) :=
    (three_dvd_card_l3bT σ).trans (Subgroup.card_subgroup_dvd_card (l3bT σ))
  have hcore : GLAPPrimeCore 3 (projectiveSL 3 F) = ⊥ :=
    CFSG.gLAPPrimeCore_eq_bot_of_isSimpleGroup_of_dvd_card Nat.prime_three hsimple h3dvd
  have hTcat : catalogIs ↥(l3bT σ) (onLie k3Lie) := by
    have hcard3 : Nat.card (fixedField σ) ^ 3 = Nat.card F := by
      simpa [hσ3] using CFSG.GH74.GLS.IVK.fixedField_card_pow σ
    have hfixcard : Nat.card (fixedField σ) % 6 = 1 := by
      apply CFSG.mod_six_eq_one_of_pow_three
      rw [hcard3]
      exact hF
    have ePL : projectiveSL 3 (fixedField σ) ≃* ↥(l3bT σ) :=
      (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 (fixedField σ))).trans
        (l3bTEquiv σ)
    have eT : ↥(l3bT σ) ≃* StatedProj (StatedSL 3 (fixedField σ)) :=
      ePL.symm.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3
        (fixedField σ))
    exact (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr eT).2
      (catalogIs_statedProj_statedSL_three hfixcard)
  exact layer_of_field_automorphism hcore hZ hαeq (l3bf_fixData_psl σ)
    (commutator_fix_eq σ) hTcat

theorem glaPComponent_fixSubgroup_of_not_mem_psuConj_range {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : p ^ f % 6 = 5)
    {α : MulAut (unitaryPSU h 3)} (hα : α ^ 3 = 1)
    (hD : α ∉ (psuConj h).range) :
    GLAPComponent 3 (fixSubgroup α) (GLAPLayer 3 (fixSubgroup α)) ∧
      catalogIs ↥(GLAPLayer 3 (fixSubgroup α)) (onLie k3Lie) := by
  classical
  have hq2 : 2 < p ^ f := by omega
  obtain ⟨σ, hσ3, H, hαeq⟩ :=
    unitary_order_three_field_descent (h := h) hq2 α hα hD
  obtain ⟨f₀, hf, hf₀1, hkcard⟩ :=
    exists_card_fixedField_of_orderOf_eq_three h hσ3
  let h₀ : UnitaryFieldData p f₀ (fixedField σ) := ⟨h.prime, hf₀1, hkcard⟩
  have hcube : (p ^ f₀) ^ 3 = p ^ f := by
    rw [hf, show 3 * f₀ = f₀ * 3 by omega, pow_mul]
  have hq₀6 : p ^ f₀ % 6 = 5 := CFSG.mod_six_eq_five_of_pow_three (by rw [hcube]; exact hq)
  have hq₀ : p ^ f₀ ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI hfin : Finite F := h.finite
  have hZ : Subgroup.center (unitaryPSU h 3) = ⊥ :=
    center_unitaryPSU_three_eq_bot h hq2
  have hFcard : Nat.card F = (p ^ f) ^ 2 := by
    rw [h.card]
    conv_rhs => rw [← pow_mul p f 2]
    rw [show 2 * f = f * 2 by omega]
  have hnq : ((3 : ℕ), p ^ f) ≠ (3, 2) := fun h' => by
    simp only [Prod.mk.injEq, true_and] at h'
    omega
  haveI : IsSimpleGroup (StatedProj (StatedSU 3 (p ^ f) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F p f hFcard 3
      le_rfl hnq
  have hsimple : IsSimpleGroup (unitaryPSU h 3) :=
    CFSG.ABGLocalTools.isSimpleGroup_of_mulEquiv
      (unitaryPSUEquiv h (n := 3) (by norm_num))
  have h3dvd : 3 ∣ Nat.card (unitaryPSU h 3) :=
    (three_dvd_card_l3bUT h hf h₀).trans
      (Subgroup.card_subgroup_dvd_card (l3bUT h hf h₀))
  have hcore : GLAPPrimeCore 3 (unitaryPSU h 3) = ⊥ :=
    CFSG.gLAPPrimeCore_eq_bot_of_isSimpleGroup_of_dvd_card Nat.prime_three hsimple h3dvd
  have hTcat : catalogIs ↥(l3bUT h hf h₀) (onLie k3Lie) := by
    have eT : ↥(l3bUT h hf h₀) ≃*
        StatedProj (StatedSU 3 (p ^ f₀) (fixedField σ)) :=
      (l3bUTEquiv h hf h₀).symm.trans (unitaryPSUEquiv h₀ (n := 3) (by norm_num))
    exact (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr eT).2
      (catalogIs_statedProj_statedSU_three h₀ hq₀6)
  exact layer_of_field_automorphism hcore hZ hαeq (l3bf_fixData_psu h hf h₀ hq₀)
    (commutator_fix_eq_U h hf h₀ hq₀) hTcat

private theorem transport_of_model {S T : Type} [Group S] [Finite S] [Group T] [Finite T]
    (e' : S ≃* T) (A : Subgroup (MulAut S))
    {α' : MulAut T} (hα'A' : α' ∈ A.map (MulAut.congr e').toMonoidHom)
    (hα'ne : α' ≠ 1)
    (hcomp' : GLAPComponent 3 (fixSubgroup α') (GLAPLayer 3 (fixSubgroup α')))
    (hcat' : catalogIs ↥(GLAPLayer 3 (fixSubgroup α')) (onLie k3Lie)) :
    ∃ α ∈ A, α ≠ 1 ∧ GLAPComponent 3 (fixSubgroup α) (GLAPLayer 3 (fixSubgroup α)) ∧
      catalogIs ↥(GLAPLayer 3 (fixSubgroup α)) (onLie k3Lie) := by
  obtain ⟨α, hαA, hαeq⟩ := Subgroup.mem_map.1 hα'A'
  have hαne : α ≠ 1 := by
    intro hα1
    apply hα'ne
    rw [← hαeq, hα1, map_one]
  have hfs : fixSubgroup α' = (fixSubgroup α).map e'.toMonoidHom := by
    rw [← hαeq]
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e' α
  have hker : Nat.Coprime 3
      (Nat.card ↥(fixSubgroup α ⊓ e'.toMonoidHom.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e'.injective, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have hlayereq : GLAPLayer 3 (fixSubgroup α') =
      (GLAPLayer 3 (fixSubgroup α)).map e'.toMonoidHom := by
    rw [← hαeq]
    exact CFSG.glaPLayer_fixSubgroup_congr Nat.prime_three e' α
  have hcomp : GLAPComponent 3 (fixSubgroup α) (GLAPLayer 3 (fixSubgroup α)) := by
    rw [hlayereq, hfs] at hcomp'
    obtain ⟨K, hK, hKmap⟩ :=
      CFSG.LocalAnalysis.GLTheoremB.exists_glaPComponent_map_eq Nat.prime_three
        e'.toMonoidHom hker hcomp'
    have hKJ : K = GLAPLayer 3 (fixSubgroup α) :=
      Subgroup.map_injective e'.injective hKmap
    rwa [hKJ] at hK
  have hcat : catalogIs ↥(GLAPLayer 3 (fixSubgroup α)) (onLie k3Lie) := by
    let eJ : ↥(GLAPLayer 3 (fixSubgroup α')) ≃*
        ↥((GLAPLayer 3 (fixSubgroup α)).map e'.toMonoidHom) :=
      MulEquiv.subgroupCongr hlayereq
    let eJ' : ↥(GLAPLayer 3 (fixSubgroup α)) ≃*
        ↥((GLAPLayer 3 (fixSubgroup α)).map e'.toMonoidHom) :=
      (GLAPLayer 3 (fixSubgroup α)).equivMapOfInjective e'.toMonoidHom e'.injective
    exact (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr eJ').2
      ((CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr eJ).1 hcat')
  exact ⟨α, hαA, hαne, hcomp, hcat⟩

private theorem l3AutFieldFacts_of_linearModel {S : Type} [Group S] [Finite S]
    {F : Type} [Field F] [Finite F] (hF : Nat.card F % 6 = 1)
    (e : S ≃* StatedProj (StatedSL 3 F)) (A : Subgroup (MulAut S))
    (hA : IsElemAbelian 3 A) (h27 : 27 ≤ Nat.card A) :
    ∃ α ∈ A, α ≠ 1 ∧ GLAPComponent 3 (fixSubgroup α) (GLAPLayer 3 (fixSubgroup α)) ∧
      catalogIs ↥(GLAPLayer 3 (fixSubgroup α)) (onLie k3Lie) := by
  have h3 : 3 ∣ Nat.card F - 1 := by omega
  let e' : S ≃* projectiveSL 3 F :=
    e.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 F).symm
  let A' : Subgroup (MulAut (projectiveSL 3 F)) :=
    A.map (MulAut.congr e').toMonoidHom
  have hA'el : IsElemAbelian 3 A' := by
    change IsElemAbelian 3 (A.map (MulAut.congr e').toMonoidHom)
    exact hA.map (MulAut.congr e').toMonoidHom
  have hA'card : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.congr e').injective
  have hnotle : ¬ A' ≤ linearAutGroup 3 F := by
    intro hle
    have := hD9_L h3 A' hle hA'el
    omega
  obtain ⟨α', hα'A', hα'D⟩ := Set.not_subset.1 hnotle
  have hα'3 : α' ^ 3 = 1 := hA'el.2 α' hα'A'
  have hα'ne : α' ≠ 1 := by
    intro h1
    apply hα'D
    rw [h1]
    exact one_mem _
  obtain ⟨hcomp', hcat'⟩ :=
    glaPComponent_fixSubgroup_of_not_mem_linearAutGroup hF hα'3 hα'D
  exact transport_of_model e' A hα'A' hα'ne hcomp' hcat'

private theorem l3AutFieldFacts_of_unitaryModel {S : Type} [Group S] [Finite S]
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hmod : p ^ f % 6 = 5) (hcard : Nat.card K = (p ^ f) ^ 2)
    (e : S ≃* StatedProj (StatedSU 3 (p ^ f) K)) (A : Subgroup (MulAut S))
    (hA : IsElemAbelian 3 A) (h27 : 27 ≤ Nat.card A) :
    ∃ α ∈ A, α ≠ 1 ∧ GLAPComponent 3 (fixSubgroup α) (GLAPLayer 3 (fixSubgroup α)) ∧
      catalogIs ↥(GLAPLayer 3 (fixSubgroup α)) (onLie k3Lie) := by
  have hq2 : 2 < p ^ f := by omega
  have h3 : 3 ∣ p ^ f + 1 := by omega
  let hF : UnitaryFieldData p f K := unitaryFieldData_of_card hp hf hcard
  let e' : S ≃* unitaryPSU hF 3 :=
    e.trans (unitaryPSUEquiv hF (n := 3) (by norm_num)).symm
  let A' : Subgroup (MulAut (unitaryPSU hF 3)) :=
    A.map (MulAut.congr e').toMonoidHom
  have hA'el : IsElemAbelian 3 A' := by
    change IsElemAbelian 3 (A.map (MulAut.congr e').toMonoidHom)
    exact hA.map (MulAut.congr e').toMonoidHom
  have hA'card : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.congr e').injective
  have hnotle : ¬ A' ≤ (psuConj hF).range := by
    intro hle
    have := hD9_U hF h3 A' hle hA'el
    omega
  obtain ⟨α', hα'A', hα'D⟩ := Set.not_subset.1 hnotle
  have hα'3 : α' ^ 3 = 1 := hA'el.2 α' hα'A'
  have hα'ne : α' ≠ 1 := by
    intro h1
    apply hα'D
    rw [h1]
    exact one_mem _
  obtain ⟨hcomp', hcat'⟩ :=
    glaPComponent_fixSubgroup_of_not_mem_psuConj_range hF hmod hα'3 hα'D
  exact transport_of_model e' A hα'A' hα'ne hcomp' hcat'

theorem l3AutFieldFacts_holds : L3AutFieldFacts := by
  intro S _ _ hmodel A hA h27
  rcases hmodel with ⟨K, hK, hKf, hmod, ⟨e⟩⟩ | ⟨K, hK, hKf, p, f, hp, hf, hmod, hcard, ⟨e⟩⟩
  · letI : Field K := hK
    letI : Finite K := hKf
    exact l3AutFieldFacts_of_linearModel hmod e A hA h27
  · letI : Field K := hK
    letI : Finite K := hKf
    exact l3AutFieldFacts_of_unitaryModel hp hf hmod hcard e A hA h27

end CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

end
