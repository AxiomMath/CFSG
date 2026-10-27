module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZBase
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Bridge
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Proving.LBBalanceUp
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open scoped commutatorElement

@[expose] def U42Sub {Y : Type} [Group Y] (D : Subgroup Y) (G : Prop) : Prop :=
  ∀ A : Subgroup Y, GLAPComponent 3 D A → catalogIs (PSimple 3 A) S9.isU4two → G

@[expose] def U42Layer {Y : Type} [Group Y] (ψ : MulAut Y) (G : Prop) : Prop :=
  U42Sub (fixSubgroup ψ) G

theorem catalogIs_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    {Q : TauCeti.CFSGIndex → Prop} (h : catalogIs S Q) : catalogIs T Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem u42Sub_of_equiv {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    {D : Subgroup Y} {D' : Subgroup Y'} (e : ↥D ≃* ↥D') {G : Prop} (h : U42Sub D' G) :
    U42Sub D G := by
  intro A hA hT
  have h1 := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf Nat.prime_three (le_refl D) hA
  rw [Subgroup.subgroupOf_self] at h1
  have h2 := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_map_mulEquiv Nat.prime_three e h1
  rw [Subgroup.map_top_of_surjective _ e.surjective] at h2
  have h3 := CFSG.HardMathSupport.Solomon.Proving.lbUp_component_top_map Nat.prime_three D' h2
  let eA : ↥A ≃* ↥(((A.subgroupOf D).map e.toMonoidHom).map D'.subtype) :=
    (Subgroup.subgroupOfEquivOfLe hA.1).symm.trans
      ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (Subgroup.equivMapOfInjective _ D'.subtype D'.subtype_injective))
  exact h _ h3 (catalogIs_of_mulEquiv (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv 3 eA) hT)

theorem u42Layer_of_fixEquiv {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    {ψ : MulAut Y} {ψ' : MulAut Y'} (e : ↥(fixSubgroup ψ) ≃* ↥(fixSubgroup ψ')) {G : Prop}
    (h : U42Layer ψ' G) : U42Layer ψ G :=
  u42Sub_of_equiv e h

theorem u42Layer_congr {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y'] (θ : Y ≃* Y')
    {ψ : MulAut Y} {G : Prop} (h : U42Layer (MulAut.congr θ ψ) G) : U42Layer ψ G := by
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr θ ψ
  exact u42Layer_of_fixEquiv
    ((Subgroup.equivMapOfInjective _ θ.toMonoidHom θ.injective).trans
      (MulEquiv.subgroupCongr hfix.symm)) h

theorem u42Layer_conj {Y : Type} [Group Y] [Finite Y] {f : MulAut Y} {G : Prop} (γ : MulAut Y)
    (h : U42Layer f G) : U42Layer (γ * f * γ⁻¹) G := by
  refine u42Layer_congr (show Y ≃* Y from γ⁻¹) (ψ := γ * f * γ⁻¹) ?_
  have : MulAut.congr (show Y ≃* Y from γ⁻¹) (γ * f * γ⁻¹) = f := by
    ext x
    simp [MulAut.congr_apply, MulAut.mul_apply]
  rwa [this]

theorem u42Layer_of_conj {Y : Type} [Group Y] [Finite Y] {G : Prop} (γ f : MulAut Y)
    (h : U42Layer (γ * f * γ⁻¹) G) : U42Layer f G := by
  have := u42Layer_conj γ⁻¹ h
  have e : γ⁻¹ * (γ * f * γ⁻¹) * (γ⁻¹)⁻¹ = f := by group
  rwa [e] at this

theorem u42Layer_of_fix_eq {Y : Type} [Group Y] {ψ ψ' : MulAut Y} {G : Prop}
    (h : fixSubgroup ψ = fixSubgroup ψ') (hψ' : U42Layer ψ' G) : U42Layer ψ G := by
  intro A hA hT
  rw [h] at hA
  exact hψ' A hA hT

theorem fixSubgroup_inv_eq' {Y : Type} [Group Y] (ψ : MulAut Y) :
    fixSubgroup ψ⁻¹ = fixSubgroup ψ := by
  ext x
  change ψ.symm x = x ↔ ψ x = x
  rw [MulEquiv.symm_apply_eq]
  exact eq_comm

theorem u42Layer_inv_iff {Y : Type} [Group Y] (ψ : MulAut Y) (G : Prop) :
    U42Layer ψ⁻¹ G ↔ U42Layer ψ G := by
  unfold U42Layer
  rw [fixSubgroup_inv_eq']

theorem u42Layer_of_conj_pow {Y : Type} [Group Y] [Finite Y] {β η δ : MulAut Y} {r j : ℕ}
    {G : Prop} (hrj : (β ^ r) ^ j = β) (hδ : δ * β ^ r * δ⁻¹ = η) (h : U42Layer η G) :
    U42Layer β G := by
  have h1 : U42Layer (δ⁻¹ * η * δ⁻¹⁻¹) G := u42Layer_conj δ⁻¹ h
  have h2 : δ⁻¹ * η * δ⁻¹⁻¹ = β ^ r := by
    rw [← hδ]
    group
  rw [h2] at h1
  exact u42Layer_of_fix_eq
    (CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2.fixSubgroup_pow_eq_of_pow_pow_up34 hrj).symm h1

theorem glaPPrimeCore_eq_bot_of_simple {Y : Type} [Group Y] [Finite Y] {D A : Subgroup Y}
    (hA : GLAPComponent 3 D A) (hs : IsSimpleGroup ↥A) : GLAPPrimeCore 3 ↥A = ⊥ := by
  have hAq := isQuasisimple_barOf_of_glaPComponent Nat.prime_three hA
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥A) with h | h
  · exact h
  · exfalso
    have hsub : Subsingleton (barOf 3 A) := by
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b =>
          rw [QuotientGroup.eq]
          rw [h]
          exact Subgroup.mem_top _
    have hs2 : Subsingleton (barOf 3 A ⧸ Subgroup.center (barOf 3 A)) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (barOf 3 A))).subsingleton
    exact (not_nontrivial_iff_subsingleton.2 hs2) hAq.2.toNontrivial

theorem psimple_equiv_of_simple_normal_comm {Y : Type} [Group Y] [Finite Y] {D S A : Subgroup Y}
    (hSle : S ≤ D) (hcomm : ⁅D, D⁆ ≤ S) (hs : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hA : GLAPComponent 3 D A) :
    A = S ∧ Nonempty (PSimple 3 A ≃* ↥S) := by
  have hq : CFSG.Open.IsQuasisimple ↥S :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2.isQuasisimple_of_simple_up34 hnab
  have hAD : A ≤ D := hA.1
  have hAS : A ≤ S := by
    have hperf := glaPComponent_perfect hA
    calc A = ⁅A, A⁆ := hperf.symm
      _ ≤ ⁅D, D⁆ := Subgroup.commutator_mono hAD hAD
      _ ≤ S := hcomm
  have hsn : IsSubnormal A S := isSubnormal_of_le_of_le hA.2.1 hAS hSle
  have hAeq : A = S :=
    Lemma510Ns.eq_of_isSubnormal_of_quasisimple hq hsn (glaPComponent_perfect hA)
      (Lemma510Ns.glaPComponent_ne_bot hA)
  refine ⟨hAeq, ?_⟩
  subst hAeq
  have hcore : GLAPPrimeCore 3 ↥A = ⊥ := glaPPrimeCore_eq_bot_of_simple hA hs
  have hZ : Subgroup.center ↥A = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.center_eq_bot_of_simple_nonab hnab
  exact ⟨CFSG.HardMathSupport.Dickson.I271.pSimpleEquivSelf A hcore hZ⟩

theorem u42Sub_of_simple_normal_comm {Y : Type} [Group Y] [Finite Y] {D S : Subgroup Y}
    (hSle : S ≤ D) (hcomm : ⁅D, D⁆ ≤ S) (hs : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) {G : Prop} (hG : catalogIs ↥S S9.isU4two → G) :
    U42Sub D G := by
  intro A hA hT
  obtain ⟨rfl, ⟨e⟩⟩ := psimple_equiv_of_simple_normal_comm hSle hcomm hs hnab hA
  exact hG (catalogIs_of_mulEquiv e hT)

theorem u42Layer_of_simple_normal_comm {Y : Type} [Group Y] [Finite Y] (ψ : MulAut Y)
    (S : Subgroup Y) (hSle : S ≤ fixSubgroup ψ) (hcomm : ⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≤ S)
    (hs : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a) {G : Prop}
    (hG : catalogIs ↥S S9.isU4two → G) : U42Layer ψ G :=
  u42Sub_of_simple_normal_comm hSle hcomm hs hnab hG

theorem u42Layer_of_fixed_equiv {Y : Type} [Group Y] [Finite Y] (ψ : MulAut Y) {X : Type}
    [Group X] (e : ↥(fixSubgroup ψ) ≃* X) (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) {G : Prop} (hG : catalogIs X S9.isU4two → G) :
    U42Layer ψ G := by
  haveI : IsSimpleGroup ↥(fixSubgroup ψ) := e.isSimpleGroup
  refine u42Layer_of_simple_normal_comm ψ (fixSubgroup ψ) le_rfl ?_ inferInstance ?_
    fun h => hG (catalogIs_of_mulEquiv e h)
  · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩

theorem u42Layer_of_simple_commutator {Y : Type} [Group Y] [Finite Y] (ψ : MulAut Y)
    (S : Subgroup Y) (hSD : S = ⁅fixSubgroup ψ, fixSubgroup ψ⁆) (hs : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) {G : Prop} (hG : catalogIs ↥S S9.isU4two → G) :
    U42Layer ψ G := by
  refine u42Layer_of_simple_normal_comm ψ S ?_ hSD.ge hs hnab hG
  rw [hSD]
  exact Subgroup.commutator_le.2 fun a ha b hb =>
    (fixSubgroup ψ).mul_mem ((fixSubgroup ψ).mul_mem ((fixSubgroup ψ).mul_mem ha hb)
      ((fixSubgroup ψ).inv_mem ha)) ((fixSubgroup ψ).inv_mem hb)

theorem u42Sub_of_normal_simple {Y : Type} [Group Y] [Finite Y] (D J : Subgroup Y) (hJC : J ≤ D)
    [(J.subgroupOf D).Normal] (hsol : Group.IsSolvable (↥D ⧸ J.subgroupOf D))
    (hs : IsSimpleGroup ↥J) (hnab : ∃ a b : ↥J, a * b ≠ b * a) {G : Prop}
    (hG : catalogIs ↥J S9.isU4two → G) : U42Sub D G := by
  intro A hA hT
  have hq : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2.isQuasisimple_of_simple_up34 hnab
  have hAJ : A ≤ J :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_of_solvable_quotient hJC
      hsol hA.1 (glaPComponent_perfect hA)
  have hsn : IsSubnormal A J := isSubnormal_of_le_of_le hA.2.1 hAJ hJC
  have hAeq : A = J :=
    Lemma510Ns.eq_of_isSubnormal_of_quasisimple hq hsn (glaPComponent_perfect hA)
      (Lemma510Ns.glaPComponent_ne_bot hA)
  subst hAeq
  have hcore : GLAPPrimeCore 3 ↥A = ⊥ := glaPPrimeCore_eq_bot_of_simple hA hs
  have hZ : Subgroup.center ↥A = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.center_eq_bot_of_simple_nonab hnab
  exact hG (catalogIs_of_mulEquiv
    (CFSG.HardMathSupport.Dickson.I271.pSimpleEquivSelf A hcore hZ) hT)

theorem u42Layer_of_fixed_normal_simple {Y : Type} [Group Y] [Finite Y] (δ : MulAut Y)
    (N J : Subgroup Y) (hfix : fixSubgroup δ = N) (hJN : J ≤ N) [(J.subgroupOf N).Normal]
    (hsol : Group.IsSolvable (↥N ⧸ J.subgroupOf N)) (hs : IsSimpleGroup ↥J)
    (hnab : ∃ a b : ↥J, a * b ≠ b * a) {G : Prop} (hG : catalogIs ↥J S9.isU4two → G) :
    U42Layer δ G := by
  subst hfix
  exact u42Sub_of_normal_simple _ J hJN hsol hs hnab hG

theorem u42Layer_of_equiv_normal_simple {Y R : Type} [Group Y] [Finite Y] [Group R]
    (δ : MulAut Y) (e : ↥(fixSubgroup δ) ≃* R) (S : Subgroup R) [S.Normal]
    (hsol : Group.IsSolvable (R ⧸ S)) (hs : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a)
    {G : Prop} (hG : catalogIs ↥S S9.isU4two → G) : U42Layer δ G := by
  set X := fixSubgroup δ with hX
  set S' : Subgroup ↥X := S.comap e.toMonoidHom with hS'
  haveI : S'.Normal := Subgroup.normal_comap _
  set J : Subgroup Y := S'.map X.subtype with hJ
  have hJC : J ≤ X := Subgroup.map_subtype_le S'
  have hJsub : J.subgroupOf X = S' := Subgroup.comap_map_eq_self_of_injective X.subtype_injective S'
  haveI : (J.subgroupOf X).Normal := by rw [hJsub]; infer_instance
  have hsolX : Group.IsSolvable (↥X ⧸ J.subgroupOf X) := by
    refine CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.isSolvable_quotient_of_eq' hJsub.symm ?_
    let f : (↥X ⧸ S') →* (R ⧸ S) := QuotientGroup.map S' S e.toMonoidHom (fun x hx => hx)
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro x hx
      induction x using QuotientGroup.induction_on with
      | H x =>
        have : e x ∈ S := (QuotientGroup.eq_one_iff _).1 hx
        exact (QuotientGroup.eq_one_iff x).2 this
    exact Group.isSolvable_of_isSolvable_injective hf
  have hSS : S'.map e.toMonoidHom = S := Subgroup.map_comap_eq_self_of_surjective e.surjective S
  let eS' : ↥S' ≃* ↥S :=
    (Subgroup.equivMapOfInjective S' e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hSS)
  let eJ : ↥J ≃* ↥S :=
    (Subgroup.equivMapOfInjective S' X.subtype X.subtype_injective).symm.trans eS'
  haveI := hs
  refine u42Sub_of_normal_simple X J hJC hsolX eJ.isSimpleGroup ?_ fun hT =>
    hG (catalogIs_of_mulEquiv eJ hT)
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨eJ.symm a, eJ.symm b, fun h => hab (by
    have := congrArg eJ h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this)⟩

theorem u42Layer_of_fixed_commutator_equiv {Y : Type} [Group Y] [Finite Y] (ψ : MulAut Y)
    {X : Type} [Group X] (e : ↥(commutator ↥(fixSubgroup ψ)) ≃* X) (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) {G : Prop} (hG : catalogIs X S9.isU4two → G) :
    U42Layer ψ G := by
  have eS : ↥⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≃* ↥(commutator ↥(fixSubgroup ψ)) :=
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator (fixSubgroup ψ)).symm).trans
      ((commutator ↥(fixSubgroup ψ)).equivMapOfInjective (fixSubgroup ψ).subtype
        (fixSubgroup ψ).subtype_injective).symm
  let e' : ↥⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≃* X := eS.trans e
  haveI : IsSimpleGroup ↥⁅fixSubgroup ψ, fixSubgroup ψ⁆ := e'.isSimpleGroup
  refine u42Layer_of_simple_commutator ψ _ rfl inferInstance ?_ fun hT =>
    hG (catalogIs_of_mulEquiv e' hT)
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e'.symm a, e'.symm b, fun h => hab (e'.symm.injective (by simpa using h))⟩

theorem u42Sub_of_card_dvd {Y : Type} [Group Y] [Finite Y] (D : Subgroup Y) {N : ℕ}
    (hdvd : Nat.card ↥D ∣ N) (hN : ¬ 25920 ∣ N) {G : Prop} : U42Sub D G := by
  intro A hA hT
  have hc1 : Nat.card (PSimple 3 A) ∣ Nat.card (PQuot 3 A) := Subgroup.card_quotient_dvd_card _
  have hc2 : Nat.card (PQuot 3 A) ∣ Nat.card ↥A := Subgroup.card_quotient_dvd_card _
  have hc3 : Nat.card ↥A ∣ Nat.card ↥D := Subgroup.card_dvd_of_le hA.1
  rw [CFSG.LocalAnalysis.GLTheoremA.I1431Z.card_eq_of_u4two hT] at hc1
  exact absurd (hc1.trans (hc2.trans (hc3.trans hdvd))) hN

theorem u42Layer_of_card_dvd {Y : Type} [Group Y] [Finite Y] (ψ : MulAut Y) {N : ℕ}
    (hdvd : Nat.card ↥(fixSubgroup ψ) ∣ N) (hN : ¬ 25920 ∣ N) {G : Prop} : U42Layer ψ G :=
  u42Sub_of_card_dvd _ hdvd hN

theorem u42Sub_of_commutator_solvable {Y : Type} [Group Y] [Finite Y] (D S : Subgroup Y)
    (hcomm : ⁅D, D⁆ ≤ S) (hS : Group.IsSolvable ↥S) {G : Prop} : U42Sub D G := by
  intro A hA hT
  have hAD : A ≤ D := hA.1
  have hperf : ⁅A, A⁆ = A := glaPComponent_perfect hA
  have hAS : A ≤ S := by
    calc A = ⁅A, A⁆ := hperf.symm
      _ ≤ ⁅D, D⁆ := Subgroup.commutator_mono hAD hAD
      _ ≤ S := hcomm
  haveI : Group.IsSolvable ↥A :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAS)
  haveI : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hperf
  haveI : Nontrivial ↥A :=
    (Subgroup.nontrivial_iff_ne_bot A).mpr (Lemma510Ns.glaPComponent_ne_bot hA)
  exact (Group.IsPerfect.not_isSolvable ↥A inferInstance).elim

theorem u42Layer_of_solvable_fixed {Y : Type} [Group Y] [Finite Y] {ψ : MulAut Y}
    (h : Group.IsSolvable ↥(fixSubgroup ψ)) {G : Prop} : U42Layer ψ G :=
  u42Sub_of_commutator_solvable (fixSubgroup ψ) (fixSubgroup ψ)
    (Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) h

theorem U42Pumpup.apply {S : Type} [Group S] {α : MulAut S} {G : Prop} (h : U42Pumpup S α)
    (hl : U42Layer α G) : G := by
  obtain ⟨-, -, J, hJ, hT⟩ := h
  exact hl J hJ hT

theorem U42Pumpup.card_dvd {S : Type} [Group S] [Finite S] {α : MulAut S} (h : U42Pumpup S α) :
    25920 ∣ Nat.card S := by
  obtain ⟨-, -, J, -, hT⟩ := h
  rw [← CFSG.LocalAnalysis.GLTheoremA.I1431Z.card_eq_of_u4two hT]
  exact (Subgroup.card_quotient_dvd_card _).trans
    ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card J))

theorem not_mem_range_conj_of_not_mem_innAutDerived {S : Type} [Group S] {α : MulAut S}
    (hα : α ∉ innAutDerived S) : α ∉ (MulAut.conj : S →* MulAut S).range :=
  fun h => hα (CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived S h)

theorem conj_ne_of_not_mem_innAutDerived {S : Type} [Group S] {α : MulAut S}
    (hα : α ∉ innAutDerived S) (a : S) : MulAut.conj a ≠ α :=
  fun h => not_mem_range_conj_of_not_mem_innAutDerived hα ⟨a, h⟩

section TypeDet

theorem lieModel_psu_four_two_of_catalogIs {X : Type} [Group X] (hX : catalogIs X S9.isU4two) :
    Blueprint.LieModel X .PSU 4 2 1 := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := CatB.lieIndex_isU4two hX
  obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_two
    (s := 1) (by norm_num) (hq.trans (by norm_num))
  have hm := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_twistedA 3 q hv e
  rwa [h1, h2] at hm

theorem eq_of_catalogIs_u4two_lieModel {X : Type} [Group X] (hX : catalogIs X S9.isU4two)
    {t : StatedLieTag} {n f : ℕ} (hm : Blueprint.LieModel X t n 2 f) :
    t = .PSU ∧ n = 4 ∧ f = 1 :=
  CFSG.SeitzReduction.UnitaryPilot.lieModel_PSU_two_unique_of_card_eq (X := X) (m := 4) (f := 1)
    le_rfl (lieModel_psu_four_two_of_catalogIs hX) hm rfl

end TypeDet

@[expose] def U42OuterAt (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, F d.1 →
      CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex d.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, α ∉ innAutDerived S → U42Pumpup S α → S9.isU4eight (.lie d)

theorem U42OuterAt.union {F G : TauCeti.LieTypeIndex → Prop} (hF : U42OuterAt F)
    (hG : U42OuterAt G) : U42OuterAt (fun d => F d ∨ G d) :=
  fun S _ _ hs hnab d hd hc he α hα hp => by
    rcases hd with h | h
    · exact hF S hs hnab d h hc he α hα hp
    · exact hG S hs hnab d h hc he α hα hp

theorem characteristic_eq_two_iff {d : TauCeti.LieTypeIndex} :
    d.characteristic = 2 ↔ CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex d := by
  cases d <;> simp [CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex]

theorem u42Outer_of_cover {F : TauCeti.LieTypeIndex → Prop}
    (hcov : ∀ d : TauCeti.ValidLieTypeIndex,
      CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex d.1 → F d.1)
    (h : U42OuterAt F) : U42Outer :=
  fun S _ _ hs hnab d hc he α hα hp =>
    h S hs hnab d (hcov d (characteristic_eq_two_iff.mp hc)) (characteristic_eq_two_iff.mp hc) he
      α hα hp

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
