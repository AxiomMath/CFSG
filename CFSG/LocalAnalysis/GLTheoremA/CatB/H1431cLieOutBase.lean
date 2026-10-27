module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.LocalAnalysis.GLTheoremA.I1431C2 (catalogIs_of_mulEquiv fixSubgroup_inv_eq'
  glaPPrimeCore_eq_bot_of_simple psimple_equiv_of_simple_normal_comm)
open scoped commutatorElement

@[expose] def TypeSub (T : TauCeti.CFSGIndex → Prop) {Y : Type} [Group Y] (D : Subgroup Y)
    (G : Prop) : Prop :=
  ∀ A : Subgroup Y, GLAPComponent 3 D A → catalogIs (PSimple 3 A) T → G

@[expose] def TypeLayer (T : TauCeti.CFSGIndex → Prop) {Y : Type} [Group Y] (ψ : MulAut Y)
    (G : Prop) : Prop :=
  TypeSub T (fixSubgroup ψ) G

variable {T : TauCeti.CFSGIndex → Prop}

theorem TypeSub.mono {Y : Type} [Group Y] {D : Subgroup Y} {G G' : Prop} (h : G → G')
    (hD : TypeSub T D G) : TypeSub T D G' :=
  fun A hA hT => h (hD A hA hT)

theorem TypeLayer.mono {Y : Type} [Group Y] {ψ : MulAut Y} {G G' : Prop} (h : G → G')
    (hψ : TypeLayer T ψ G) : TypeLayer T ψ G' :=
  TypeSub.mono h hψ

@[expose] def TypeOrd (T : TauCeti.CFSGIndex → Prop) (N : ℕ) : Prop :=
  ∀ {X : Type} [Group X], catalogIs X T → Nat.card X = N

theorem typeSub_of_equiv {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    {D : Subgroup Y} {D' : Subgroup Y'} (e : ↥D ≃* ↥D') {G : Prop} (h : TypeSub T D' G) :
    TypeSub T D G := by
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

theorem typeLayer_of_fixEquiv {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    {ψ : MulAut Y} {ψ' : MulAut Y'} (e : ↥(fixSubgroup ψ) ≃* ↥(fixSubgroup ψ')) {G : Prop}
    (h : TypeLayer T ψ' G) : TypeLayer T ψ G :=
  typeSub_of_equiv e h

theorem typeLayer_congr {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y'] (θ : Y ≃* Y')
    {ψ : MulAut Y} {G : Prop} (h : TypeLayer T (MulAut.congr θ ψ) G) : TypeLayer T ψ G := by
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr θ ψ
  exact typeLayer_of_fixEquiv
    ((Subgroup.equivMapOfInjective _ θ.toMonoidHom θ.injective).trans
      (MulEquiv.subgroupCongr hfix.symm)) h

theorem typeLayer_conj {Y : Type} [Group Y] [Finite Y] {f : MulAut Y} {G : Prop} (γ : MulAut Y)
    (h : TypeLayer T f G) : TypeLayer T (γ * f * γ⁻¹) G := by
  refine typeLayer_congr (show Y ≃* Y from γ⁻¹) (ψ := γ * f * γ⁻¹) ?_
  have : MulAut.congr (show Y ≃* Y from γ⁻¹) (γ * f * γ⁻¹) = f := by
    ext x
    simp [MulAut.congr_apply, MulAut.mul_apply]
  rwa [this]

theorem typeLayer_of_conj {Y : Type} [Group Y] [Finite Y] {G : Prop} (γ f : MulAut Y)
    (h : TypeLayer T (γ * f * γ⁻¹) G) : TypeLayer T f G := by
  have := typeLayer_conj γ⁻¹ h
  have e : γ⁻¹ * (γ * f * γ⁻¹) * (γ⁻¹)⁻¹ = f := by group
  rwa [e] at this

theorem typeLayer_of_fix_eq {Y : Type} [Group Y] {ψ ψ' : MulAut Y} {G : Prop}
    (h : fixSubgroup ψ = fixSubgroup ψ') (hψ' : TypeLayer T ψ' G) : TypeLayer T ψ G := by
  intro A hA hT
  rw [h] at hA
  exact hψ' A hA hT

theorem typeLayer_inv_iff {Y : Type} [Group Y] (ψ : MulAut Y) (G : Prop) :
    TypeLayer T ψ⁻¹ G ↔ TypeLayer T ψ G := by
  unfold TypeLayer
  rw [fixSubgroup_inv_eq']

theorem typeLayer_of_conj_pow {Y : Type} [Group Y] [Finite Y] {β η δ : MulAut Y} {r j : ℕ}
    {G : Prop} (hrj : (β ^ r) ^ j = β) (hδ : δ * β ^ r * δ⁻¹ = η) (h : TypeLayer T η G) :
    TypeLayer T β G := by
  have h1 : TypeLayer T (δ⁻¹ * η * δ⁻¹⁻¹) G := typeLayer_conj δ⁻¹ h
  have h2 : δ⁻¹ * η * δ⁻¹⁻¹ = β ^ r := by
    rw [← hδ]
    group
  rw [h2] at h1
  exact typeLayer_of_fix_eq
    (CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2.fixSubgroup_pow_eq_of_pow_pow_up34 hrj).symm h1

theorem typeSub_of_simple_normal_comm {Y : Type} [Group Y] [Finite Y] {D S : Subgroup Y}
    (hSle : S ≤ D) (hcomm : ⁅D, D⁆ ≤ S) (hs : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) {G : Prop} (hG : catalogIs ↥S T → G) :
    TypeSub T D G := by
  intro A hA hT
  obtain ⟨rfl, ⟨e⟩⟩ := psimple_equiv_of_simple_normal_comm hSle hcomm hs hnab hA
  exact hG (catalogIs_of_mulEquiv e hT)

theorem typeLayer_of_simple_normal_comm {Y : Type} [Group Y] [Finite Y] (ψ : MulAut Y)
    (S : Subgroup Y) (hSle : S ≤ fixSubgroup ψ) (hcomm : ⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≤ S)
    (hs : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a) {G : Prop}
    (hG : catalogIs ↥S T → G) : TypeLayer T ψ G :=
  typeSub_of_simple_normal_comm hSle hcomm hs hnab hG

theorem typeLayer_of_fixed_equiv {Y : Type} [Group Y] [Finite Y] (ψ : MulAut Y) {X : Type}
    [Group X] (e : ↥(fixSubgroup ψ) ≃* X) (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) {G : Prop} (hG : catalogIs X T → G) :
    TypeLayer T ψ G := by
  haveI : IsSimpleGroup ↥(fixSubgroup ψ) := e.isSimpleGroup
  refine typeLayer_of_simple_normal_comm ψ (fixSubgroup ψ) le_rfl ?_ inferInstance ?_
    fun h => hG (catalogIs_of_mulEquiv e h)
  · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩

theorem typeLayer_of_simple_commutator {Y : Type} [Group Y] [Finite Y] (ψ : MulAut Y)
    (S : Subgroup Y) (hSD : S = ⁅fixSubgroup ψ, fixSubgroup ψ⁆) (hs : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) {G : Prop} (hG : catalogIs ↥S T → G) :
    TypeLayer T ψ G := by
  refine typeLayer_of_simple_normal_comm ψ S ?_ hSD.ge hs hnab hG
  rw [hSD]
  exact Subgroup.commutator_le.2 fun a ha b hb =>
    (fixSubgroup ψ).mul_mem ((fixSubgroup ψ).mul_mem ((fixSubgroup ψ).mul_mem ha hb)
      ((fixSubgroup ψ).inv_mem ha)) ((fixSubgroup ψ).inv_mem hb)

theorem typeSub_of_normal_simple {Y : Type} [Group Y] [Finite Y] (D J : Subgroup Y) (hJC : J ≤ D)
    [(J.subgroupOf D).Normal] (hsol : Group.IsSolvable (↥D ⧸ J.subgroupOf D))
    (hs : IsSimpleGroup ↥J) (hnab : ∃ a b : ↥J, a * b ≠ b * a) {G : Prop}
    (hG : catalogIs ↥J T → G) : TypeSub T D G := by
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

theorem typeLayer_of_fixed_normal_simple {Y : Type} [Group Y] [Finite Y] (δ : MulAut Y)
    (N J : Subgroup Y) (hfix : fixSubgroup δ = N) (hJN : J ≤ N) [(J.subgroupOf N).Normal]
    (hsol : Group.IsSolvable (↥N ⧸ J.subgroupOf N)) (hs : IsSimpleGroup ↥J)
    (hnab : ∃ a b : ↥J, a * b ≠ b * a) {G : Prop} (hG : catalogIs ↥J T → G) :
    TypeLayer T δ G := by
  subst hfix
  exact typeSub_of_normal_simple _ J hJN hsol hs hnab hG

theorem typeLayer_of_equiv_normal_simple {Y R : Type} [Group Y] [Finite Y] [Group R]
    (δ : MulAut Y) (e : ↥(fixSubgroup δ) ≃* R) (S : Subgroup R) [S.Normal]
    (hsol : Group.IsSolvable (R ⧸ S)) (hs : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a)
    {G : Prop} (hG : catalogIs ↥S T → G) : TypeLayer T δ G := by
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
  refine typeSub_of_normal_simple X J hJC hsolX eJ.isSimpleGroup ?_ fun hT =>
    hG (catalogIs_of_mulEquiv eJ hT)
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨eJ.symm a, eJ.symm b, fun h => hab (by
    have := congrArg eJ h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this)⟩

theorem typeLayer_of_fixed_commutator_equiv {Y : Type} [Group Y] [Finite Y] (ψ : MulAut Y)
    {X : Type} [Group X] (e : ↥(commutator ↥(fixSubgroup ψ)) ≃* X) (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) {G : Prop} (hG : catalogIs X T → G) :
    TypeLayer T ψ G := by
  have eS : ↥⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≃* ↥(commutator ↥(fixSubgroup ψ)) :=
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator (fixSubgroup ψ)).symm).trans
      ((commutator ↥(fixSubgroup ψ)).equivMapOfInjective (fixSubgroup ψ).subtype
        (fixSubgroup ψ).subtype_injective).symm
  let e' : ↥⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≃* X := eS.trans e
  haveI : IsSimpleGroup ↥⁅fixSubgroup ψ, fixSubgroup ψ⁆ := e'.isSimpleGroup
  refine typeLayer_of_simple_commutator ψ _ rfl inferInstance ?_ fun hT =>
    hG (catalogIs_of_mulEquiv e' hT)
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e'.symm a, e'.symm b, fun h => hab (e'.symm.injective (by simpa using h))⟩

theorem typeSub_of_card_dvd {Y : Type} [Group Y] [Finite Y] {N : ℕ} (hT : TypeOrd T N)
    (D : Subgroup Y) {M : ℕ} (hdvd : Nat.card ↥D ∣ M) (hM : ¬ N ∣ M) {G : Prop} :
    TypeSub T D G := by
  intro A hA hTA
  have hc1 : Nat.card (PSimple 3 A) ∣ Nat.card (PQuot 3 A) := Subgroup.card_quotient_dvd_card _
  have hc2 : Nat.card (PQuot 3 A) ∣ Nat.card ↥A := Subgroup.card_quotient_dvd_card _
  have hc3 : Nat.card ↥A ∣ Nat.card ↥D := Subgroup.card_dvd_of_le hA.1
  rw [hT hTA] at hc1
  exact absurd (hc1.trans (hc2.trans (hc3.trans hdvd))) hM

theorem typeLayer_of_card_dvd {Y : Type} [Group Y] [Finite Y] {N : ℕ} (hT : TypeOrd T N)
    (ψ : MulAut Y) {M : ℕ} (hdvd : Nat.card ↥(fixSubgroup ψ) ∣ M) (hM : ¬ N ∣ M) {G : Prop} :
    TypeLayer T ψ G :=
  typeSub_of_card_dvd hT _ hdvd hM

theorem typeSub_of_commutator_solvable {Y : Type} [Group Y] [Finite Y] (D S : Subgroup Y)
    (hcomm : ⁅D, D⁆ ≤ S) (hS : Group.IsSolvable ↥S) {G : Prop} : TypeSub T D G := by
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

theorem typeLayer_of_solvable_fixed {Y : Type} [Group Y] [Finite Y] {ψ : MulAut Y}
    (h : Group.IsSolvable ↥(fixSubgroup ψ)) {G : Prop} : TypeLayer T ψ G :=
  typeSub_of_commutator_solvable (fixSubgroup ψ) (fixSubgroup ψ)
    (Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) h

@[expose] def TypePumpup (T : TauCeti.CFSGIndex → Prop) (S : Type) [Group S] (α : MulAut S) :
    Prop :=
  α ^ 3 = 1 ∧ α ≠ 1 ∧ ∃ J : Subgroup S, GLAPComponent 3 (fixSubgroup α) J ∧
    catalogIs (PSimple 3 J) T

theorem TypePumpup.apply {S : Type} [Group S] {α : MulAut S} {G : Prop} (h : TypePumpup T S α)
    (hl : TypeLayer T α G) : G := by
  obtain ⟨-, -, J, hJ, hT⟩ := h
  exact hl J hJ hT

theorem TypePumpup.card_dvd {S : Type} [Group S] [Finite S] {α : MulAut S} {N : ℕ}
    (hT : TypeOrd T N) (h : TypePumpup T S α) : N ∣ Nat.card S := by
  obtain ⟨-, -, J, -, hJ⟩ := h
  rw [← hT hJ]
  exact (Subgroup.card_quotient_dvd_card _).trans
    ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card J))

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
