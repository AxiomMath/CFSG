module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorSection1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic

public section

namespace CFSG.QuasithinUnique.Setup.Layer.Actor

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Layer
open scoped Multiplicative commutatorElement

section Defs

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (θ : V ≃* Multiplicative W)

@[expose] def subOf (I : Submodule (ZMod 2) W) : Subgroup V where
  carrier := {v | Multiplicative.toAdd (θ v) ∈ I}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    show Multiplicative.toAdd (θ (a * b)) ∈ I
    rw [map_mul, toAdd_mul]
    exact I.add_mem ha hb
  inv_mem' := fun {a} ha => by
    show Multiplicative.toAdd (θ a⁻¹) ∈ I
    rw [map_inv, toAdd_inv]
    exact I.neg_mem ha

theorem mem_subOf {I : Submodule (ZMod 2) W} {v : V} :
    v ∈ subOf θ I ↔ Multiplicative.toAdd (θ v) ∈ I := Iff.rfl

theorem apply_mem_subOf {I : Submodule (ZMod 2) W} {x : MulAut V}
    (hx : ∀ u ∈ I, binPsi θ x u ∈ I) {v : V} (hv : v ∈ subOf θ I) : x v ∈ subOf θ I := by
  rw [mem_subOf, ← binPsi_toAdd]
  exact hx _ hv

@[expose] def restrictAut (I : Subgroup V) (x : MulAut V) (h : ∀ v ∈ I, x v ∈ I)
    (h' : ∀ v ∈ I, x⁻¹ v ∈ I) : MulAut ↥I where
  toFun v := ⟨x v, h v v.2⟩
  invFun v := ⟨x⁻¹ v, h' v v.2⟩
  left_inv v := Subtype.ext (by simp)
  right_inv v := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem restrictAut_coe (I : Subgroup V) (x : MulAut V) (h : ∀ v ∈ I, x v ∈ I)
    (h' : ∀ v ∈ I, x⁻¹ v ∈ I) (v : ↥I) : ((restrictAut I x h h' v : ↥I) : V) = x (v : V) := rfl

@[expose] def embSup (L A : Subgroup (MulAut V)) :
    ↥(L ⊔ A) →* ↥(L.map (binPsi θ).toMonoidHom ⊔ A.map (binPsi θ).toMonoidHom) :=
  (Subgroup.inclusion (le_of_eq (Subgroup.map_sup L A (binPsi θ).toMonoidHom))).comp
    ((binPsi θ).toMonoidHom.subgroupMap (L ⊔ A))

theorem embSup_coe (L A : Subgroup (MulAut V)) (x : ↥(L ⊔ A)) :
    ((embSup θ L A x : ↥(L.map (binPsi θ).toMonoidHom ⊔ A.map (binPsi θ).toMonoidHom)) :
      W ≃ₗ[ZMod 2] W) = binPsi θ (x : MulAut V) := rfl

end Defs

section Data

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (θ : V ≃* Multiplicative W)

@[expose] def mulSubToSub (U : Subgroup (Multiplicative W)) : Submodule (ZMod 2) W :=
  AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm U)

theorem mem_mulSubToSub {U : Subgroup (Multiplicative W)} {u : W} :
    u ∈ mulSubToSub U ↔ Multiplicative.ofAdd u ∈ U := Iff.rfl

@[expose] def tauI (L A : Subgroup (MulAut V)) {I : Submodule (ZMod 2) W}
    (hinv : ∀ x ∈ L ⊔ A, ∀ u ∈ I, binPsi θ x u ∈ I) :
    ↥(L ⊔ A) →* MulAut ↥(subOf θ I) where
  toFun x := restrictAut _ (x : MulAut V) (fun _ hv => apply_mem_subOf θ (hinv x x.2) hv)
    (fun _ hv => apply_mem_subOf θ (hinv _ ((L ⊔ A).inv_mem x.2)) hv)
  map_one' := MulEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Subtype.ext rfl

@[expose] def piMap (L' : Subgroup (W ≃ₗ[ZMod 2] W)) (I : Submodule (ZMod 2) W) :
    ↥(subOf θ I) →* Multiplicative (↥I ⧸ fixIn L' I) where
  toFun v := Multiplicative.ofAdd (Submodule.Quotient.mk ⟨Multiplicative.toAdd (θ v), v.2⟩)
  map_one' := by
    have h : (⟨Multiplicative.toAdd (θ ((1 : ↥(subOf θ I)) : V)), (1 : ↥(subOf θ I)).2⟩ : ↥I) =
        0 := Subtype.ext (by simp)
    show Multiplicative.ofAdd (Submodule.Quotient.mk _) = 1
    rw [h, Submodule.Quotient.mk_zero]
    rfl
  map_mul' a b := by
    have h : (⟨Multiplicative.toAdd (θ ((a * b : ↥(subOf θ I)) : V)), (a * b).2⟩ : ↥I) =
        ⟨Multiplicative.toAdd (θ (a : V)), a.2⟩ + ⟨Multiplicative.toAdd (θ (b : V)), b.2⟩ :=
      Subtype.ext (by simp)
    show Multiplicative.ofAdd (Submodule.Quotient.mk _) = _
    rw [h, Submodule.Quotient.mk_add]
    rfl

@[expose] noncomputable def tauW (L A : Subgroup (MulAut V)) {I : Submodule (ZMod 2) W}
    (hAn : A.map (binPsi θ).toMonoidHom ≤
      Subgroup.normalizer ((L.map (binPsi θ).toMonoidHom : Subgroup (W ≃ₗ[ZMod 2] W)) :
        Set (W ≃ₗ[ZMod 2] W)))
    (hI : Offender.IsInvariant (MonoidHom.id (W ≃ₗ[ZMod 2] W))
      (L.map (binPsi θ).toMonoidHom ⊔ A.map (binPsi θ).toMonoidHom) I) :
    ↥(L ⊔ A) →* MulAut (Multiplicative (↥I ⧸ fixIn (L.map (binPsi θ).toMonoidHom) I)) :=
  linToMulAut.comp ((actW (L.map (binPsi θ).toMonoidHom) (A.map (binPsi θ).toMonoidHom) I hAn
    hI).comp (embSup θ L A))

end Data

section Facts

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (θ : V ≃* Multiplicative W) {L A : Subgroup (MulAut V)} {I : Submodule (ZMod 2) W}

theorem range_comp_of_surjective {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]
    (f : G₂ →* G₃) (e : G₁ →* G₂) (he : Function.Surjective e) : (f.comp e).range = f.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 he]
  exact (MonoidHom.range_eq_map f).symm

theorem range_tauW_L
    (hAn : A.map (binPsi θ).toMonoidHom ≤
      Subgroup.normalizer ((L.map (binPsi θ).toMonoidHom : Subgroup (W ≃ₗ[ZMod 2] W)) :
        Set (W ≃ₗ[ZMod 2] W)))
    (hI : Offender.IsInvariant (MonoidHom.id (W ≃ₗ[ZMod 2] W))
      (L.map (binPsi θ).toMonoidHom ⊔ A.map (binPsi θ).toMonoidHom) I) :
    ((tauW θ L A hAn hI).comp (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ A))).range =
      ((actOn (L.map (binPsi θ).toMonoidHom) (A.map (binPsi θ).toMonoidHom) I hAn hI
        (L.map (binPsi θ).toMonoidHom) le_sup_left).range).map linToMulAut := by
  have h1 : (tauW θ L A hAn hI).comp (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ A)) =
      linToMulAut.comp ((actOn (L.map (binPsi θ).toMonoidHom) (A.map (binPsi θ).toMonoidHom) I
        hAn hI (L.map (binPsi θ).toMonoidHom) le_sup_left).comp
          (mapEquiv (binPsi θ) L).toMonoidHom) := MonoidHom.ext fun x => rfl
  rw [h1, MonoidHom.range_comp, range_comp_of_surjective _ _ (mapEquiv (binPsi θ) L).surjective]

theorem range_tauW_A
    (hAn : A.map (binPsi θ).toMonoidHom ≤
      Subgroup.normalizer ((L.map (binPsi θ).toMonoidHom : Subgroup (W ≃ₗ[ZMod 2] W)) :
        Set (W ≃ₗ[ZMod 2] W)))
    (hI : Offender.IsInvariant (MonoidHom.id (W ≃ₗ[ZMod 2] W))
      (L.map (binPsi θ).toMonoidHom ⊔ A.map (binPsi θ).toMonoidHom) I) :
    ((tauW θ L A hAn hI).comp (Subgroup.inclusion (le_sup_right : A ≤ L ⊔ A))).range =
      ((actOn (L.map (binPsi θ).toMonoidHom) (A.map (binPsi θ).toMonoidHom) I hAn hI
        (A.map (binPsi θ).toMonoidHom) le_sup_right).range).map linToMulAut := by
  have h1 : (tauW θ L A hAn hI).comp (Subgroup.inclusion (le_sup_right : A ≤ L ⊔ A)) =
      linToMulAut.comp ((actOn (L.map (binPsi θ).toMonoidHom) (A.map (binPsi θ).toMonoidHom) I
        hAn hI (A.map (binPsi θ).toMonoidHom) le_sup_right).comp
          (mapEquiv (binPsi θ) A).toMonoidHom) := MonoidHom.ext fun x => rfl
  rw [h1, MonoidHom.range_comp, range_comp_of_surjective _ _ (mapEquiv (binPsi θ) A).surjective]

end Facts

section Main

variable {V : Type} [CommGroup V] [Finite V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] (θ : V ≃* Multiplicative W)

theorem irrSection_of_componentSection {L A : Subgroup (MulAut V)} {I : Submodule (ZMod 2) W}
    (hcs : ComponentSection (L.map (binPsi θ).toMonoidHom) (A.map (binPsi θ).toMonoidHom) I) :
    Nonempty (X1.IrrSection V L A) := by
  classical
  have hHA : Offender.IsInvariant (MonoidHom.id (W ≃ₗ[ZMod 2] W))
      (L.map (binPsi θ).toMonoidHom ⊔ A.map (binPsi θ).toMonoidHom) I :=
    isInvariant_sup_subgroup hcs.inv_L hcs.inv_A
  have hinv : ∀ x ∈ L ⊔ A, ∀ u ∈ I, binPsi θ x u ∈ I := fun x hx u hu =>
    hHA ((embSup θ L A) ⟨x, hx⟩ : _) ((embSup θ L A) ⟨x, hx⟩).2 u hu
  have hLinv : ∀ l ∈ L, ∀ u ∈ I, binPsi θ l u ∈ I := fun l hl u hu =>
    hcs.inv_L (binPsi θ l) ⟨l, hl, rfl⟩ u hu
  refine ⟨{ I := subOf θ I
            W := Multiplicative (↥I ⧸ fixIn (L.map (binPsi θ).toMonoidHom) I)
            τI := tauI θ L A hinv
            π := piMap θ (L.map (binPsi θ).toMonoidHom) I
            τW := tauW θ L A hcs.A_norm hHA
            τI_apply := fun x v => rfl
            I_eq := ?_
            π_surjective := ?_
            π_ker := ?_
            π_equivariant := ?_
            nontrivial := ?_
            irreducible := ?_
            lbar_ne_bot := ?_
            lbar_quasisimple := ?_
            abar_ne_bot := ?_
            abar_elem := ?_
            abar_quadratic := ?_
            abar_offender := ?_
            injective_image := ?_ }⟩
  · apply le_antisymm
    · intro v hv
      have hspan : commGL (L.map (binPsi θ).toMonoidHom) I ≤
          mulSubToSub ((Subgroup.closure
            {w | ∃ l ∈ L, ∃ v ∈ subOf θ I, (l : MulAut V) v * v⁻¹ = w}).map θ.toMonoidHom) := by
        refine Submodule.span_le.2 ?_
        rintro w ⟨b, hb, u, hu, rfl⟩
        obtain ⟨l, hl, rfl⟩ := hb
        obtain ⟨v', rfl⟩ : ∃ v', Multiplicative.toAdd (θ v') = u :=
          ⟨θ.symm (Multiplicative.ofAdd u), by simp⟩
        show Multiplicative.ofAdd (binPsi θ l (Multiplicative.toAdd (θ v')) -
          Multiplicative.toAdd (θ v')) ∈ _
        rw [binPsi_sub, ofAdd_toAdd]
        exact ⟨l v' * v'⁻¹, Subgroup.subset_closure ⟨l, hl, v', hu, rfl⟩, rfl⟩
      have h1 : Multiplicative.toAdd (θ v) ∈ commGL (L.map (binPsi θ).toMonoidHom) I := by
        rw [hcs.comm]
        exact hv
      exact (mem_map_equiv_iff θ).1 (hspan h1)
    · refine (Subgroup.closure_le _).2 ?_
      rintro w ⟨l, hl, v, hv, rfl⟩
      exact (subOf θ I).mul_mem (apply_mem_subOf θ (hLinv l hl) hv) ((subOf θ I).inv_mem hv)
  ·
    intro q
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd q)
    refine ⟨⟨θ.symm (Multiplicative.ofAdd (u : W)), ?_⟩, ?_⟩
    · show Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd (u : W)))) ∈ I
      simp
    · refine Eq.trans ?_ (ofAdd_toAdd q)
      show Multiplicative.ofAdd (Submodule.Quotient.mk _) =
        Multiplicative.ofAdd (Multiplicative.toAdd q)
      rw [← hu]
      congr 2
      apply Subtype.ext
      simp
  ·
    intro v
    show Multiplicative.ofAdd (Submodule.Quotient.mk _) = Multiplicative.ofAdd 0 ↔ _
    rw [Multiplicative.ofAdd.apply_eq_iff_eq, Submodule.Quotient.mk_eq_zero, mem_fixIn]
    constructor
    · intro h l hl
      have h1 := h (binPsi θ l) ⟨l, hl, rfl⟩
      change binPsi θ l (Multiplicative.toAdd (θ (v : V))) = Multiplicative.toAdd (θ (v : V)) at h1
      rw [binPsi_toAdd] at h1
      exact θ.injective (Multiplicative.toAdd.injective h1)
    · intro h l' hl'
      obtain ⟨l, hl, rfl⟩ := hl'
      show binPsi θ l (Multiplicative.toAdd (θ (v : V))) = Multiplicative.toAdd (θ (v : V))
      rw [binPsi_toAdd, h l hl]
  ·
    intro x v
    show Multiplicative.ofAdd (Submodule.Quotient.mk _) =
      linToMulAut (actW _ _ I hcs.A_norm hHA (embSup θ L A x))
        (Multiplicative.ofAdd (Submodule.Quotient.mk _))
    rw [linToMulAut_apply, toAdd_ofAdd, actW_mk]
    congr 2
    apply Subtype.ext
    rw [resSub_apply]
    show Multiplicative.toAdd (θ ((x : MulAut V) (v : V))) =
      binPsi θ (x : MulAut V) (Multiplicative.toAdd (θ (v : V)))
    rw [binPsi_toAdd]
  ·
    have hWnt : Nontrivial (↥I ⧸ fixIn (L.map (binPsi θ).toMonoidHom) I) := by
      by_contra hcon
      have hsub : Subsingleton (↥I ⧸ fixIn (L.map (binPsi θ).toMonoidHom) I) :=
        not_nontrivial_iff_subsingleton.1 hcon
      apply hcs.irr.1
      intro u hu l hl
      have h0 : (Submodule.Quotient.mk (⟨u, hu⟩ : ↥I) :
          ↥I ⧸ fixIn (L.map (binPsi θ).toMonoidHom) I) = 0 := Subsingleton.elim _ _
      exact ((Submodule.Quotient.mk_eq_zero _).1 h0) l hl
    exact inferInstanceAs (Nontrivial (Multiplicative (↥I ⧸ fixIn (L.map (binPsi θ).toMonoidHom)
        I)))
  ·
    intro U hU
    have hirr := isIrrAct_actW hcs.A_norm hHA hcs.inv_L hcs.irr
    have h1 := hirr (mulSubToSub U) (by
      intro h hh u hu
      obtain ⟨y, hy, rfl⟩ := hh
      obtain ⟨l, hl, hly⟩ := hy
      have hxy : embSup θ L A ⟨l, Subgroup.mem_sup_left hl⟩ = y := Subtype.ext hly
      have := hU ⟨l, Subgroup.mem_sup_left hl⟩ hl (Multiplicative.ofAdd u) hu
      rw [← hxy]
      exact this)
    rcases h1 with h | h
    · left
      refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
      have h2 : Multiplicative.toAdd u ∈ mulSubToSub U := by
        rw [mem_mulSubToSub, ofAdd_toAdd]
        exact hu
      rw [h] at h2
      exact Multiplicative.toAdd.injective ((Submodule.mem_bot _).1 h2)
    · right
      refine (Subgroup.eq_top_iff' _).2 fun u => ?_
      have h2 : Multiplicative.toAdd u ∈ mulSubToSub U := by
        rw [h]
        trivial
      rw [mem_mulSubToSub, ofAdd_toAdd] at h2
      exact h2
  · rw [range_tauW_L θ hcs.A_norm hHA]
    intro h
    exact hcs.Lbar_ne ((Subgroup.map_eq_bot_iff_of_injective _ linToMulAut_injective).1 h)
  · rw [range_tauW_L θ hcs.A_norm hHA]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective _ linToMulAut linToMulAut_injective) hcs.Lbar_qs
  · rw [range_tauW_A θ hcs.A_norm hHA]
    intro h
    exact hcs.Abar_ne ((Subgroup.map_eq_bot_iff_of_injective _ linToMulAut_injective).1 h)
  · rw [range_tauW_A θ hcs.A_norm hHA]
    refine (isElemAbelian2_iff_map (MulEquiv.refl (Multiplicative _)) _).2 ?_
    rw [map_linToMulAut]
    exact hcs.Abar_elem
  · rw [range_tauW_A θ hcs.A_norm hHA]
    refine (isQuadratic_iff_map (MulEquiv.refl (Multiplicative _)) _).2 ?_
    rw [map_linToMulAut]
    exact hcs.Abar_quad
  · rw [range_tauW_A θ hcs.A_norm hHA, ← weight_map (MulEquiv.refl (Multiplicative _)),
      map_linToMulAut]
    have h1 := hcs.Abar_off
    rw [← natCard_eq (MulEquiv.refl (Multiplicative (↥I ⧸ fixIn (L.map (binPsi θ).toMonoidHom) I)))]
      at h1
    exact h1
  · intro x hx v
    have h1 : actW _ _ I hcs.A_norm hHA (embSup θ L A x) = 1 := by
      have := (linToMulAut_eq_one_iff _).1 (MulEquiv.ext hx)
      exact LinearEquiv.ext this
    have h2 := hcs.inj (embSup θ L A x) h1
    apply Subtype.ext
    have h3 := congrArg (fun f : ↥I ≃ₗ[ZMod 2] ↥I =>
      ((f ⟨Multiplicative.toAdd (θ (v : V)), v.2⟩ : ↥I) : W)) h2
    simp only [resSub_apply] at h3
    change binPsi θ (x : MulAut V) (Multiplicative.toAdd (θ (v : V))) =
      Multiplicative.toAdd (θ (v : V)) at h3
    rw [binPsi_toAdd] at h3
    exact θ.injective (Multiplicative.toAdd.injective h3)

theorem irreducibleSectionProp : X1.IrreducibleSectionProp := by
  intro V _ _ hV G L A hL hA hne
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hV
  have hinj : Function.Injective (binPsi θ).toMonoidHom := (binPsi θ).injective
  have hL' : IsComponentIn (L.map (binPsi θ).toMonoidHom) (G.map (binPsi θ).toMonoidHom) :=
    (isComponentIn_map_iff (binPsi θ)).2 ((isComp_iff L G).1 hL)
  have hA' := (isMinOffender_map_iff θ G A).2 hA
  have hne' : ⁅L.map (binPsi θ).toMonoidHom, A.map (binPsi θ).toMonoidHom⁆ ≠ ⊥ := by
    intro h
    apply hne
    apply Subgroup.map_injective hinj
    rw [map_commutator_mulEquiv, h, Subgroup.map_bot]
  obtain ⟨I, hcs⟩ := Final.component_section hL' hA'.1 hA'.2.2.1 hA'.2.1 hA'.2.2.2.1
    hA'.2.2.2.2 hne'
  refine ⟨?_, ?_, irrSection_of_componentSection θ hcs⟩
  · exact (map_le_normalizer_iff (binPsi θ)).1 hcs.A_norm
  · apply Subgroup.map_injective hinj
    rw [map_commutator_mulEquiv]
    exact hcs.L_perf

end Main

end CFSG.QuasithinUnique.Setup.Layer.Actor
