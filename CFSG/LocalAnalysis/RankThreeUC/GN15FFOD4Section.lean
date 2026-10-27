module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Section

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

theorem exists_irrSection_retained {X : Type} [Group X] [Finite X]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) X W) (K A : Subgroup X)
    (hKq : CFSG.IsQuasisimple K) (hA2 : CFSG.IsElementaryAbelian 2 A)
    (hAK : A ≤ Subgroup.normalizer (K : Set X)) (hKA : ⁅K, A⁆ = K)
    (hKnt : ¬ K ≤ cenOn ρ K ⊤) (hb : IsBestOffenderOn ρ A ⊤) :
    ∃ (I : Submodule (ZMod 2) W) (W' : Type) (_ : CommGroup W') (_ : Finite W')
      (Lb Eb : Subgroup (MulAut W')) (p : I →+ Additive W') (ψ : K →* Lb),
      (∀ k ∈ K, ∀ v ∈ I, ρ k v ∈ I) ∧
      I ≤ Submodule.span (ZMod 2) {w | ∃ k ∈ K, ∃ v ∈ I, w = ρ k v - v} ∧
      Function.Surjective p ∧
      (∀ v : I, p v = 0 → ∀ k ∈ K, ρ k v = v) ∧
      (∀ (k : K) (v w : I), (w : W) = ρ k v →
        p w = Additive.ofMul ((ψ k : MulAut W') (Additive.toMul (p v)))) ∧
      Function.Surjective ψ ∧
      (∀ w : W', w * w = 1) ∧
      CFSG.QuasithinUnique.Setup.X1.IsIrrOn Lb ∧ CFSG.IsQuasisimple Lb ∧
      Eb ≠ ⊥ ∧ CFSG.Quasithin.IsElemAbelian2 Eb ∧ CFSG.Quasithin.IsQuadratic Eb ∧
      Eb ≤ Subgroup.normalizer (Lb : Set (MulAut W')) ∧
      Nat.card W' ≤ Nat.card Eb * Nat.card (CFSG.Quasithin.fixV Eb) := by
  obtain ⟨B, hBA, hinv, hKU, hBU, hBbest, hBquad, hmove, hstrict⟩ :=
    exists_strictMin_moving K A hA2 hAK hKA hKnt hb
  set U := commOn ρ K ⊤ with hUdef
  have hKH : K ≤ K ⊔ B := le_sup_left
  have hBH : B ≤ K ⊔ B := le_sup_right
  have hHn : K ⊔ B ≤ Subgroup.normalizer (K : Set X) :=
    sup_le Subgroup.le_normalizer (hBA.trans hAK)
  have hK : ∀ h ∈ K ⊔ B, ∀ k ∈ K, h * k * h⁻¹ ∈ K :=
    fun h hh k hk => (Subgroup.mem_normalizer_iff.1 (hHn hh) k).1 hk
  have hmove' : ∃ b ∈ B, ∃ k ∈ K, ∃ u ∈ U, ρ b (ρ k u) ≠ ρ k (ρ b u) := by
    have : ¬ B ≤ cenOn ρ B U := hBU
    obtain ⟨b, hb, hbn⟩ := Set.not_subset.1 this
    obtain ⟨k, hk, u, hu, h⟩ := hmove b hb hbn
    exact ⟨b, hb, k, hk, u, hu, h⟩
  have hLG := isComp_imgBin (hU := hinv) hKH hKq hKU hK
  have hAG := isBestOffender_imgBin (hU := hinv) hBH hBbest hBU hstrict
  have hne := commutator_imgBin_ne_bot (hU := hinv) hKH hBH hmove'
  obtain ⟨hAn, hLL, ⟨sec⟩⟩ := CFSG.QuasithinUnique.Setup.Layer.Actor.irreducibleSectionProp
    (Multiplicative ↥U) (binU_sq U) _ _ _ hLG hAG hne
  let f : K →* ↥(imgBin ρ (K ⊔ B) U hinv K) :=
    ((resBin ρ (K ⊔ B) U hinv).comp (Subgroup.inclusion hKH)).codRestrict _
      fun k => resBin_mem_imgBin (hU := hinv) k.2 (hKH k.2)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨b, hbK, hby⟩ := (mem_imgBin (hU := hinv)).1 hy
    refine ⟨⟨b, hbK⟩, ?_⟩
    apply Subtype.ext
    change (resBin ρ (K ⊔ B) U hinv) ⟨(b : X), hKH hbK⟩ = y
    rw [show (⟨(b : X), hKH hbK⟩ : ↥(K ⊔ B)) = b from Subtype.ext rfl]
    exact hby
  let ψ : K →* ↥((sec.τW.comp (Subgroup.inclusion le_sup_left)).range) :=
    ((sec.τW.comp (Subgroup.inclusion le_sup_left)).rangeRestrict).comp f
  have hψ : Function.Surjective ψ :=
    (MonoidHom.rangeRestrict_surjective _).comp hf
  let J : AddSubgroup ↥U := Subgroup.toAddSubgroup' sec.I
  let I : Submodule (ZMod 2) W :=
    AddSubgroup.toZModSubmodule 2 (J.map (Submodule.subtype U).toAddMonoidHom)
  have mem_I : ∀ w : W, w ∈ I ↔
      ∃ u : ↥sec.I, ((Multiplicative.toAdd (u : Multiplicative ↥U) : ↥U) : W) = w := by
    intro w
    change w ∈ AddSubgroup.toZModSubmodule 2
      (J.map (Submodule.subtype U).toAddMonoidHom) ↔ _
    rw [AddSubgroup.mem_toZModSubmodule, AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hxJ, rfl⟩
      exact ⟨⟨Multiplicative.ofAdd x, (Subgroup.mem_toAddSubgroup' sec.I x).1 hxJ⟩, by simp⟩
    · rintro ⟨u, rfl⟩
      exact ⟨Multiplicative.toAdd (u : Multiplicative ↥U),
        (Subgroup.mem_toAddSubgroup' sec.I _).2 (by simp), rfl⟩
  let toI : ↥sec.I → ↥I := fun u =>
    ⟨((Multiplicative.toAdd (u : Multiplicative ↥U) : ↥U) : W), (mem_I _).2 ⟨u, rfl⟩⟩
  have toI_inj : Function.Injective toI := by
    intro u v h
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg (fun x : ↥I => (x : W)) h
  have toI_surj : Function.Surjective toI := by
    intro v
    obtain ⟨u, hu⟩ := (mem_I (v : W)).1 v.2
    exact ⟨u, Subtype.ext hu⟩
  let toIAdd : Additive ↥sec.I →+ ↥I :=
    { toFun := fun x => toI (Additive.toMul x)
      map_zero' := by
        apply Subtype.ext
        simp [toI]
      map_add' := by
        intro x y
        apply Subtype.ext
        simp [toI, toMul_add, toAdd_mul] }
  have toIAdd_inj : Function.Injective toIAdd := by
    intro x y h
    apply Additive.toMul.injective
    exact toI_inj h
  have toIAdd_surj : Function.Surjective toIAdd := by
    intro v
    obtain ⟨u, rfl⟩ := toI_surj v
    exact ⟨Additive.ofMul u, rfl⟩
  let e : Additive ↥sec.I ≃+ ↥I := AddEquiv.ofBijective toIAdd ⟨toIAdd_inj, toIAdd_surj⟩
  let q : Additive ↥sec.I →+ Additive sec.W :=
    { toFun := fun x => Additive.ofMul (sec.π (Additive.toMul x))
      map_zero' := by simp
      map_add' := by
        intro x y
        simp [toMul_add, map_mul, ofMul_mul] }
  let p : I →+ Additive sec.W := q.comp e.symm.toAddMonoidHom
  have p_toI : ∀ u : ↥sec.I, p (toI u) = Additive.ofMul (sec.π u) := by
    intro u
    have h1 : e (Additive.ofMul u) = toI u := rfl
    have h : e.symm (toI u) = Additive.ofMul u := by
      rw [← h1, AddEquiv.symm_apply_apply]
    simp [p, q, h]
  have tauI_apply_W (k : K) (u : ↥sec.I) :
      ((Multiplicative.toAdd ((sec.τI (Subgroup.inclusion le_sup_left (f k)) u : ↥sec.I) :
        Multiplicative ↥U) : ↥U) : W)
        = ρ (k : X) (((Multiplicative.toAdd (u : Multiplicative ↥U) : ↥U) : W)) := by
    rw [sec.τI_apply]
    show ((Multiplicative.toAdd (((resBin ρ (K ⊔ B) U hinv) ⟨(k : X), hKH k.2⟩)
      (u : Multiplicative ↥U)) : ↥U) : W) = _
    exact resBin_apply_val ρ (K ⊔ B) U hinv ⟨(k : X), hKH k.2⟩
      (u : Multiplicative ↥U)
  refine ⟨I, sec.W, sec.commGroup, sec.finite,
    (sec.τW.comp (Subgroup.inclusion le_sup_left)).range,
    (sec.τW.comp (Subgroup.inclusion le_sup_right)).range, p, ψ, ?_, ?_, ?_, ?_, ?_, hψ,
    irrSection_sq (binU_sq U) sec, irrSection_isIrrOn sec, sec.lbar_quasisimple,
    sec.abar_ne_bot, sec.abar_elem, sec.abar_quadratic,
    irrSection_range_le_normalizer sec hAn, sec.abar_offender⟩
  ·
    intro k hk v hv
    obtain ⟨u, hu⟩ := toI_surj ⟨v, hv⟩
    have hval : (toI u : W) = v := congrArg Subtype.val hu
    rw [← hval]
    change ρ (k : X) (((Multiplicative.toAdd (u : Multiplicative ↥U) : ↥U) : W)) ∈ I
    rw [← tauI_apply_W ⟨k, hk⟩ u]
    exact (toI (sec.τI (Subgroup.inclusion le_sup_left (f ⟨k, hk⟩)) u)).2
  ·
    have key : ∀ u : ↥sec.I,
        ((Multiplicative.toAdd (u : Multiplicative ↥U) : ↥U) : W) ∈
          Submodule.span (ZMod 2) {w | ∃ k ∈ K, ∃ v ∈ I, w = ρ k v - v} := by
      intro u
      have hu : (u : Multiplicative ↥U) ∈ Subgroup.closure
          {w | ∃ l ∈ imgBin ρ (K ⊔ B) U hinv K, ∃ v ∈ sec.I,
            (l : MulAut (Multiplicative ↥U)) v * v⁻¹ = w} := by
        rw [← sec.I_eq]
        exact u.2
      refine Subgroup.closure_induction (p := fun x _ =>
        ((Multiplicative.toAdd x : ↥U) : W) ∈
          Submodule.span (ZMod 2) {w | ∃ k ∈ K, ∃ v ∈ I, w = ρ k v - v})
        ?_ ?_ ?_ ?_ hu
      · rintro x ⟨l, hl, v, hv, rfl⟩
        obtain ⟨k, hk⟩ := hf ⟨l, hl⟩
        have hx : ((Multiplicative.toAdd ((l : MulAut (Multiplicative ↥U)) v * v⁻¹) : ↥U) : W)
            = ρ (k : X) (((Multiplicative.toAdd v : ↥U) : W)) -
              ((Multiplicative.toAdd v : ↥U) : W) := by
          have hfk : (l : MulAut (Multiplicative ↥U)) =
              resBin ρ (K ⊔ B) U hinv ⟨(k : X), hKH k.2⟩ := by
            have hval : (f k : MulAut (Multiplicative ↥U)) = l := congrArg Subtype.val hk
            rw [← hval]
            rfl
          rw [toAdd_mul, toAdd_inv, Submodule.coe_add, Submodule.coe_neg, hfk,
            resBin_apply_val ρ (K ⊔ B) U hinv ⟨(k : X), hKH k.2⟩ v]
          abel
        rw [hx]
        exact Submodule.subset_span
          (a := ρ (k : X) (((Multiplicative.toAdd v : ↥U) : W)) -
            ((Multiplicative.toAdd v : ↥U) : W))
          ⟨k, k.2, toI ⟨v, hv⟩, (toI ⟨v, hv⟩).2, rfl⟩
      · simp
      · intro x y hx hy hpx hpy
        rw [toAdd_mul, Submodule.coe_add]
        exact Submodule.add_mem _ hpx hpy
      · intro x hx hpx
        rw [toAdd_inv, Submodule.coe_neg]
        exact Submodule.neg_mem _ hpx
    intro v hv
    obtain ⟨u, hu⟩ := toI_surj ⟨v, hv⟩
    have hval : (toI u : W) = v := congrArg Subtype.val hu
    rw [← hval]
    exact key u
  ·
    intro w
    obtain ⟨u, hu⟩ := sec.π_surjective (Additive.toMul w)
    exact ⟨toI u, by rw [p_toI, hu]; rfl⟩
  ·
    intro v hp k hk
    obtain ⟨u, rfl⟩ := toI_surj v
    have hp' : Additive.ofMul (sec.π u) = 0 := by
      rw [← p_toI u]
      exact hp
    have hπ : sec.π u = 1 := by
      have := congrArg Additive.toMul hp'
      simpa using this
    have hfix := (sec.π_ker u).1 hπ (f ⟨k, hk⟩) (f ⟨k, hk⟩).2
    have hW := congrArg (fun w : Multiplicative ↥U =>
      ((Multiplicative.toAdd w : ↥U) : W)) hfix
    change ρ (k : X) (((Multiplicative.toAdd (u : Multiplicative ↥U) : ↥U) : W))
      = ((Multiplicative.toAdd (u : Multiplicative ↥U) : ↥U) : W)
    rw [show (f ⟨k, hk⟩ : MulAut (Multiplicative ↥U)) =
        resBin ρ (K ⊔ B) U hinv ⟨(k : X), hKH hk⟩ from rfl,
      resBin_apply_val ρ (K ⊔ B) U hinv ⟨(k : X), hKH hk⟩ (u : Multiplicative ↥U)] at hW
    simpa using hW
  ·
    intro k v w hw
    obtain ⟨u, rfl⟩ := toI_surj v
    obtain ⟨u', rfl⟩ := toI_surj w
    have hψapply : ((ψ k : MulAut sec.W) (sec.π u))
        = sec.π (sec.τI (Subgroup.inclusion le_sup_left (f k)) u) := by
      rw [sec.π_equivariant]
      rfl
    have hu' : u' = sec.τI (Subgroup.inclusion le_sup_left (f k)) u := by
      apply toI_inj
      apply Subtype.ext
      rw [tauI_apply_W k u]
      exact hw
    rw [p_toI, p_toI, hu']
    show Additive.ofMul (sec.π (sec.τI (Subgroup.inclusion le_sup_left (f k)) u)) =
      Additive.ofMul (((ψ k : MulAut sec.W)) (sec.π u))
    rw [hψapply]

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
