module

public import CFSG.LieType.Chevalley.E6SecondGraphFixedSubgroup
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoAAutomorphisms

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SecondGraphFull

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree

section General

variable {G : Type*} [Group G] {C J : Subgroup G}

@[expose] def restrictAut (hJC : J ≤ C) (β : MulAut C)
    (hβ : ∀ g : C, (β g : G) ∈ J ↔ (g : G) ∈ J) : MulAut J where
  toFun g := ⟨β ⟨g, hJC g.2⟩, (hβ _).2 g.2⟩
  invFun g := ⟨β.symm ⟨g, hJC g.2⟩, (hβ _).1 (by rw [MulEquiv.apply_symm_apply]; exact g.2)⟩
  left_inv g := Subtype.ext (by simp)
  right_inv g := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by
    change (β (⟨g, hJC g.2⟩ * ⟨h, hJC h.2⟩) : G) = β ⟨g, hJC g.2⟩ * β ⟨h, hJC h.2⟩
    rw [map_mul, Subgroup.coe_mul])

theorem coe_restrictAut (hJC : J ≤ C) (β : MulAut C)
    (hβ : ∀ g : C, (β g : G) ∈ J ↔ (g : G) ∈ J) (g : J) :
    (restrictAut hJC β hβ g : G) = β ⟨g, hJC g.2⟩ :=
  rfl

@[expose] def restrictHom (hJC : J ≤ C) (Z : Subgroup (MulAut C))
    (hZ : ∀ β ∈ Z, ∀ g : C, (β g : G) ∈ J ↔ (g : G) ∈ J) : Z →* MulAut J :=
  MonoidHom.mk' (fun β => restrictAut hJC β (hZ β β.2)) fun _ _ =>
    MulEquiv.ext fun _ => Subtype.ext rfl

theorem coe_restrictHom (hJC : J ≤ C) (Z : Subgroup (MulAut C))
    (hZ : ∀ β ∈ Z, ∀ g : C, (β g : G) ∈ J ↔ (g : G) ∈ J) (β : Z) (g : J) :
    (restrictHom hJC Z hZ β g : G) = (β : MulAut C) ⟨g, hJC g.2⟩ :=
  rfl

@[expose] def SecondGraphFullCentralizer (C J : Subgroup G) (P t : G) {F : Type*}
    (act : F → MulAut J) : Prop :=
  ∃ (htJ : t ∈ J) (hJC : J ≤ C) (η : MulAut C), (∀ g : C, (η g : G) = P * g * P⁻¹) ∧
    (∀ β ∈ Subgroup.centralizer {MulAut.conj (⟨t, hJC htJ⟩ : C) * η}, ∀ g : C,
      (β g : G) ∈ J ↔ (g : G) ∈ J) ∧
    ∃ res : Subgroup.centralizer {MulAut.conj (⟨t, hJC htJ⟩ : C) * η} →* MulAut J,
      (∀ β (x : J), (res β x : G) = (β : MulAut C) ⟨x, hJC x.2⟩) ∧
      res.ker.map (Subgroup.centralizer {MulAut.conj (⟨t, hJC htJ⟩ : C) * η}).subtype =
        Subgroup.zpowers η ∧
      (∀ α : MulAut J, α ∈ res.range ↔
        ∃ x : J, x * ⟨t, htJ⟩ = ⟨t, htJ⟩ * x ∧ ∃ φ : F, α = MulAut.conj x * act φ) ∧
      (∀ (x x' : J) (φ φ' : F), MulAut.conj x * act φ = MulAut.conj x' * act φ' →
        x = x' ∧ φ = φ') ∧
      (∀ α ∈ res.range, α ⟨t, htJ⟩ = ⟨t, htJ⟩) ∧
      (∀ x : J, x * ⟨t, htJ⟩ = ⟨t, htJ⟩ * x →
        ∃ hx : MulAut.conj (⟨x, hJC x.2⟩ : C) ∈
          Subgroup.centralizer {MulAut.conj (⟨t, hJC htJ⟩ : C) * η},
          res ⟨_, hx⟩ = MulAut.conj x) ∧
      res '' {β | ∃ x : J, x * ⟨t, htJ⟩ = ⟨t, htJ⟩ * x ∧
          (β : MulAut C) = MulAut.conj (⟨x, hJC x.2⟩ : C)} =
        {α | ∃ x : J, x * ⟨t, htJ⟩ = ⟨t, htJ⟩ * x ∧ α = MulAut.conj x}

theorem secondGraphFullCentralizer_of {P t : G} {F : Type*} {act : F → MulAut J} (htJ : t ∈ J)
    (hJC : J ≤ C) (η : MulAut C) (hη : ∀ g : C, (η g : G) = P * g * P⁻¹)
    (hηJ : ∀ g : C, (g : G) ∈ J → η g = g) (ξ : MulAut C)
    (hξ : ξ = MulAut.conj (⟨t, hJC htJ⟩ : C) * η)
    (hdec : ∀ β ∈ Subgroup.centralizer {ξ}, ∃ x : J, x * ⟨t, htJ⟩ = ⟨t, htJ⟩ * x ∧
      ∃ φ : F, ∀ g : J, (β ⟨g, hJC g.2⟩ : G) = ((MulAut.conj x * act φ) g : J))
    (hker : ∀ β ∈ Subgroup.centralizer {ξ}, (∀ g : C, (g : G) ∈ J → β g = g) →
      β ∈ Subgroup.zpowers η)
    (hfield : ∀ φ : F, ∃ ψ ∈ Subgroup.centralizer {ξ}, ∀ g : J,
      (ψ ⟨g, hJC g.2⟩ : G) = act φ g)
    (huniq : ∀ (x x' : J) (φ φ' : F), MulAut.conj x * act φ = MulAut.conj x' * act φ' →
      x = x' ∧ φ = φ')
    (hact : ∀ φ, act φ ⟨t, htJ⟩ = ⟨t, htJ⟩) :
    SecondGraphFullCentralizer C J P t act := by
  subst hξ
  set tC : C := ⟨t, hJC htJ⟩ with htC
  set ξ := MulAut.conj tC * η with hξdef
  set Z := Subgroup.centralizer ({ξ} : Set (MulAut C)) with hZ
  have hηt : η tC = tC := hηJ tC htJ
  have hηZ : η ∈ Z := by
    rw [hZ, Subgroup.mem_centralizer_singleton_iff, hξdef, ← mul_assoc,
      E6SecondGraphFixed.mulAut_mul_conj, hηt]
  have hinner : ∀ x : J, x * ⟨t, htJ⟩ = ⟨t, htJ⟩ * x →
      MulAut.conj (⟨x, hJC x.2⟩ : C) ∈ Z := fun x hxt => by
    have hc : tC * ⟨x, hJC x.2⟩ = ⟨x, hJC x.2⟩ * tC :=
      Subtype.ext (congrArg Subtype.val hxt).symm
    have hξx : ξ ⟨x, hJC x.2⟩ = ⟨x, hJC x.2⟩ := by
      rw [hξdef, MulAut.mul_apply, hηJ _ x.2, MulAut.conj_apply, hc, mul_inv_cancel_right]
    rw [hZ, Subgroup.mem_centralizer_singleton_iff, E6SecondGraphFixed.mulAut_mul_conj ξ, hξx]
  have hpres₁ : ∀ β ∈ Z, ∀ g : C, (g : G) ∈ J → (β g : G) ∈ J := fun β hβ g hg => by
    obtain ⟨x, -, φ, hx⟩ := hdec β hβ
    have h1 : (β g : G) = ((MulAut.conj x * act φ) ⟨g, hg⟩ : J) := hx ⟨g, hg⟩
    rw [h1]
    exact Subtype.mem _
  have hpres : ∀ β ∈ Z, ∀ g : C, (β g : G) ∈ J ↔ (g : G) ∈ J := fun β hβ g =>
    ⟨fun h => by simpa using hpres₁ β⁻¹ (inv_mem hβ) (β g) h, hpres₁ β hβ g⟩
  have hres : ∀ β : Z, ∃ x : J, x * ⟨t, htJ⟩ = ⟨t, htJ⟩ * x ∧ ∃ φ : F,
      restrictHom hJC Z hpres β = MulAut.conj x * act φ := fun β => by
    obtain ⟨x, hxt, φ, hx⟩ := hdec β β.2
    exact ⟨x, hxt, φ, MulEquiv.ext fun g => Subtype.ext (hx g)⟩
  refine ⟨htJ, hJC, η, hη, hpres, restrictHom hJC Z hpres, fun β x => rfl, ?_, fun α => ?_,
    huniq, ?_, fun x hxt => ⟨hinner x hxt, MulEquiv.ext fun g => Subtype.ext rfl⟩, ?_⟩
  ·
    refine le_antisymm ?_ ?_
    · rintro _ ⟨β, hβ, rfl⟩
      refine hker β β.2 fun g hg => Subtype.ext ?_
      have h1 := congrArg (fun α : MulAut J => (α ⟨g, hg⟩ : G)) (MonoidHom.mem_ker.1 hβ)
      exact h1
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨η, hηZ⟩, MonoidHom.mem_ker.2 (MulEquiv.ext fun g => Subtype.ext ?_), rfl⟩
      have h1 := congrArg (Subtype.val : C → G) (hηJ ⟨g, hJC g.2⟩ g.2)
      exact h1
  ·
    constructor
    · rintro ⟨β, rfl⟩
      exact hres β
    · rintro ⟨x, hxt, φ, rfl⟩
      obtain ⟨ψ, hψZ, hψ⟩ := hfield φ
      refine ⟨⟨MulAut.conj (⟨x, hJC x.2⟩ : C) * ψ, mul_mem (hinner x hxt) hψZ⟩,
        MulEquiv.ext fun g => Subtype.ext ?_⟩
      change ((x : G) * (ψ ⟨g, hJC g.2⟩ : G) * (x : G)⁻¹) = _
      rw [hψ]
      rfl
  ·
    rintro α ⟨β, rfl⟩
    obtain ⟨x, hxt, φ, e⟩ := hres β
    rw [e, MulAut.mul_apply, hact, MulAut.conj_apply, hxt, mul_inv_cancel_right]
  ·
    ext α
    constructor
    · rintro ⟨β, ⟨x, hxt, hβx⟩, rfl⟩
      refine ⟨x, hxt, MulEquiv.ext fun g => Subtype.ext ?_⟩
      change ((β : MulAut C) ⟨g, hJC g.2⟩ : G) = _
      rw [hβx]
      rfl
    · rintro ⟨x, hxt, rfl⟩
      exact ⟨⟨_, hinner x hxt⟩, ⟨x, hxt, rfl⟩, MulEquiv.ext fun g => Subtype.ext rfl⟩

theorem conj_commute_of_commute {T x : G} {F β ξ : MulAut C}
    (hβ : ∀ h : C, (β h : G) = x * F h * x⁻¹) (hξ : ∀ h : C, (ξ h : G) = T * h * T⁻¹)
    (hFξ : ∀ h : C, (F (ξ h) : G) = T * F h * T⁻¹) (hcomm : ξ * β = β * ξ) (w : C) :
    (T * x)⁻¹ * (x * T) * w = w * ((T * x)⁻¹ * (x * T)) := by
  obtain ⟨h, rfl⟩ := F.surjective w
  have e := congrArg (fun γ : MulAut C => ((γ h : C) : G)) hcomm
  simp only [MulAut.mul_apply] at e
  rw [hξ, hβ, hβ, hFξ] at e
  calc (T * x)⁻¹ * (x * T) * F h
      = (T * x)⁻¹ * ((x * (T * F h * T⁻¹) * x⁻¹) * (x * T)) := by group
    _ = (T * x)⁻¹ * ((T * (x * F h * x⁻¹) * T⁻¹) * (x * T)) := by rw [e]
    _ = F h * ((T * x)⁻¹ * (x * T)) := by group

end General

section FieldAction

variable {k : Type} [Field k]

theorem map_exactEntrywiseAut_twistedFixedGroup
    (φ : k ≃+* k) :
    (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
        (exactEntrywiseAut TwistTag.E6.tag φ).toMonoidHom =
      twistedFixedGroup TwistTag.E6 k (RingHom.id k) := by
  refine le_antisymm ?_ fun g hg => ⟨(exactEntrywiseAut TwistTag.E6.tag φ).symm g, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact baseChangeGL_mem_twistedFixedGroup φ.toRingHom hg
  · exact baseChangeGL_mem_twistedFixedGroup φ.symm.toRingHom hg
  · exact (exactEntrywiseAut TwistTag.E6.tag φ).apply_symm_apply g

@[expose] def gammaFieldAut
    (φ : k ≃+* k) :
    MulAut (twistedFixedGroup TwistTag.E6 k (RingHom.id k)) :=
  mulAutRestrict _ (exactEntrywiseAut TwistTag.E6.tag φ)
    (map_exactEntrywiseAut_twistedFixedGroup φ)

theorem coe_gammaFieldAut
    (φ : k ≃+* k) (g : twistedFixedGroup TwistTag.E6 k (RingHom.id k)) :
    (gammaFieldAut φ g : ModGL TwistTag.E6.tag k) = Units.map (entrywiseHom φ.toRingHom) g :=
  rfl

variable {E : Type} [Field E]

@[expose] def gammaImageEquiv
    (ι : k →+* E) :
    twistedFixedGroup TwistTag.E6 k (RingHom.id k) ≃*
      (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL ι) :=
  Subgroup.equivMapOfInjective _ (baseChangeGL ι) (baseChangeGL_injective ι)

theorem coe_gammaImageEquiv
    (ι : k →+* E) (g : twistedFixedGroup TwistTag.E6 k (RingHom.id k)) :
    (gammaImageEquiv ι g : ModGL TwistTag.E6.tag E) = baseChangeGL ι g :=
  rfl

@[expose] def embeddedFieldAut
    (ι : k →+* E) (φ : k ≃+* k) :
    MulAut ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL ι)) :=
  MulAut.congr (gammaImageEquiv ι) (gammaFieldAut φ)

theorem coe_embeddedFieldAut
    (ι : k →+* E) (φ : k ≃+* k)
    (g : twistedFixedGroup TwistTag.E6 k (RingHom.id k))
    (x : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL ι))
    (hx : (x : ModGL TwistTag.E6.tag E) = baseChangeGL ι g) :
    (embeddedFieldAut ι φ x : ModGL TwistTag.E6.tag E) =
      baseChangeGL ι (Units.map (entrywiseHom φ.toRingHom) g) := by
  obtain rfl : gammaImageEquiv ι g = x := Subtype.ext (by rw [coe_gammaImageEquiv, hx])
  change (gammaImageEquiv ι (gammaFieldAut φ ((gammaImageEquiv ι).symm (gammaImageEquiv ι g))) :
    ModGL TwistTag.E6.tag E) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem baseChangeGL_pinnedX_one
    (ι : k →+* E) :
    baseChangeGL ι (pinnedX TwistTag.E6.tag k e6HighestRoot 1) =
      pinnedX TwistTag.E6.tag E e6HighestRoot 1 := by
  rw [baseChangeGL_pinnedX, map_one]

theorem baseChangeGL_secondGraphRep
    (ι : k →+* E) :
    baseChangeGL ι (pinnedX TwistTag.E6.tag k e6HighestRoot 1 * diagramMap TwistTag.E6 k) =
      pinnedX TwistTag.E6.tag E e6HighestRoot 1 * diagramMap TwistTag.E6 E := by
  rw [map_mul, baseChangeGL_pinnedX_one, baseChangeGL_diagramMap]

theorem embeddedFieldAut_refl
    (ι : k →+* E) : embeddedFieldAut ι (RingEquiv.refl k) = 1 := by
  have h : gammaFieldAut (RingEquiv.refl k) = 1 :=
    MulEquiv.ext fun g => Subtype.ext (Units.ext (entrywise_id _))
  rw [embeddedFieldAut, h, map_one]

theorem embeddedFieldAut_pinnedX
    (hk : ringChar k = 2) (ι : k →+* E) (φ : k ≃+* k)
    (htJ : pinnedX TwistTag.E6.tag E e6HighestRoot 1 ∈
      (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL ι)) :
    embeddedFieldAut ι φ ⟨_, htJ⟩ = ⟨_, htJ⟩ := by
  have ht := E6SecondGraphFixed.pinnedX_e6HighestRoot_mem_twistedFixedGroup hk
  refine Subtype.ext ?_
  rw [coe_embeddedFieldAut ι φ ⟨_, ht⟩ ⟨_, htJ⟩ (baseChangeGL_pinnedX_one ι).symm]
  change baseChangeGL ι (Units.map (entrywiseHom φ.toRingHom)
    (pinnedX TwistTag.E6.tag k e6HighestRoot 1)) = _
  rw [show Units.map (entrywiseHom φ.toRingHom) (pinnedX TwistTag.E6.tag k e6HighestRoot 1) =
      pinnedX TwistTag.E6.tag k e6HighestRoot 1 from
    Units.ext ((entrywise_pinnedX _ _ _).trans (by rw [map_one])), baseChangeGL_pinnedX_one]

end FieldAction

section Uniqueness

variable {f : ℕ} {k : Type} [Field k] [Finite k]

theorem F4_eq_of_conj_entrywise_eq
    (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    {y y' : adjointGroup ReeTag.F4.tag k} {φ φ' : k ≃+* k}
    (h : ∀ z : adjointGroup ReeTag.F4.tag k, (y : ModGL ReeTag.F4.tag k) *
      Units.map (entrywiseHom φ.toRingHom) (z : ModGL ReeTag.F4.tag k) *
        (y : ModGL ReeTag.F4.tag k)⁻¹ = (y' : ModGL ReeTag.F4.tag k) *
          Units.map (entrywiseHom φ'.toRingHom) (z : ModGL ReeTag.F4.tag k) *
            (y' : ModGL ReeTag.F4.tag k)⁻¹) :
    y = y' ∧ φ = φ' := by
  have : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hk
  have : CharP k ReeTag.F4.prime := this
  obtain ⟨s, hs, hφ, -⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_frobenius_pow_eq hf hk φ
  obtain ⟨s', hs', hφ', -⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_frobenius_pow_eq hf hk φ'
  have hA : ∀ (y : adjointGroup ReeTag.F4.tag k) (φ : k ≃+* k) (s : ℕ), (∀ c, φ c = c ^ 2 ^ s) →
      MulAut.conj y * ReeTag.F4.finiteExceptionalAut k ^ (2 * s) =
        MulAut.conj y * exactNormalAut ReeTag.F4.tag k 1 φ 0 := fun y φ s hφ => by
    rw [finiteExceptionalAut_pow_two_mul ReeTag.F4,
      exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.F4 hφ]
  have hQ : exactQ ReeTag.F4.tag k 0 = (1 : ModGL ReeTag.F4.tag k) := rfl
  have hB : MulAut.conj y * exactNormalAut ReeTag.F4.tag k 1 φ 0 =
      MulAut.conj y' * exactNormalAut ReeTag.F4.tag k 1 φ' 0 := by
    refine MulEquiv.ext fun z => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv, coe_exactNormalAut, coe_exactNormalAut, hQ, rootDiagUnit_one]
    simp only [one_mul, mul_one, inv_one]
    exact h z
  obtain ⟨-, huniq, -⟩ := even_F4_exact_automorphism_normal_form hf k hk
  obtain ⟨p, -, hp⟩ := huniq (MulAut.conj y * exactNormalAut ReeTag.F4.tag k 1 φ 0)
  have e1 := hp (y, ⟨2 * s, by omega⟩) (hA y φ s hφ).symm
  have e2 := hp (y', ⟨2 * s', by omega⟩) (hB.trans (hA y' φ' s' hφ').symm)
  have e := e1.trans e2.symm
  have hss : 2 * s = 2 * s' :=
    congrArg (fun p : adjointGroup ReeTag.F4.tag k × Fin (2 * f) => (p.2 : ℕ)) e
  refine ⟨congrArg Prod.fst e, RingEquiv.ext fun c => ?_⟩
  rw [hφ, hφ', show s = s' by omega]

theorem gamma_eq_of_conj_entrywise_eq
    (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    {y y' : twistedFixedGroup TwistTag.E6 k (RingHom.id k)} {φ φ' : k ≃+* k}
    (h : ∀ g : twistedFixedGroup TwistTag.E6 k (RingHom.id k), (y : ModGL TwistTag.E6.tag k) *
      Units.map (entrywiseHom φ.toRingHom) (g : ModGL TwistTag.E6.tag k) *
        (y : ModGL TwistTag.E6.tag k)⁻¹ = (y' : ModGL TwistTag.E6.tag k) *
          Units.map (entrywiseHom φ'.toRingHom) (g : ModGL TwistTag.E6.tag k) *
            (y' : ModGL TwistTag.E6.tag k)⁻¹) :
    y = y' ∧ φ = φ' := by
  have h2 : (2 : k) = 0 :=
    two_eq_zero_of_ringChar (E6SecondGraphFixed.ringChar_eq_two_of_card hf hk)
  set Ψ := e6FixedF4Equiv k h2
  have hnat : ∀ (φ : k ≃+* k) (g : twistedFixedGroup TwistTag.E6 k (RingHom.id k)),
      (Ψ (gammaFieldAut φ g) : ModGL Tag.F4 k) =
        Units.map (entrywiseHom φ.toRingHom) (Ψ g : ModGL Tag.F4 k) := fun φ g => by
    rw [coe_e6FixedF4Equiv, coe_e6FixedF4Equiv]
    exact e6FixedToF4_baseChangeGL φ.toRingHom g
  have hΓ : ∀ g, y * gammaFieldAut φ g * y⁻¹ = y' * gammaFieldAut φ' g * y'⁻¹ := fun g =>
    Subtype.ext (h g)
  have hF4 := F4_eq_of_conj_entrywise_eq hf hk (y := Ψ y) (y' := Ψ y') (φ := φ) (φ' := φ')
    fun z => by
      obtain ⟨g, rfl⟩ := Ψ.surjective z
      have e := congrArg (fun w => (Ψ w : ModGL Tag.F4 k)) (hΓ g)
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hnat] at e
      exact e
  exact ⟨Ψ.injective hF4.1, hF4.2⟩

variable {E : Type} [Field E]

theorem eq_of_conj_mul_embeddedFieldAut_eq
    (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (ι : k →+* E) {x x' : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL ι)}
    {φ φ' : k ≃+* k}
    (h : MulAut.conj x * embeddedFieldAut ι φ = MulAut.conj x' * embeddedFieldAut ι φ') :
    x = x' ∧ φ = φ' := by
  set e := gammaImageEquiv ι
  have hx : ∀ x : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL ι),
      (x : ModGL TwistTag.E6.tag E) = baseChangeGL ι (e.symm x) := fun x => by
    calc (x : ModGL TwistTag.E6.tag E) = (e (e.symm x) : ModGL TwistTag.E6.tag E) := by
          rw [e.apply_symm_apply]
      _ = baseChangeGL ι (e.symm x) := rfl
  have h' := gamma_eq_of_conj_entrywise_eq hf hk (y := e.symm x) (y' := e.symm x') (φ := φ)
    (φ' := φ') fun g => by
      have e1 := congrArg (fun α => ((α (e g) : _) : ModGL TwistTag.E6.tag E)) h
      simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at e1
      rw [coe_embeddedFieldAut ι φ g (e g) rfl, coe_embeddedFieldAut ι φ' g (e g) rfl, hx x,
        hx x', ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul] at e1
      exact baseChangeGL_injective ι e1
  refine ⟨?_, h'.2⟩
  have e2 := congrArg e h'.1
  rwa [e.apply_symm_apply, e.apply_symm_apply] at e2

end Uniqueness

theorem mem_map_of_conj_fixed
    {k L : Type} [Field k] [Finite k] [Field L] [Algebra k L]
    [IsAlgClosed L] (hk : ringChar k = 2) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card k)
    {y : ModGL TwistTag.E6.tag L} (hy : y ∈ adjointGroup TwistTag.E6.tag L)
    (hFy : Units.map (entrywiseHom Fr) y = y)
    (hζ : pinnedX TwistTag.E6.tag L e6HighestRoot 1 *
      (diagramMap TwistTag.E6 L * y * (diagramMap TwistTag.E6 L)⁻¹) *
        (pinnedX TwistTag.E6.tag L e6HighestRoot 1)⁻¹ = y) :
    y ∈ (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k L)) ∧
      pinnedX TwistTag.E6.tag L e6HighestRoot 1 * y =
        y * pinnedX TwistTag.E6.tag L e6HighestRoot 1 := by
  have hL : ringChar L = 2 := by
    have : CharP k 2 := ringChar.of_eq hk
    have : CharP L 2 := charP_of_injective_algebraMap (algebraMap k L).injective 2
    exact ringChar.eq L 2
  have hP := E6SecondGraphFixed.diagramMap_conj_eq_of_conj hL hy hζ
  refine ⟨?_, ?_⟩
  · rw [← e6_frobenius_fixed_eq_map hk Fr hFr]
    exact ⟨mem_twistedFixedGroup_id_iff.2 ⟨hy, mul_inv_eq_iff_eq_mul.1 hP⟩, hFy⟩
  · rw [hP] at hζ
    exact mul_inv_eq_iff_eq_mul.1 hζ

end CFSG.LieType.Chevalley.E6SecondGraphFull
