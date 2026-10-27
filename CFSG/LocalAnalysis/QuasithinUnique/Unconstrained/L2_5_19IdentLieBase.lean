module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentOrd
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Small

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open scoped commutatorElement

section Centralizers

theorem map_centralizer_mulEquiv {X Γ : Type*} [Group X] [Group Γ] (e : X ≃* Γ) (x : X) :
    (Subgroup.centralizer ({x} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set Γ) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hz]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy

@[expose] noncomputable def centralizerEquiv {X Γ : Type*} [Group X] [Group Γ] (e : X ≃* Γ)
    (x : X) : ↥(Subgroup.centralizer ({x} : Set X)) ≃* ↥(Subgroup.centralizer ({e x} : Set Γ)) :=
  ((Subgroup.centralizer ({x} : Set X)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_centralizer_mulEquiv e x))

theorem exists_isComponent_centralizer_of_mulEquiv {X Γ : Type*} [Group X] [Group Γ]
    (e : X ≃* Γ) (x : X) {B : Subgroup ↥(Subgroup.centralizer ({x} : Set X))}
    (hB : CFSG.IsComponent B) :
    ∃ B' : Subgroup ↥(Subgroup.centralizer ({e x} : Set Γ)), CFSG.IsComponent B' :=
  ⟨B.map (centralizerEquiv e x).toMonoidHom,
    CFSG.LocalCores.isComponent_map_mulEquiv (centralizerEquiv e x) hB⟩

end Centralizers

section Inner

variable {G : Type} [Group G] {X K : Subgroup G} {t : G}

theorem IdentSetting.involution_of_inner (hs : IdentSetting X K t) (hsimple : IsSimpleGroup ↥X)
    (x : ↥X) (hx : ∀ y : ↥X, hs.conjAut y = x * y * x⁻¹) : x * x = 1 ∧ x ≠ 1 := by
  have hZ := hs.center_eq_bot_of_simple hsimple
  refine ⟨?_, ?_⟩
  · have hc : x * x ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := hs.conjAut_conjAut y
      rw [hx, hx] at h
      calc y * (x * x) = (x * (x * y * x⁻¹) * x⁻¹) * (x * x) := by rw [h]
        _ = (x * x) * y := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  · rintro rfl
    refine hs.false_of_comm_central fun y => ?_
    rw [hx]
    simp only [inv_one, one_mul, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _

theorem IdentSetting.mem_cent_iff_of_inner (hs : IdentSetting X K t) (x : ↥X)
    (hx : ∀ y : ↥X, hs.conjAut y = x * y * x⁻¹) (y : ↥X) :
    (y : G) ∈ Subgroup.centralizer ({t} : Set G) ↔
      y ∈ Subgroup.centralizer ({x} : Set ↥X) := by
  constructor
  · intro hy
    have h := hs.conjAut_of_mem_cent hy
    rw [hx] at h
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * x = (x * y * x⁻¹) * x := by rw [h]
      _ = x * y := by group
  · intro hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    have h : x * y * x⁻¹ = y := by
      calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [← hy]
        _ = y := by group
    have h2 : hs.conjAut y = y := by rw [hx, h]
    have h3 : t⁻¹ * (y : G) * t = y := by
      have := congrArg Subtype.val h2
      rwa [hs.coe_conjAut] at this
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (y : G) * t = t * (t⁻¹ * (y : G) * t) := by group
      _ = t * y := by rw [h3]

theorem IdentSetting.exists_isComponent_centralizer (hs : IdentSetting X K t) (x : ↥X)
    (hx : ∀ y : ↥X, hs.conjAut y = x * y * x⁻¹) :
    ∃ B : Subgroup ↥(Subgroup.centralizer ({x} : Set ↥X)),
      CFSG.IsComponent B ∧ Nonempty (↥B ≃* ↥K) := by
  set C : Subgroup G := X ⊓ Subgroup.centralizer ({t} : Set G) with hC
  have hCX : C ≤ X := inf_le_left
  have heq : C.subgroupOf X = Subgroup.centralizer ({x} : Set ↥X) := by
    ext y
    rw [Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf]
    exact ⟨fun h => (hs.mem_cent_iff_of_inner x hx y).mp h.2,
      fun h => ⟨y.2, (hs.mem_cent_iff_of_inner x hx y).mpr h⟩⟩
  let ε : ↥C ≃* ↥(Subgroup.centralizer ({x} : Set ↥X)) :=
    (Subgroup.subgroupOfEquivOfLe hCX).symm.trans (MulEquiv.subgroupCongr heq)
  refine ⟨(K.subgroupOf C).map ε.toMonoidHom,
    CFSG.LocalCores.isComponent_map_mulEquiv ε hs.comp.2, ⟨?_⟩⟩
  exact (((K.subgroupOf C).equivMapOfInjective ε.toMonoidHom ε.injective).symm).trans
    (Subgroup.subgroupOfEquivOfLe hs.comp.1)

theorem IdentSetting.false_of_inner (hs : IdentSetting X K t) (hsimple : IsSimpleGroup ↥X)
    {Γ : Type*} [Group Γ] (e : ↥X ≃* Γ)
    (hfree : ∀ y : Γ, orderOf y = 2 →
      ∀ B : Subgroup ↥(Subgroup.centralizer ({y} : Set Γ)), ¬ CFSG.IsComponent B)
    (x : ↥X) (hx : ∀ y : ↥X, hs.conjAut y = x * y * x⁻¹) : False := by
  obtain ⟨hxx, hx1⟩ := hs.involution_of_inner hsimple x hx
  obtain ⟨B, hB, -⟩ := hs.exists_isComponent_centralizer x hx
  obtain ⟨B', hB'⟩ := exists_isComponent_centralizer_of_mulEquiv e x hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (e x) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, hxx, map_one]
    · intro h
      exact hx1 (e.injective (by rw [h, map_one]))
  exact hfree (e x) hord B' hB'

end Inner

section Socle

open CFSG.ComponentClassification.OuterAutomorphisms

theorem conj_injective_of_center_bot {H : Type*} [Group H] (hZ : Subgroup.center H = ⊥) :
    Function.Injective (MulAut.conj : H →* MulAut H) := by
  intro g g' h
  have hc : g'⁻¹ * g ∈ Subgroup.center H := Subgroup.mem_center_iff.2 fun x => by
    have hx := congrArg (fun φ : MulAut H => φ x) h
    simp only [MulAut.conj_apply] at hx
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
      _ = g'⁻¹ * g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem centralizer_inner_eq_bot_of_center_bot {H : Type*} [Group H]
    (hZ : Subgroup.center H = ⊥) :
    Subgroup.centralizer ((inner H : Subgroup (MulAut H)) : Set (MulAut H)) = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_centralizer_iff] at hφ
  rw [Subgroup.mem_bot]
  ext v
  have h1 : MulAut.conj (φ v) = MulAut.conj v := by
    ext w
    have h2 := congrArg (fun ψ : MulAut H => ψ (φ.symm w)) (hφ (MulAut.conj v) ⟨v, rfl⟩)
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at h2
    simpa [MulAut.conj_apply] using h2.symm
  simpa using conj_injective_of_center_bot hZ h1

noncomputable def innerEquiv {H : Type*} [Group H] (hZ : Subgroup.center H = ⊥) :
    H ≃* ↥(inner H) :=
  MonoidHom.ofInjective (f := (MulAut.conj : H →* MulAut H)) (conj_injective_of_center_bot hZ)

theorem isSimpleGroup_inner {H : Type*} [Group H] [IsSimpleGroup H]
    (hZ : Subgroup.center H = ⊥) : IsSimpleGroup ↥(inner H) :=
  (innerEquiv hZ).symm.isSimpleGroup

end Socle

section SocleData

open CFSG.ComponentClassification.OuterAutomorphisms

theorem assemblySubnormal_of_normal {A : Type*} [Group A] {L N C : Subgroup A}
    (hLN : CFSG.Assembly.IsSubnormal L N) (hNC : N ≤ C) (hn : (N.subgroupOf C).Normal) :
    CFSG.Assembly.IsSubnormal L C :=
  hLN.trans (.step hNC hn (.refl C))

variable {G : Type} [Group G] {X K : Subgroup G} {t : G}

theorem IdentSetting.isComponentOf_map (hs : IdentSetting X K t) {A : Type*} [Group A]
    (ι : ↥X →* A) (hι : Function.Injective ι) :
    CFSG.Assembly.IsComponentOf ((K.subgroupOf X).map ι)
      (((X ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf X).map ι) := by
  set C : Subgroup G := X ⊓ Subgroup.centralizer ({t} : Set G) with hC
  have hCX : C ≤ X := inf_le_left
  have hKC : K ≤ C := hs.comp.1
  have hLN : (K.subgroupOf X).map ι ≤ (C.subgroupOf X).map ι :=
    Subgroup.map_mono (fun y hy => hKC hy)
  rw [CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLN]
  let ε : ↥C ≃* ↥((C.subgroupOf X).map ι) :=
    (Subgroup.subgroupOfEquivOfLe hCX).symm.trans ((C.subgroupOf X).equivMapOfInjective ι hι)
  have hε : ∀ c : ↥C, ((ε c : ↥((C.subgroupOf X).map ι)) : A) = ι ⟨(c : G), hCX c.2⟩ := fun c => rfl
  have key : (K.subgroupOf C).map ε.toMonoidHom =
      ((K.subgroupOf X).map ι).subgroupOf ((C.subgroupOf X).map ι) := by
    ext n
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨(c : G), hCX c.2⟩, hc, (hε c).symm⟩
    · rintro ⟨y, hy, hyn⟩
      obtain ⟨c, rfl⟩ := ε.surjective n
      refine ⟨c, ?_, rfl⟩
      have h1 : ι ⟨(c : G), hCX c.2⟩ = ι y := by rw [← hε c, hyn]
      have h2 : (⟨(c : G), hCX c.2⟩ : ↥X) = y := hι h1
      show (c : G) ∈ K
      have : (y : G) ∈ K := hy
      rw [← h2] at this
      exact this
  rw [← key]
  exact CFSG.LocalCores.isComponent_map_mulEquiv ε hs.comp.2

theorem IdentSetting.orderOf_conjAut (hs : IdentSetting X K t) :
    orderOf (hs.conjAut : MulAut ↥X) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two]
    refine MulEquiv.ext fun y => ?_
    rw [MulAut.mul_apply, MulAut.one_apply]
    exact hs.conjAut_conjAut y
  · intro h
    refine hs.false_of_comm_central fun y => ?_
    have : (hs.conjAut : MulAut ↥X) y = y := by rw [h]; rfl
    rw [this, mul_inv_cancel]
    exact Subgroup.one_mem _

theorem IdentSetting.map_conj_eq_inner_inf_centralizer (hs : IdentSetting X K t)
    (hsimple : IsSimpleGroup ↥X) :
    ((X ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf X).map
        (MulAut.conj : ↥X →* MulAut ↥X) =
      inner ↥X ⊓ Subgroup.centralizer ({(hs.conjAut : MulAut ↥X)} : Set (MulAut ↥X)) := by
  have hZ := hs.center_eq_bot_of_simple hsimple
  have hι := conj_injective_of_center_bot hZ
  set a : MulAut ↥X := hs.conjAut with ha
  set C : Subgroup G := X ⊓ Subgroup.centralizer ({t} : Set G) with hC
  have hconj : ∀ y : ↥X, a * MulAut.conj y * a⁻¹ = MulAut.conj (a y) := fun y => by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have hfix : ∀ y : ↥X, a y = y ↔ (y : G) ∈ Subgroup.centralizer ({t} : Set G) := by
    intro y
    constructor
    · intro h
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : t⁻¹ * (y : G) * t = y := by
        have := congrArg Subtype.val h
        rwa [ha, hs.coe_conjAut] at this
      calc (y : G) * t = t * (t⁻¹ * (y : G) * t) := by group
        _ = t * y := by rw [h1]
    · intro h
      exact hs.conjAut_of_mem_cent h
  ext c
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    show MulAut.conj y ∈ Subgroup.centralizer ({a} : Set (MulAut ↥X))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyfix : a y = y := (hfix y).mpr ((Subgroup.mem_subgroupOf.mp hy).2)
    have := hconj y
    rw [hyfix] at this
    calc MulAut.conj y * a = (a * MulAut.conj y * a⁻¹) * a := by rw [this]
      _ = a * MulAut.conj y := by group
  · rintro ⟨⟨y, rfl⟩, hy⟩
    refine ⟨y, ?_, rfl⟩
    have hy' : MulAut.conj y ∈ Subgroup.centralizer ({a} : Set (MulAut ↥X)) := hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy'
    have h1 : MulAut.conj (a y) = MulAut.conj y := by
      rw [← hconj y]
      calc a * MulAut.conj y * a⁻¹ = (a * MulAut.conj y) * a⁻¹ := rfl
        _ = (MulAut.conj y * a) * a⁻¹ := by rw [hy']
        _ = MulAut.conj y := by group
    have h2 : a y = y := hι h1
    exact Subgroup.mem_subgroupOf.mpr ⟨y.2, (hfix y).mp h2⟩

theorem IdentSetting.exists_socle_conjAut (hs : IdentSetting X K t) (hsimple : IsSimpleGroup ↥X) :
    ∃ L : Subgroup (MulAut ↥X), L ≤ inner ↥X ∧
      CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({(hs.conjAut : MulAut ↥X)} :
        Set (MulAut ↥X))) ∧ Nonempty (↥L ≃* ↥K) := by
  have hZ := hs.center_eq_bot_of_simple hsimple
  have hι := conj_injective_of_center_bot hZ
  set a : MulAut ↥X := hs.conjAut with ha
  set C : Subgroup G := X ⊓ Subgroup.centralizer ({t} : Set G) with hC
  set N : Subgroup (MulAut ↥X) := (C.subgroupOf X).map (MulAut.conj : ↥X →* MulAut ↥X) with hN
  set L : Subgroup (MulAut ↥X) := (K.subgroupOf X).map (MulAut.conj : ↥X →* MulAut ↥X) with hL
  have hcomp : CFSG.Assembly.IsComponentOf L N := hs.isComponentOf_map MulAut.conj hι
  have hNeq : N = inner ↥X ⊓ Subgroup.centralizer ({a} : Set (MulAut ↥X)) :=
    hs.map_conj_eq_inner_inf_centralizer hsimple
  have hNa : N ≤ Subgroup.centralizer ({a} : Set (MulAut ↥X)) := hNeq ▸ inf_le_right
  have hNnormal : (N.subgroupOf (Subgroup.centralizer ({a} : Set (MulAut ↥X)))).Normal := by
    rw [hNeq, Subgroup.inf_subgroupOf_right]
    infer_instance
  refine ⟨L, hcomp.1.trans (hNeq ▸ inf_le_left), ⟨hcomp.1.trans hNa,
    assemblySubnormal_of_normal hcomp.2.1 hNa hNnormal, hcomp.2.2⟩, ⟨?_⟩⟩
  exact (((K.subgroupOf X).equivMapOfInjective _ hι).symm).trans
    (Subgroup.subgroupOfEquivOfLe hs.K_le)

theorem IdentSetting.exists_socle (hs : IdentSetting X K t) (hsimple : IsSimpleGroup ↥X) :
    ∃ (a : MulAut ↥X) (L : Subgroup (MulAut ↥X)), orderOf a = 2 ∧ L ≤ inner ↥X ∧
      CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({a} : Set (MulAut ↥X))) ∧
      Nonempty (↥L ≃* ↥K) := by
  obtain ⟨L, h1, h2, h3⟩ := hs.exists_socle_conjAut hsimple
  exact ⟨hs.conjAut, L, hs.orderOf_conjAut, h1, h2, h3⟩

theorem IsKType.exists_psl_two_source
    {K : Subgroup G} (hK : IsKType K) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel ↥K .PSL 2 p f := by
  rcases hK with ⟨p, hp, h7, hm⟩ | hK | hK
  · exact ⟨p, 1, hp.1, by omega, le_rfl, hm⟩
  · obtain ⟨ℓ, e, hℓ, hodd, he, hm⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.small_models_odd_linear_two_aliases ↥K
        (Or.inr (Or.inr (Or.inr hK)))
    exact ⟨ℓ, e, hℓ, by rintro rfl; exact absurd hodd (by decide), he, hm⟩
  · obtain ⟨ℓ, e, hℓ, hodd, he, hm⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.small_models_odd_linear_two_aliases ↥K
        (Or.inr (Or.inl hK))
    exact ⟨ℓ, e, hℓ, by rintro rfl; exact absurd hodd (by decide), he, hm⟩

theorem IdentSetting.exists_inner_of_mem_inner (hs : IdentSetting X K t)
    (hα : (hs.conjAut : MulAut ↥X) ∈ inner ↥X) :
    ∃ x : ↥X, ∀ y : ↥X, hs.conjAut y = x * y * x⁻¹ := by
  obtain ⟨x, hx⟩ := hα
  exact ⟨x, fun y => by rw [← hx, MulAut.conj_apply]⟩

theorem IdentSetting.conjAut_mem_inner_of_equiv (hs : IdentSetting X K t) {Γ : Type*} [Group Γ]
    (e : ↥X ≃* Γ) (h : ∀ α : MulAut Γ, α * α = 1 → α ∈ inner Γ) :
    (hs.conjAut : MulAut ↥X) ∈ inner ↥X := by
  have haa : (hs.conjAut : MulAut ↥X) * hs.conjAut = 1 :=
    MulEquiv.ext fun y => hs.conjAut_conjAut y
  have hα2 : MulAut.congr e hs.conjAut * MulAut.congr e hs.conjAut = 1 := by
    rw [← map_mul, haa, map_one]
  have hmem : MulAut.congr e hs.conjAut ∈ inner Γ := h _ hα2
  rw [← inner_map_congr e] at hmem
  obtain ⟨β, hβ, hβe⟩ := hmem
  have : β = hs.conjAut := (MulAut.congr e).injective hβe
  rwa [this] at hβ

theorem IdentSetting.false_of_all_inner (hs : IdentSetting X K t) (hsimple : IsSimpleGroup ↥X)
    {Γ : Type*} [Group Γ] (e : ↥X ≃* Γ) (h : ∀ α : MulAut Γ, α * α = 1 → α ∈ inner Γ)
    (hfree : ∀ y : Γ, orderOf y = 2 →
      ∀ B : Subgroup ↥(Subgroup.centralizer ({y} : Set Γ)), ¬ CFSG.IsComponent B) : False := by
  obtain ⟨x, hx⟩ := hs.exists_inner_of_mem_inner (hs.conjAut_mem_inner_of_equiv e h)
  exact hs.false_of_inner hsimple e hfree x hx

theorem IdentSetting.exists_noncomm_inner (hs : IdentSetting X K t) (hsimple : IsSimpleGroup ↥X) :
    ∃ x y : ↥(inner ↥X), x * y ≠ y * x := by
  have hZ := hs.center_eq_bot_of_simple hsimple
  obtain ⟨-, -, a, b, hab⟩ := hs.quasi
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  have hab' : a' * b' ≠ b' * a' := fun h =>
    hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])
  exact ⟨innerEquiv hZ a', innerEquiv hZ b', fun h => hab' ((innerEquiv hZ).injective (by
    rw [map_mul, map_mul]; exact h))⟩

theorem IsKType.exists_psl_two_source_quot
    [Finite G] {K : Subgroup G} (hK : IsKType K)
    {A : Type} [Group A] {L : Subgroup A} (e : ↥L ≃* ↥K) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 p f := by
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hK.exists_psl_two_source
  obtain ⟨hsimple, hnc⟩ := isKType_simple hK
  have hZK : Subgroup.center ↥K = ⊥ := center_eq_bot_of_simple_nonab hnc
  have hZL : Subgroup.center ↥L = ⊥ := by
    have := Subgroup.map_center_eq e
    rw [hZK] at this
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp this
  let q : (↥L ⧸ Subgroup.center ↥L) ≃* ↥K :=
    ((QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot).trans e
  exact ⟨p, f, hp, hp2, hf,
    CFSG.QuasithinUnique.Unc25Small.statedClassicalModel_psl_of_mulEquiv q hm⟩

end SocleData


end CFSG.QuasithinUnique.Id2519
