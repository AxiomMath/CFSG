module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.OuterInvolutionRankFour
public import CFSG.LocalAnalysis.EvenBN.U4.Model.OuterInvolutionRankThree

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem commutator_le_of_relIndex_eq_two {H K : Subgroup G} (h2 : H.relIndex K = 2) :
    ⁅K, K⁆ ≤ H := by
  have hsq : ∀ a ∈ K, a * a ∈ H := fun a ha =>
    mem_subgroupOf.1 (Subgroup.mul_self_mem_of_index_two (H := H.subgroupOf K) h2 ⟨a, ha⟩)
  rw [commutator_le]
  intro a ha b hb
  have e : ⁅a, b⁆ = (a * a) * ((a⁻¹ * b) * (a⁻¹ * b)) * (b⁻¹ * b⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (mul_mem (hsq a ha) (hsq _ (mul_mem (inv_mem ha) hb))) (hsq _ (inv_mem hb))

theorem mul_comm_of_inf_centralizer_eq_bot [Finite G] {A : Subgroup G} {x : G}
    (hx : x ∈ normalizer (A : Set G)) (hx2 : x * x = 1)
    (hC : A ⊓ centralizer ({x} : Set G) = ⊥) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hconj : ∀ b ∈ A, x * b * x⁻¹ ∈ A := fun b hb => (mem_normalizer_iff.1 hx b).1 hb
  let φ : A → A := fun b => ⟨(b : G)⁻¹ * (x * b * x⁻¹), mul_mem (inv_mem b.2) (hconj b b.2)⟩
  have hinj : Function.Injective φ := by
    intro b b' hbb
    have e : (b : G)⁻¹ * (x * b * x⁻¹) = (b' : G)⁻¹ * (x * b' * x⁻¹) := congrArg Subtype.val hbb
    have e1 : (b' : G) * (b : G)⁻¹ * x = x * ((b' : G) * (b : G)⁻¹) := by
      calc (b' : G) * (b : G)⁻¹ * x = b' * ((b : G)⁻¹ * (x * b * x⁻¹)) * x * (b : G)⁻¹ := by
            group
        _ = b' * ((b' : G)⁻¹ * (x * b' * x⁻¹)) * x * (b : G)⁻¹ := by rw [e]
        _ = x * ((b' : G) * (b : G)⁻¹) := by group
    have hc : (b' : G) * (b : G)⁻¹ ∈ A ⊓ centralizer ({x} : Set G) :=
      mem_inf.2 ⟨mul_mem b'.2 (inv_mem b.2), mem_centralizer_singleton_iff.2 e1⟩
    rw [hC, mem_bot, mul_inv_eq_one] at hc
    exact Subtype.ext hc.symm
  have hsurj := Finite.injective_iff_surjective.1 hinj
  have hinv : ∀ a ∈ A, x * a * x⁻¹ = a⁻¹ := by
    intro a ha
    obtain ⟨b, hb⟩ := hsurj ⟨a, ha⟩
    have e : a = (b : G)⁻¹ * (x * b * x⁻¹) := (congrArg Subtype.val hb).symm
    rw [e, hxinv]
    calc x * ((b : G)⁻¹ * (x * b * x)) * x = x * (b : G)⁻¹ * x * b * (x * x) := by group
      _ = x⁻¹ * (b : G)⁻¹ * x⁻¹ * b := by rw [hx2, mul_one, hxinv]
      _ = ((b : G)⁻¹ * (x * b * x))⁻¹ := by group
  intro a ha b hb
  have h1 := hinv (a * b) (mul_mem ha hb)
  rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group, hinv a ha, hinv b hb,
    mul_inv_rev] at h1
  calc a * b = (b⁻¹ * a⁻¹)⁻¹ := by group
    _ = (a⁻¹ * b⁻¹)⁻¹ := by rw [h1]
    _ = b * a := by group

end Generic

section Cover

variable {G : Type} [Group G]

@[expose] def quotientCenterConjHom (X : Subgroup G) :
    normalizer (X : Set G) →* MulAut (X ⧸ center X) where
  toFun := quotientCenterConj
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H a => rw [quotientCenterConj_mk, map_one]; rfl
  map_mul' x y := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [MulAut.mul_apply, quotientCenterConj_mk, quotientCenterConj_mk, quotientCenterConj_mk,
        map_mul]
      rfl

theorem quotientCenterConjHom_mk (X : Subgroup G) (x : normalizer (X : Set G)) (a : X) :
    quotientCenterConjHom X x (a : X ⧸ center X) =
      ((X.normalizerMonoidHom x a : X) : X ⧸ center X) :=
  rfl

theorem quotientCenterConjHom_of_mem (X : Subgroup G) (a : X) :
    quotientCenterConjHom X ⟨a, le_normalizer a.2⟩ = MulAut.conj (a : X ⧸ center X) := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H b => rfl

theorem mem_centralizer_of_quotientCenterConjHom_eq_one {X : Subgroup G} (hX : ⁅X, X⁆ = X)
    {x : normalizer (X : Set G)} (hx : quotientCenterConjHom X x = 1) :
    (x : G) ∈ centralizer (X : Set G) := by
  have hXp : Group.IsPerfect X := (Common.isPerfect_subgroup_iff_commutator_eq X).2 hX
  have hc : ∀ a : X, X.normalizerMonoidHom x a * a⁻¹ ∈ center X := by
    intro a
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have := DFunLike.congr_fun hx (a : X ⧸ center X)
    rw [quotientCenterConjHom_mk, MulAut.one_apply] at this
    rw [this, mul_inv_cancel]
  let φ : X →* center X :=
    { toFun := fun a => ⟨_, hc a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change X.normalizerMonoidHom x (a * b) * (a * b)⁻¹ =
          (X.normalizerMonoidHom x a * a⁻¹) * (X.normalizerMonoidHom x b * b⁻¹)
        have hz := mem_center_iff.1 (hc b) a⁻¹
        rw [map_mul, mul_inv_rev]
        calc X.normalizerMonoidHom x a * X.normalizerMonoidHom x b * (b⁻¹ * a⁻¹) =
            X.normalizerMonoidHom x a * ((X.normalizerMonoidHom x b * b⁻¹) * a⁻¹) := by group
          _ = X.normalizerMonoidHom x a * (a⁻¹ * (X.normalizerMonoidHom x b * b⁻¹)) := by
            rw [hz]
          _ = X.normalizerMonoidHom x a * a⁻¹ * (X.normalizerMonoidHom x b * b⁻¹) := by group) }
  rw [mem_centralizer_iff]
  intro g hg
  have hmem : (⟨g, hg⟩ : X) ∈ commutator X := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact mem_top _
  have h1 : φ ⟨g, hg⟩ = 1 := Abelianization.commutator_subset_ker φ hmem
  have h2 : X.normalizerMonoidHom x ⟨g, hg⟩ = ⟨g, hg⟩ := by
    have : X.normalizerMonoidHom x ⟨g, hg⟩ * (⟨g, hg⟩ : X)⁻¹ = 1 := congrArg Subtype.val h1
    exact mul_inv_eq_one.1 this
  have h3 : (x : G) * g * (x : G)⁻¹ = g := congrArg Subtype.val h2
  calc g * x = x * g * (x : G)⁻¹ * x := by rw [h3]
    _ = x * g := by group

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] def coverFieldFactor {X : Subgroup G} (ψ : X ⧸ center X ≃* gramSU h (miyamotoJ4 K)) :
    normalizer (X : Set G) →* (K ≃+* K) :=
  (miyamotoFieldFactor h).comp ((MulAut.congr ψ).toMonoidHom.comp (quotientCenterConjHom X))

theorem exists_mul_of_coverFieldFactor_eq_one {X : Subgroup G} (hX : ⁅X, X⁆ = X)
    (ψ : X ⧸ center X ≃* gramSU h (miyamotoJ4 K)) {x : normalizer (X : Set G)}
    (hx : coverFieldFactor h ψ x = 1) :
    ∃ a ∈ X, ∃ c ∈ centralizer (X : Set G), (x : G) = a * c := by
  obtain ⟨s, hs⟩ := (miyamotoFieldFactor_eq_one_iff h _).1 hx
  obtain ⟨a₀, ha₀⟩ := QuotientGroup.mk_surjective (ψ.symm s)
  have e1 : MulAut.congr ψ (MulAut.conj (a₀ : X ⧸ center X)) = MulAut.conj s := by
    refine MulEquiv.ext fun q => ?_
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply, ha₀]
  have hx' : quotientCenterConjHom X x = MulAut.conj (a₀ : X ⧸ center X) :=
    (MulAut.congr ψ).injective (hs.trans e1.symm)
  set y : normalizer (X : Set G) := x * (⟨a₀, le_normalizer a₀.2⟩)⁻¹ with hydef
  have hy : quotientCenterConjHom X y = 1 := by
    rw [hydef, map_mul, map_inv, hx', quotientCenterConjHom_of_mem, mul_inv_cancel]
  have hyc := mem_centralizer_of_quotientCenterConjHom_eq_one hX hy
  refine ⟨a₀, a₀.2, (y : G), hyc, ?_⟩
  have hcomm := mem_centralizer_iff.1 hyc a₀ a₀.2
  have hyv : (y : G) = (x : G) * (a₀ : G)⁻¹ := rfl
  rw [hyv] at hcomm
  rw [hyv, hcomm]
  group

theorem coverFieldFactor_eq_one_of_perfect {X M : Subgroup G}
    (ψ : X ⧸ center X ≃* gramSU h (miyamotoJ4 K)) (hM : ⁅M, M⁆ = M)
    (hMX : M ≤ normalizer (X : Set G)) {x : G} (hx : x ∈ M) :
    coverFieldFactor h ψ ⟨x, hMX hx⟩ = 1 := by
  have := isCyclic_ringEquiv_of_unitaryFieldData h
  set σ : M →* (K ≃+* K) := (coverFieldFactor h ψ).comp (inclusion hMX) with hσ
  have hker : ⁅M, M⁆ ≤ σ.ker.map M.subtype := by
    rw [commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : M), ⟨b, hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm' _ _
  have hx' : x ∈ ⁅M, M⁆ := by rw [hM]; exact hx
  obtain ⟨y, hy, rfl⟩ := hker hx'
  exact hy

theorem exists_mul_centralizer_of_le_normalizer {X M : Subgroup G} (hX : ⁅X, X⁆ = X)
    (ψ : X ⧸ center X ≃* gramSU h (miyamotoJ4 K)) (hM : ⁅M, M⁆ = M)
    (hMX : M ≤ normalizer (X : Set G)) {x : G} (hx : x ∈ M) :
    ∃ a ∈ X, ∃ c ∈ centralizer (X : Set G), x = a * c :=
  exists_mul_of_coverFieldFactor_eq_one h hX ψ (coverFieldFactor_eq_one_of_perfect h ψ hM hMX hx)

theorem perfect_le_sup_of_le_normalizer {G₁ G₂ M : Subgroup G}
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hG₁ : ⁅G₁, G₁⁆ = G₁) (hG₂ : ⁅G₂, G₂⁆ = G₂)
    (ψ₁ : G₁ ⧸ center G₁ ≃* gramSU h (miyamotoJ4 K))
    (ψ₂ : G₂ ⧸ center G₂ ≃* gramSU h (miyamotoJ4 K))
    (hab : ∀ c ∈ centralizer (G₁ : Set G) ⊓ centralizer (G₂ : Set G),
      ∀ d ∈ centralizer (G₁ : Set G) ⊓ centralizer (G₂ : Set G), c * d = d * c)
    (hM : ⁅M, M⁆ = M) (hM₁ : M ≤ normalizer (G₁ : Set G)) (hM₂ : M ≤ normalizer (G₂ : Set G)) :
    M ≤ G₁ ⊔ G₂ := by
  have hdec : ∀ x ∈ M, ∃ g ∈ G₁ ⊔ G₂,
      ∃ c ∈ centralizer (G₁ : Set G) ⊓ centralizer (G₂ : Set G), x = g * c := by
    intro x hx
    obtain ⟨a₁, ha₁, c₁, hc₁, e₁⟩ := exists_mul_centralizer_of_le_normalizer h hG₁ ψ₁ hM hM₁ hx
    obtain ⟨a₂, ha₂, c₂, hc₂, e₂⟩ := exists_mul_centralizer_of_le_normalizer h hG₂ ψ₂ hM hM₂ hx
    have h12 : a₁ * a₂ = a₂ * a₁ := hcomm a₁ ha₁ a₂ ha₂
    refine ⟨a₁ * a₂, mul_mem (mem_sup_left ha₁) (mem_sup_right ha₂), (a₁ * a₂)⁻¹ * x,
      mem_inf.2 ⟨?_, ?_⟩, by group⟩
    ·
      have e : (a₁ * a₂)⁻¹ * x = a₂⁻¹ * c₁ := by rw [e₁]; group
      rw [e]
      refine mul_mem (inv_mem (mem_centralizer_iff.2 fun g hg => hcomm g hg a₂ ha₂)) hc₁
    ·
      have e : (a₁ * a₂)⁻¹ * x = a₁⁻¹ * c₂ := by rw [h12, e₂]; group
      rw [e]
      refine mul_mem (inv_mem (mem_centralizer_iff.2 fun g hg => (hcomm a₁ ha₁ g hg).symm)) hc₂
  have hcen : ∀ c ∈ centralizer (G₁ : Set G) ⊓ centralizer (G₂ : Set G), ∀ g ∈ G₁ ⊔ G₂,
      c * g = g * c := by
    intro c hc g hg
    have hle : G₁ ⊔ G₂ ≤ centralizer ({c} : Set G) := sup_le
      (fun a ha => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (mem_inf.1 hc).1 a ha))
      (fun b hb => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (mem_inf.1 hc).2 b hb))
    exact (mem_centralizer_singleton_iff.1 (hle hg)).symm
  rw [← hM, commutator_le]
  intro x hx y hy
  obtain ⟨g, hg, c, hc, rfl⟩ := hdec x hx
  obtain ⟨g', hg', c', hc', rfl⟩ := hdec y hy
  rw [commutatorElement_mul_mul_eq_of_commute (hcen c hc g' hg') (hab c hc c' hc')
    (hcen c' hc' g hg)]
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')

end Cover

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem mem_normalizer_of_conj_mem_normalizer (hS : Setting h L η t Q T) {G₁ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₁) (ψ : G₁ ⧸ center G₁ ≃* gramSU h (miyamotoJ4 K))
    (hZ : Odd (Nat.card (center G₁)))
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hNQ : normalizer (Q : Set G) ≤
      normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (g : G) (hg : g⁻¹ * t * g ∈
      normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) :
    g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  set G₂ := G₁.map (MulAut.conj t).toMonoidHom with hG₂
  set G₀ : Subgroup G := G₁ ⊔ G₂ with hG₀
  obtain ⟨hperf, hbot, hn₁⟩ :=
    SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hq
  have hn₂ := SeitzReduction.F4Pilot.dichotomy_map_mulAut (MulAut.conj t) hn₁
  have hperf₂ : ⁅G₂, G₂⁆ = G₂ := by rw [hG₂, ← map_commutator, hperf]
  have hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 (h₁₂ hb) a ha
  let e₂ : G₁ ≃* G₂ := Subgroup.equivMapOfInjective G₁ _ (MulAut.conj t).injective
  have hZ₂ : Odd (Nat.card (center G₂)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr e₂).toEquiv]
    exact hZ
  have htt := hS.t_mul_t
  have hne : G₁ ≠ G₂ := by
    intro e
    apply hbot
    have h11 : G₁ ≤ centralizer (G₁ : Set G) := by
      calc G₁ = G₂ := e
        _ ≤ centralizer (G₁ : Set G) := h₁₂
    rw [← hperf, commutator_eq_bot_iff_le_centralizer.2 h11]
  have hperm : ∀ x ∈ normalizer (G₀ : Set G), G₁.map (MulAut.conj x).toMonoidHom = G₁ ∨
      G₁.map (MulAut.conj x).toMonoidHom = G₂ := fun x hx =>
    SeitzReduction.F4Pilot.map_conj_eq_or_eq_of_perfect h₁₂ hperf hbot hn₁ hn₂ hx
  have hG₂' : G₁.map (MulAut.conj t⁻¹).toMonoidHom = G₂ := by rw [hS.t_inv]
  have hcomm12 : ⁅G₁, G₂⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.2 h₁₂
  have hcommD : ⁅G₁, G₁.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥ := by
    rw [hG₂']
    exact hcomm12
  have hLG₀ : L ≤ G₀ := by
    rw [← hS.range_diagonalHom_eq_L hperf ψ hcommD]
    rintro _ ⟨a, rfl⟩
    rw [Common.diagonalHom_apply]
    exact mul_mem (mem_sup_left a.2) (mem_sup_right (hG₂' ▸ Common.conj_mem_map_conj_inv t a.2))
  set C₀ : Subgroup G := centralizer (G₁ : Set G) ⊓ centralizer (G₂ : Set G) with hC₀
  have hmemG₂ : ∀ a ∈ G₁, t * a * t⁻¹ ∈ G₂ := fun a ha => ⟨a, ha, rfl⟩
  have hmemG₁ : ∀ b ∈ G₂, t⁻¹ * b * t ∈ G₁ := by
    rintro _ ⟨a, ha, rfl⟩
    change t⁻¹ * (t * a * t⁻¹) * t ∈ G₁
    rw [show t⁻¹ * (t * a * t⁻¹) * t = a by group]
    exact ha
  have htC₀ : t ∈ normalizer (C₀ : Set G) := by
    refine mem_normalizer_fintype fun c hc => ?_
    have hc₁ := (mem_inf.1 hc).1
    have hc₂ := (mem_inf.1 hc).2
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun a ha => ?_, mem_centralizer_iff.2 fun b hb => ?_⟩
    · have hat : t⁻¹ * a * t ∈ G₂ := by
        rw [show t⁻¹ * a * t = t * a * t⁻¹ by rw [hS.t_inv]]
        exact hmemG₂ a ha
      have := mem_centralizer_iff.1 hc₂ _ hat
      calc a * (t * c * t⁻¹) = t * ((t⁻¹ * a * t) * c) * t⁻¹ := by group
        _ = t * (c * (t⁻¹ * a * t)) * t⁻¹ := by rw [this]
        _ = t * c * t⁻¹ * a := by group
    · have hbt := hmemG₁ b hb
      have := mem_centralizer_iff.1 hc₁ _ hbt
      calc b * (t * c * t⁻¹) = t * ((t⁻¹ * b * t) * c) * t⁻¹ := by group
        _ = t * (c * (t⁻¹ * b * t)) * t⁻¹ := by rw [this]
        _ = t * c * t⁻¹ * b := by group
  have htG₁ : t ∉ centralizer (G₁ : Set G) := by
    intro ht
    apply hne
    refine le_antisymm (fun a ha => ?_) ?_
    · have e : t * a * t⁻¹ = a := by
        rw [← mem_centralizer_iff.1 ht a ha, mul_inv_cancel_right]
      exact e ▸ hmemG₂ a ha
    · rintro _ ⟨a, ha, rfl⟩
      change t * a * t⁻¹ ∈ G₁
      rw [← mem_centralizer_iff.1 ht a ha, mul_inv_cancel_right]
      exact ha
  have hC₀t : C₀ ⊓ centralizer ({t} : Set G) = ⊥ := by
    refine eq_bot_iff.2 fun c hc => ?_
    obtain ⟨hcC₀, hct⟩ := mem_inf.1 hc
    have hcL : c ∈ centralizer (L : Set G) := by
      refine mem_centralizer_iff.2 fun l hl => ?_
      have hle : G₀ ≤ centralizer ({c} : Set G) := sup_le
        (fun a ha => mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 (mem_inf.1 hcC₀).1 a ha))
        (fun b hb => mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 (mem_inf.1 hcC₀).2 b hb))
      exact mem_centralizer_singleton_iff.1 (hle (hLG₀ hl))
    have hk : c ∈ zpowers t := by
      rw [← hS.kernel_eq_zpowers']
      exact mem_inf.2 ⟨hcL, hct⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hk
    rcases hS.zpow_t_eq k with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1] at hcC₀
      exact absurd (mem_inf.1 hcC₀).1 htG₁
  have hab := mul_comm_of_inf_centralizer_eq_bot htC₀ htt hC₀t
  have hY : ∀ M : Subgroup G, ⁅M, M⁆ = M → M ≤ normalizer (G₀ : Set G) →
      M ≤ normalizer (G₁ : Set G) ⊓ normalizer (G₂ : Set G) := by
    intro M hM hMN
    have h2 := SeitzReduction.F4Pilot.relIndex_inf_normalizer_eq_two_of_swap htt rfl hne hperm
    rw [← SeitzReduction.F4Pilot.inf_normalizer_eq_of_swap htt rfl hne hperm, ← hM]
    exact (commutator_mono hMN hMN).trans (commutator_le_of_relIndex_eq_two h2)
  have hy := hS.map_conj_eq_of_conj_mem_normalizer hq ψ hZ h₁₂ g hg
  set A' : Subgroup G := G₁.map (MulAut.conj g).toMonoidHom with hA'
  have hA'perf : ⁅A', A'⁆ = A' := by rw [hA', ← map_commutator, hperf]
  have hA't : A'.map (MulAut.conj t⁻¹).toMonoidHom = G₂.map (MulAut.conj g).toMonoidHom := by
    rw [hS.t_inv, hA', SeitzReduction.F4Pilot.map_conj_map_conj_toMonoidHom, hG₂, ← hy,
      SeitzReduction.F4Pilot.map_conj_map_conj_toMonoidHom,
      show g * (g⁻¹ * t * g) = t * g by group]
  have hcommD' : ⁅A', A'.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥ := by
    rw [hA't, hA', ← map_commutator, hcomm12, Subgroup.map_bot]
  let e' : G₁ ≃* A' := Subgroup.equivMapOfInjective G₁ _ (MulAut.conj g).injective
  have hZ' : Odd (Nat.card (center A')) := by
    rw [← Nat.card_congr (Subgroup.centerCongr e').toEquiv]
    exact hZ
  have hsup := hS.sup_le_of_swap hA'perf ((quotientCenterCongr e').symm.trans ψ) hZ' hcommD'
    (hLG₀.trans le_normalizer) hNQ
  have hG₀' : A' ⊔ A'.map (MulAut.conj t⁻¹).toMonoidHom = G₀.map (MulAut.conj g).toMonoidHom := by
    rw [hA't, hA', hG₀, Subgroup.map_sup]
  rw [hG₀'] at hsup
  have hG₀perf : ⁅G₀, G₀⁆ = G₀ := le_antisymm (commutator_le_self _)
    (sup_le (hperf.ge.trans (commutator_mono le_sup_left le_sup_left))
      (hperf₂.ge.trans (commutator_mono le_sup_right le_sup_right)))
  have hG₀'perf : ⁅G₀.map (MulAut.conj g).toMonoidHom, G₀.map (MulAut.conj g).toMonoidHom⁆ =
      G₀.map (MulAut.conj g).toMonoidHom := by
    rw [← map_commutator, hG₀perf]
  have hNN := hY _ hG₀'perf hsup
  have hle : G₀.map (MulAut.conj g).toMonoidHom ≤ G₀ :=
    perfect_le_sup_of_le_normalizer h hcomm hperf hperf₂ ψ ((quotientCenterCongr e₂).symm.trans ψ)
      hab hG₀'perf (hNN.trans inf_le_left) (hNN.trans inf_le_right)
  have heq : G₀.map (MulAut.conj g).toMonoidHom = G₀ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])
  exact mem_normalizer_iff_map_conj_eq.2 heq

theorem false_of_quasisimple_swap (hS : Setting h L η t Q T) {G₁ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₁) (ψ : G₁ ⧸ center G₁ ≃* gramSU h (miyamotoJ4 K))
    (hZ : Odd (Nat.card (center G₁)))
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hNQ : normalizer (Q : Set G) ≤
      normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) :
    False := by
  have := hS.simple
  exact SeitzReduction.F4Pilot.false_of_simple_of_swap_of_isQuasisimple hS.t_two hq h₁₂ rfl
    fun g hg => hS.mem_normalizer_of_conj_mem_normalizer hq ψ hZ h₁₂ hNQ g hg

theorem center_eq_ker_diagonalHom (_hS : Setting h L η t Q T) {A : Subgroup G}
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hδ : (Common.diagonalHom A t hcomm).range = L) :
    center A = (Common.diagonalHom A t hcomm).ker := by
  set δ := Common.diagonalHom A t hcomm with hδdef
  have hZL := center_eq_bot_of_mulEquiv_gramSU h η
  refine le_antisymm (fun z hz => ?_) (Common.ker_diagonalHom_le_center hcomm)
  rw [MonoidHom.mem_ker]
  have hzL : δ z ∈ L := by
    rw [← hδ]
    exact ⟨z, rfl⟩
  have hc : (⟨δ z, hzL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro l
    obtain ⟨a, ha⟩ : (l : G) ∈ δ.range := by
      rw [hδ]
      exact l.2
    apply Subtype.ext
    change (l : G) * δ z = δ z * l
    rw [← ha, ← map_mul, ← map_mul, mem_center_iff.1 hz a]
  rw [hZL, mem_bot] at hc
  exact congrArg Subtype.val hc

@[expose] def quotientCenterEquivOfDiagonal (hS : Setting h L η t Q T) {A : Subgroup G}
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hδ : (Common.diagonalHom A t hcomm).range = L) :
    A ⧸ center A ≃* gramSU h (miyamotoJ4 K) :=
  ((QuotientGroup.quotientMulEquivOfEq (hS.center_eq_ker_diagonalHom hcomm hδ)).trans
    (QuotientGroup.quotientKerEquivRange _)).trans ((MulEquiv.subgroupCongr hδ).trans η)

theorem isQuasisimple_of_diagonal (hS : Setting h L η t Q T) {A : Subgroup G} (hA : ⁅A, A⁆ = A)
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hδ : (Common.diagonalHom A t hcomm).range = L) : CFSG.Open.IsQuasisimple A :=
  ⟨((Common.isPerfect_subgroup_iff_commutator_eq A).2 hA).commutator_eq_top,
    hS.isSimpleGroup_quotient_center (hS.quotientCenterEquivOfDiagonal hcomm hδ)⟩

theorem map_conj_le_centralizer_of_commutator (hS : Setting h L η t Q T) {A : Subgroup G}
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) :
    A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G) := by
  rw [← hS.t_inv]
  rw [commutator_comm] at hcomm
  exact commutator_eq_bot_iff_le_centralizer.1 hcomm

theorem false_of_diagonal_swap (hS : Setting h L η t Q T) {A : Subgroup G} (hA : ⁅A, A⁆ = A)
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hδ : (Common.diagonalHom A t hcomm).range = L)
    (hodd : Odd (Nat.card (Common.diagonalHom A t hcomm).ker))
    (hNQ : normalizer (Q : Set G) ≤
      normalizer ((A ⊔ A.map (MulAut.conj t⁻¹).toMonoidHom : Subgroup G) : Set G)) :
    False := by
  have hZodd : Odd (Nat.card (center A)) := by
    rw [hS.center_eq_ker_diagonalHom hcomm hδ]
    exact hodd
  have hmap : A.map (MulAut.conj t⁻¹).toMonoidHom = A.map (MulAut.conj t).toMonoidHom := by
    rw [hS.t_inv]
  rw [hmap] at hNQ
  exact hS.false_of_quasisimple_swap (hS.isQuasisimple_of_diagonal hA hcomm hδ)
    (hS.quotientCenterEquivOfDiagonal hcomm hδ) hZodd
    (hS.map_conj_le_centralizer_of_commutator hcomm) hNQ

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
