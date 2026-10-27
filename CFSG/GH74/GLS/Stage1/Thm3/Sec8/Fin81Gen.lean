module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Ref
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylModel

public section

open Equiv

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

open CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.ShapeModel Subgroup

section Generic
variable {G : Type*} [Group G]

theorem exists_hom_two_cyclic (V W : Subgroup G) (hV : IsCyclic V) (hW : IsCyclic W)
    (hVc : Nat.card V = 4) (hWc : Nat.card W = 4)
    (hcomm : ∀ x ∈ V, ∀ y ∈ W, x * y = y * x) (hdisj : V ⊓ W = ⊥) :
    ∃ fn : Multiplicative V4 →* G, Function.Injective fn ∧ fn.range = V ⊔ W := by
  obtain ⟨g₁, hg₁⟩ := hV.exists_generator
  obtain ⟨g₂, hg₂⟩ := hW.exists_generator
  have ho₁ : orderOf (g₁ : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg₁, hVc]
  have ho₂ : orderOf (g₂ : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg₂, hWc]
  have hp₁ : (g₁ : G) ^ 4 = 1 := by rw [← ho₁]; exact pow_orderOf_eq_one _
  have hp₂ : (g₂ : G) ^ 4 = 1 := by rw [← ho₂]; exact pow_orderOf_eq_one _
  have hz₁ : Subgroup.zpowers (g₁ : G) = V := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact V.zpow_mem g₁.2 k
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg₁ ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hz₂ : Subgroup.zpowers (g₂ : G) = W := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact W.zpow_mem g₂.2 k
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg₂ ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hr₁ : (cycHom 4 (g₁ : G) hp₁).range = V := by rw [cycHom_range, hz₁]
  have hr₂ : (cycHom 4 (g₂ : G) hp₂).range = W := by rw [cycHom_range, hz₂]
  have hi₁ := cycHom_injective 4 (g₁ : G) hp₁ ho₁
  have hi₂ := cycHom_injective 4 (g₂ : G) hp₂ ho₂
  have hc₁ : ∀ x, cycHom 4 (g₁ : G) hp₁ x ∈ V := fun x => by
    have h : cycHom 4 (g₁ : G) hp₁ x ∈ (cycHom 4 (g₁ : G) hp₁).range := ⟨x, rfl⟩
    rwa [hr₁] at h
  have hc₂ : ∀ x, cycHom 4 (g₂ : G) hp₂ x ∈ W := fun x => by
    have h : cycHom 4 (g₂ : G) hp₂ x ∈ (cycHom 4 (g₂ : G) hp₂).range := ⟨x, rfl⟩
    rwa [hr₂] at h
  have hcc : ∀ x y, cycHom 4 (g₂ : G) hp₂ y * cycHom 4 (g₁ : G) hp₁ x =
      cycHom 4 (g₁ : G) hp₁ x * cycHom 4 (g₂ : G) hp₂ y := fun x y => (hcomm _ (hc₁ x) _ (hc₂ y)).symm
  let fn : Multiplicative V4 →* G := MonoidHom.mk'
    (fun v => cycHom 4 (g₁ : G) hp₁ (Multiplicative.ofAdd (Multiplicative.toAdd v).1) *
      cycHom 4 (g₂ : G) hp₂ (Multiplicative.ofAdd (Multiplicative.toAdd v).2))
    (fun v w => by
      simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ofAdd_add, map_mul]
      calc _ = cycHom 4 (g₁ : G) hp₁ (Multiplicative.ofAdd (Multiplicative.toAdd v).1) *
            (cycHom 4 (g₁ : G) hp₁ (Multiplicative.ofAdd (Multiplicative.toAdd w).1) *
              cycHom 4 (g₂ : G) hp₂ (Multiplicative.ofAdd (Multiplicative.toAdd v).2)) *
            cycHom 4 (g₂ : G) hp₂ (Multiplicative.ofAdd (Multiplicative.toAdd w).2) := by
              simp only [mul_assoc]
        _ = _ := by
              rw [← hcc (Multiplicative.ofAdd (Multiplicative.toAdd w).1)
                (Multiplicative.ofAdd (Multiplicative.toAdd v).2)]
              simp only [mul_assoc])
  refine ⟨fn, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro v hv
    have hv' : cycHom 4 (g₁ : G) hp₁ (Multiplicative.ofAdd (Multiplicative.toAdd v).1) *
      cycHom 4 (g₂ : G) hp₂ (Multiplicative.ofAdd (Multiplicative.toAdd v).2) = 1 := hv
    set x := Multiplicative.ofAdd (Multiplicative.toAdd v).1 with hx
    set y := Multiplicative.ofAdd (Multiplicative.toAdd v).2 with hy
    have h1 : cycHom 4 (g₁ : G) hp₁ x = (cycHom 4 (g₂ : G) hp₂ y)⁻¹ := eq_inv_of_mul_eq_one_left hv'
    have h2 : cycHom 4 (g₁ : G) hp₁ x ∈ V ⊓ W := ⟨hc₁ x, by rw [h1]; exact W.inv_mem (hc₂ y)⟩
    rw [hdisj, Subgroup.mem_bot] at h2
    have h3 : cycHom 4 (g₂ : G) hp₂ y = 1 := by
      have : (cycHom 4 (g₂ : G) hp₂ y)⁻¹ = 1 := by rw [← h1, h2]
      simpa using this
    have hx1 : x = 1 := hi₁ (by rw [h2, map_one])
    have hy1 : y = 1 := hi₂ (by rw [h3, map_one])
    apply Multiplicative.toAdd.injective
    ext
    · have := congrArg Multiplicative.toAdd hx1
      simpa [hx] using this
    · have := congrArg Multiplicative.toAdd hy1
      simpa [hy] using this
  · apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact Subgroup.mul_mem_sup (hc₁ _) (hc₂ _)
    · refine sup_le ?_ ?_
      · intro x hx
        have hx' : x ∈ (cycHom 4 (g₁ : G) hp₁).range := by rwa [hr₁]
        obtain ⟨t, rfl⟩ := hx'
        exact ⟨Multiplicative.ofAdd ((Multiplicative.toAdd t), 0), by simp [fn]⟩
      · intro x hx
        have hx' : x ∈ (cycHom 4 (g₂ : G) hp₂).range := by rwa [hr₂]
        obtain ⟨t, rfl⟩ := hx'
        exact ⟨Multiplicative.ofAdd (0, (Multiplicative.toAdd t)), by simp [fn]⟩


theorem card_eq_mul_of_factor {S A R : Subgroup G} (hAS : A ≤ S) (hRS : R ≤ S) (hdisj : A ⊓ R = ⊥)
    (hfac : ∀ s ∈ S, ∃ a ∈ A, ∃ r ∈ R, s = a * r) : Nat.card S = Nat.card A * Nat.card R := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p : A × R => (⟨p.1 * p.2, S.mul_mem (hAS p.1.2) (hRS p.2.2)⟩ : S)) ⟨?_, ?_⟩)
  · rintro ⟨⟨a, ha⟩, ⟨r, hr⟩⟩ ⟨⟨a', ha'⟩, ⟨r', hr'⟩⟩ h
    have h1 : a * r = a' * r' := congrArg Subtype.val h
    have h2 : a'⁻¹ * a = r' * r⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * r) * r⁻¹ := by group
        _ = a'⁻¹ * (a' * r') * r⁻¹ := by rw [h1]
        _ = r' * r⁻¹ := by group
    have h3 : a'⁻¹ * a ∈ A ⊓ R := ⟨A.mul_mem (A.inv_mem ha') ha, by rw [h2]; exact R.mul_mem hr' (R.inv_mem hr)⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    have h4 : a = a' := by
      have := congrArg (fun x => a' * x) h3
      simpa using this
    subst h4
    have h5 : r = r' := by simpa using h1
    subst h5
    rfl
  · rintro ⟨s, hs⟩
    obtain ⟨a, ha, r, hr, rfl⟩ := hfac s hs
    exact ⟨(⟨a, ha⟩, ⟨r, hr⟩), rfl⟩


theorem inf_pgroups_trivial {P Q : Subgroup G} {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hP : IsPGroup p P) (hQ : IsPGroup q Q) {x : G} (hxP : x ∈ P) (hxQ : x ∈ Q) : x = 1 := by
  obtain ⟨a, ha⟩ := hP ⟨x, hxP⟩
  obtain ⟨b, hb⟩ := hQ ⟨x, hxQ⟩
  have ha' : x ^ (p ^ a) = 1 := by simpa using congrArg Subtype.val ha
  have hb' : x ^ (q ^ b) = 1 := by simpa using congrArg Subtype.val hb
  have h1 := orderOf_dvd_of_pow_eq_one ha'
  have h2 := orderOf_dvd_of_pow_eq_one hb'
  have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes (Fact.out) (Fact.out)).2 hpq)
  have h3 : Nat.Coprime (orderOf x) (q ^ b) := Nat.Coprime.coprime_dvd_left h1 hcop
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h3 h2)


theorem exists_fn_fg [Finite G]
    (A S Sg : Subgroup G) (h : G) (θ : Multiplicative V4 →* G) (hθinj : Function.Injective θ)
    (hθA : θ.range = A) (hAS : A ≤ S)
    (hnorm : ∀ x ∈ S ⊔ zpowers h, ∀ a ∈ A, x * a * x⁻¹ ∈ A)
    (hH : S ⊔ zpowers h = A ⊔ Sg) (hAdisj : A ⊓ Sg = ⊥)
    (hkerc : ∀ σ ∈ Sg, (∀ a ∈ A, σ * a = a * σ) → σ ∈ zpowers (h ^ 3))
    (hS128 : Nat.card S = 128) (hA16 : Nat.card A = 16) (hS2 : IsPGroup 2 S)
    (hh3 : IsPGroup 3 (zpowers h)) (hcube : ∀ a ∈ A, h ^ 3 * a = a * h ^ 3)
    (hN : ((zpowers (h ^ 3)).subgroupOf Sg).Normal)
    (e0 : (Sg ⧸ (zpowers (h ^ 3)).subgroupOf Sg) ≃* Perm (Fin 4)) :
    ∃ (fn : Multiplicative V4 →* G) (fg : R0 →* G), (∀ v, fn v ∈ A) ∧ Function.Injective fn ∧
      Function.Injective fg ∧ (∀ r, fg r ∈ S ⊓ Sg) ∧
      (∀ r v, fg r * fn v * (fg r)⁻¹ = fn (ψ r v)) := by
  classical
  have hSgH : Sg ≤ S ⊔ zpowers h := by rw [hH]; exact le_sup_right
  have hSH : S ≤ S ⊔ zpowers h := le_sup_left
  have hSgN : Sg ≤ Subgroup.normalizer (A : Set G) := by
    intro σ hσ
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha; exact hnorm σ (hSgH hσ) a ha
    · intro ha
      have := hnorm σ⁻¹ ((S ⊔ zpowers h).inv_mem (hSgH hσ)) _ ha
      simpa [mul_assoc] using this
  have hfac : ∀ s ∈ S, ∃ a ∈ A, ∃ r ∈ S ⊓ Sg, s = a * r := by
    intro s hs
    have h1 : s ∈ A ⊔ Sg := hH ▸ hSH hs
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A Sg hSgN] at h1
    obtain ⟨a, ha, σ, hσ, rfl⟩ := h1
    refine ⟨a, ha, σ, ⟨?_, hσ⟩, rfl⟩
    have : σ = a⁻¹ * (a * σ) := by group
    rw [this]; exact S.mul_mem (S.inv_mem (hAS ha)) hs
  have hRS : S ⊓ Sg ≤ S := inf_le_left
  have hAR : A ⊓ (S ⊓ Sg) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ A ⊓ Sg := ⟨hx.1, hx.2.2⟩
    rw [hAdisj] at this
    exact this
  have hRcard : Nat.card (S ⊓ Sg : Subgroup G) = 8 := by
    have := card_eq_mul_of_factor hAS hRS hAR hfac
    rw [hS128, hA16] at this
    omega
  let θ' : Multiplicative V4 ≃* A := MulEquiv.ofBijective
    (θ.codRestrict A (fun v => by rw [← hθA]; exact ⟨v, rfl⟩))
    ⟨fun x y hxy => hθinj (congrArg Subtype.val hxy), fun a => by
      have : (a : G) ∈ θ.range := by rw [hθA]; exact a.2
      obtain ⟨v, hv⟩ := this
      exact ⟨v, Subtype.ext hv⟩⟩
  have hθ' : ∀ v, ((θ' v : A) : G) = θ v := fun v => rfl
  let c : Sg →* MulAut A := A.normalizerMonoidHom.comp (Subgroup.inclusion hSgN)
  have hc : ∀ (σ : Sg) (a : A), ((c σ a : A) : G) = σ * a * (σ : G)⁻¹ := fun σ a => rfl
  let ρ₁ : Sg →* MulAut (Multiplicative V4) := (MulAut.congr θ'.symm).toMonoidHom.comp c
  have hρ₁ : ∀ (σ : Sg) (w : Multiplicative V4), θ (ρ₁ σ w) = σ * θ w * (σ : G)⁻¹ := by
    intro σ w
    have h1 : θ' (ρ₁ σ w) = c σ (θ' w) := by
      show θ' ((MulAut.congr θ'.symm) (c σ) w) = _
      simp [MulAut.congr_apply]
    calc θ (ρ₁ σ w) = ((θ' (ρ₁ σ w) : A) : G) := rfl
      _ = _ := by rw [h1, hc]; rfl
  have hker : ∀ x ∈ (zpowers (h ^ 3)).subgroupOf Sg, ρ₁ x = 1 := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine MulEquiv.ext fun w => ?_
    apply hθinj
    rw [hρ₁]
    show _ = θ w
    have hmem : θ w ∈ A := by rw [← hθA]; exact ⟨w, rfl⟩
    have hcm : Commute (h ^ 3) (θ w) := hcube _ hmem
    have hcm' : Commute ((h ^ 3) ^ k) (θ w) := hcm.zpow_left k
    rw [← hk]
    have := hcm'.eq
    calc (h ^ 3) ^ k * θ w * ((h ^ 3) ^ k)⁻¹ = θ w * (h ^ 3) ^ k * ((h ^ 3) ^ k)⁻¹ := by rw [this]
      _ = θ w := by group
  let ρ₀ : (Sg ⧸ (zpowers (h ^ 3)).subgroupOf Sg) →* MulAut (Multiplicative V4) :=
    QuotientGroup.lift _ ρ₁ hker
  let ρbar : Perm (Fin 4) →* MulAut (Multiplicative V4) := ρ₀.comp e0.symm.toMonoidHom
  have hρbar : ∀ σ : Sg, ρbar (e0 (QuotientGroup.mk σ)) = ρ₁ σ := by
    intro σ
    show ρ₀ (e0.symm (e0 (QuotientGroup.mk σ))) = ρ₁ σ
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hinj : Function.Injective ρbar := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨q, hq⟩ := e0.surjective x
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective q
    have hρσ : ρ₁ σ = 1 := by rw [← hρbar, hq, hx]
    have hσc' : ∀ a ∈ A, (σ : G) * a = a * (σ : G) := by
      intro a ha
      have : a ∈ θ.range := by rw [hθA]; exact ha
      obtain ⟨w, rfl⟩ := this
      have h1 := hρ₁ σ w
      rw [hρσ] at h1
      have h2 : θ w = (σ : G) * θ w * (σ : G)⁻¹ := h1
      calc (σ : G) * θ w = (σ : G) * θ w * (σ : G)⁻¹ * σ := by group
        _ = θ w * σ := by rw [← h2]
    have hσN : (σ : G) ∈ zpowers (h ^ 3) := hkerc σ σ.2 hσc'
    have h1 : (QuotientGroup.mk σ : Sg ⧸ (zpowers (h ^ 3)).subgroupOf Sg) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hσN
    rw [h1, map_one] at hq
    exact hq.symm
  obtain ⟨β₀, π₀, hβ₀⟩ := exists_conj_refAct ρbar hinj
  let N : Subgroup Sg := (zpowers (h ^ 3)).subgroupOf Sg
  let e1 : (S ⊓ Sg : Subgroup G) →* Perm (Fin 4) :=
    e0.toMonoidHom.comp ((QuotientGroup.mk' N).comp
      (Subgroup.inclusion (inf_le_right : S ⊓ Sg ≤ Sg)))
  have he1 : ∀ x : (S ⊓ Sg : Subgroup G), e1 x = e0 (QuotientGroup.mk (⟨x.1, x.2.2⟩ : Sg)) :=
    fun x => rfl
  have hz3 : zpowers (h ^ 3) ≤ zpowers h := Subgroup.zpowers_le.2 (pow_mem (mem_zpowers h) 3)
  have he1inj : Function.Injective e1 := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (QuotientGroup.mk (⟨x.1, x.2.2⟩ : Sg) : Sg ⧸ N) = 1 := by
      apply e0.injective
      rw [← he1, hx]
      simp
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    have hx3 : (x : G) ∈ zpowers h := hz3 h1
    have : (x : G) = 1 := inf_pgroups_trivial (p := 2) (q := 3) (by norm_num) hS2 hh3 x.2.1 hx3
    exact Subtype.ext this
  have hR1card : Nat.card ((e1.range).map (MulAut.conj π₀).toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj π₀).injective,
      Nat.card_congr (MonoidHom.ofInjective he1inj).toEquiv.symm, hRcard]
  obtain ⟨τ, hτ⟩ := exists_conj_R0 _ hR1card
  have hmem : ∀ x' : (S ⊓ Sg : Subgroup G), (τ * π₀) * e1 x' * (τ * π₀)⁻¹ ∈ R0 := by
    intro x'
    have h1 : π₀ * e1 x' * π₀⁻¹ ∈ (e1.range).map (MulAut.conj π₀).toMonoidHom :=
      ⟨e1 x', ⟨x', rfl⟩, rfl⟩
    have h2 := hτ _ h1
    have : (τ * π₀) * e1 x' * (τ * π₀)⁻¹ = τ * (π₀ * e1 x' * π₀⁻¹) * τ⁻¹ := by group
    rw [this]; exact h2
  let E : (S ⊓ Sg : Subgroup G) →* R0 :=
    ((MulAut.conj (τ * π₀)).toMonoidHom.comp e1).codRestrict R0 hmem
  have hEinj : Function.Injective E := by
    intro x y hxy
    apply he1inj
    have : (τ * π₀) * e1 x * (τ * π₀)⁻¹ = (τ * π₀) * e1 y * (τ * π₀)⁻¹ := congrArg Subtype.val hxy
    simpa using this
  have hEbij : Function.Bijective E := by
    refine (Nat.bijective_iff_injective_and_card E).2 ⟨hEinj, ?_⟩
    rw [hRcard, card_R0]
  let Eeq : (S ⊓ Sg : Subgroup G) ≃* R0 := MulEquiv.ofBijective E hEbij
  let β : MulAut (Multiplicative V4) := refAct τ * β₀
  have hβ : ∀ x, β * ρbar x * β⁻¹ = refAct ((τ * π₀) * x * (τ * π₀)⁻¹) := by
    intro x
    calc β * ρbar x * β⁻¹ = refAct τ * (β₀ * ρbar x * β₀⁻¹) * (refAct τ)⁻¹ := by
          simp only [β]; group
      _ = refAct τ * refAct (π₀ * x * π₀⁻¹) * (refAct τ)⁻¹ := by rw [hβ₀]
      _ = refAct (τ * (π₀ * x * π₀⁻¹) * τ⁻¹) := by simp [map_mul, map_inv]
      _ = _ := by rw [show τ * (π₀ * x * π₀⁻¹) * τ⁻¹ = (τ * π₀) * x * (τ * π₀)⁻¹ by group]
  let fn : Multiplicative V4 →* G := θ.comp β⁻¹.toMonoidHom
  let fg : R0 →* G := (S ⊓ Sg : Subgroup G).subtype.comp Eeq.symm.toMonoidHom
  refine ⟨fn, fg, fun v => ?_, ?_, ?_, fun r => (Eeq.symm r).2, ?_⟩
  · have : θ (β⁻¹ v) ∈ θ.range := ⟨_, rfl⟩
    rw [hθA] at this
    exact this
  · intro x y hxy
    exact β⁻¹.injective (hθinj hxy)
  · intro x y hxy
    exact Eeq.symm.injective (Subtype.ext hxy)
  · intro r v
    set x' : (S ⊓ Sg : Subgroup G) := Eeq.symm r with hx'
    have hEx : E x' = r := by
      have := Eeq.apply_symm_apply r
      exact this
    have hr : (r : Perm (Fin 4)) = (τ * π₀) * e1 x' * (τ * π₀)⁻¹ := by
      rw [← hEx]; rfl
    have hfg : fg r = (x' : G) := rfl
    set σ : Sg := ⟨x'.1, x'.2.2⟩ with hσ
    have hρσ : ρ₁ σ = ρbar (e1 x') := by rw [he1, hρbar]
    show fg r * θ (β⁻¹ v) * (fg r)⁻¹ = θ (β⁻¹ (ψ r v))
    rw [hfg]
    have h1 : (x' : G) * θ (β⁻¹ v) * (x' : G)⁻¹ = θ (ρbar (e1 x') (β⁻¹ v)) := by
      rw [← hρσ, hρ₁]
    rw [h1]
    congr 1
    have h2 : ψ r = β * ρbar (e1 x') * β⁻¹ := by
      rw [hβ, ← hr]; rfl
    calc ρbar (e1 x') (β⁻¹ v) = ((ρbar (e1 x') * β⁻¹ : MulAut _)) v := rfl
      _ = ((β⁻¹ * (β * ρbar (e1 x') * β⁻¹) : MulAut _)) v := by congr 1; group
      _ = β⁻¹ (ψ r v) := by rw [← h2]; rfl

end Generic

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81
