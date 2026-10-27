module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Gen
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.A5.Kc3NSC

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5
open CFSG.QuasithinUnique.A5.Kc3Gen

abbrev Dm : Type := Multiplicative ↥(evenWeight 5)

@[expose] def permAut (σ : Equiv.Perm (Fin 5)) : MulAut Dm where
  toFun x := Multiplicative.ofAdd (vact σ (Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd (vact σ⁻¹ (Multiplicative.toAdd x))
  left_inv x := by
    simp only [toAdd_ofAdd, ← vact_mul, inv_mul_cancel, vact_one, ofAdd_toAdd]
  right_inv x := by
    simp only [toAdd_ofAdd, ← vact_mul, mul_inv_cancel, vact_one, ofAdd_toAdd]
  map_mul' x y := by
    simp only [toAdd_mul, vact_add, ofAdd_add]

theorem permAut_apply (σ : Equiv.Perm (Fin 5)) (x : Dm) :
    permAut σ x = Multiplicative.ofAdd (vact σ (Multiplicative.toAdd x)) := rfl

@[expose] def permHom : Equiv.Perm (Fin 5) →* MulAut Dm where
  toFun := permAut
  map_one' := by
    ext x
    simp [permAut_apply, vact_one]
  map_mul' σ τ := by
    ext x
    simp [permAut_apply, vact_mul]

theorem permHom_apply (σ : Equiv.Perm (Fin 5)) (x : Dm) :
    permHom σ x = Multiplicative.ofAdd (vact σ (Multiplicative.toAdd x)) := rfl

theorem permHom_injective : Function.Injective permHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have h : ∀ w, vact σ w = w := fun w => by
    have := congrArg (fun g : MulAut Dm => Multiplicative.toAdd (g (Multiplicative.ofAdd w))) hσ
    simpa [permHom_apply] using this
  exact vact_faithful h

theorem cent_trivial (g : MulAut Dm)
    (hg : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → g * permHom σ = permHom σ * g) :
    g = 1 := by
  let gf : evenWeight 5 → evenWeight 5 := fun w => Multiplicative.toAdd (g (Multiplicative.ofAdd w))
  have hadd : ∀ x y, gf (x + y) = gf x + gf y := fun x y => by
    simp only [gf, ofAdd_add, map_mul, toAdd_mul]
  have hinj : Function.Injective gf := fun x y h => by
    have := g.injective (Multiplicative.toAdd.injective h)
    exact Multiplicative.ofAdd.injective this
  have hcomm : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → ∀ w, gf (vact σ w) = vact σ (gf w) := by
    intro σ hσ w
    have := congrArg (fun h : MulAut Dm => Multiplicative.toAdd (h (Multiplicative.ofAdd w))) (hg σ hσ)
    simpa [gf, permHom_apply] using this
  have := rigid gf hadd hinj hcomm
  refine MulEquiv.ext fun x => ?_
  have h1 : Multiplicative.toAdd (g x) = Multiplicative.toAdd x := by
    simpa [gf] using this (Multiplicative.toAdd x)
  rw [MulAut.one_apply]
  exact Multiplicative.toAdd.injective h1

section Closure

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem normalizer_closure {A H : Subgroup Γ} (hs : IsSimpleGroup ↥A)
    (hC : ∀ g : Γ, (∀ a ∈ A, g * a = a * g) → g = 1) (hAH : A ≤ H)
    (hHN : H ≤ Subgroup.normalizer (A : Set Γ)) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (H : Set Γ)) : g ∈ Subgroup.normalizer (A : Set Γ) := by
  classical
  set A' : Subgroup Γ := A.map (MulAut.conj g).toMonoidHom with hA'
  have hmemA' : ∀ x, x ∈ A' ↔ g⁻¹ * x * g ∈ A := by
    intro x
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using ha
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hgH : ∀ y ∈ H, g * y * g⁻¹ ∈ H := fun y hy => (Subgroup.mem_normalizer_iff.1 hg y).1 hy
  have hgH' : ∀ y ∈ H, g⁻¹ * y * g ∈ H := by
    intro y hy
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (H : Set Γ)).inv_mem hg) y).1 hy
    simpa using this
  have hA'H : A' ≤ H := by
    intro x hx
    have h1 : g⁻¹ * x * g ∈ H := hAH ((hmemA' x).1 hx)
    have := hgH _ h1
    simpa [mul_assoc] using this
  have hHA : ∀ h ∈ H, ∀ y ∈ A, h * y * h⁻¹ ∈ A := fun h hh y hy =>
    (Subgroup.mem_normalizer_iff.1 (hHN hh) y).1 hy
  have hHA' : ∀ h ∈ H, ∀ x ∈ A', h * x * h⁻¹ ∈ A' := by
    intro h hh x hx
    rw [hmemA']
    have h0 : g⁻¹ * h * g ∈ H := hgH' h hh
    have h1 := hHA _ h0 _ ((hmemA' x).1 hx)
    have : g⁻¹ * (h * x * h⁻¹) * g = (g⁻¹ * h * g) * (g⁻¹ * x * g) * (g⁻¹ * h * g)⁻¹ := by group
    rw [this]
    exact h1
  have hnorm : ((A ⊓ A').subgroupOf A).Normal := by
    refine (Subgroup.normal_subgroupOf_iff inf_le_left).2 ?_
    intro x k hx hk
    exact ⟨hHA k (hAH hk) x hx.1, hHA' k (hAH hk) x hx.2⟩
  have hcard : Nat.card ↥A' = Nat.card ↥A := Subgroup.card_map_of_injective (MulAut.conj g).injective
  have := hnorm
  rcases hs.eq_bot_or_eq_top_of_normal ((A ⊓ A').subgroupOf A) with hbot | htop
  · exfalso
    have hdis : Disjoint (A ⊓ A') A := Subgroup.subgroupOf_eq_bot.1 hbot
    have hAA' : ∀ x ∈ A, x ∈ A' → x = 1 := by
      intro x hxA hxA'
      have : x ∈ (A ⊓ A') ⊓ A := ⟨⟨hxA, hxA'⟩, hxA⟩
      rw [disjoint_iff.1 hdis] at this
      exact Subgroup.mem_bot.1 this
    have hcomm : ∀ x ∈ A', ∀ a ∈ A, x * a = a * x := by
      intro x hx a ha
      have hxH : x ∈ H := hA'H hx
      have hc1 : x * a * x⁻¹ * a⁻¹ ∈ A := A.mul_mem (hHA x hxH a ha) (A.inv_mem ha)
      have hc2 : x * a * x⁻¹ * a⁻¹ ∈ A' := by
        have h1 : a * x⁻¹ * a⁻¹ ∈ A' := hHA' a (hAH ha) _ (A'.inv_mem hx)
        have := A'.mul_mem hx h1
        simpa [mul_assoc] using this
      have h1 := hAA' _ hc1 hc2
      have : x * a = a * x := by
        calc x * a = (x * a * x⁻¹ * a⁻¹) * (a * x) := by group
          _ = a * x := by rw [h1, one_mul]
      exact this
    have hone : ∀ x ∈ A', x = 1 := fun x hx => hC x (fun a ha => hcomm x hx a ha)
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥A)
    have hmem : g * (a : Γ) * g⁻¹ ∈ A' := ⟨a, a.2, by simp [MulAut.conj_apply]⟩
    have := hone _ hmem
    apply ha
    apply Subtype.ext
    simpa using this
  · have hle : A ≤ A' := fun x hx => (Subgroup.subgroupOf_eq_top.1 htop) hx |>.2
    have hAeq : A = A' := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : g * x * g⁻¹ ∈ A' := ⟨x, hx, by simp [MulAut.conj_apply]⟩
      rwa [← hAeq] at this
    · intro hx
      rw [hAeq] at hx
      have := (hmemA' _).1 hx
      simpa [mul_assoc] using this

theorem le_normalizer_of_subnormal {A : Subgroup Γ} (hs : IsSimpleGroup ↥A)
    (hC : ∀ g : Γ, (∀ a ∈ A, g * a = a * g) → g = 1) {H B : Subgroup Γ} (h : IsSubnormal H B) :
    A ≤ H → H ≤ Subgroup.normalizer (A : Set Γ) → B ≤ Subgroup.normalizer (A : Set Γ) := by
  induction h with
  | refl H => intro _ h2; exact h2
  | @step H M B hHM hn _ ih =>
    intro hAH hHN
    have hMN : M ≤ Subgroup.normalizer (A : Set Γ) := by
      intro g hg
      have hgH : g ∈ Subgroup.normalizer (H : Set Γ) :=
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hn) hg
      exact normalizer_closure hs hC hAH hHN hgH
    exact ih (hAH.trans hHM) hMN

end Closure

@[expose] def altImg : Subgroup (MulAut Dm) := (alternatingGroup (Fin 5)).map permHom

theorem mem_altImg {σ : Equiv.Perm (Fin 5)} (hσ : Equiv.Perm.sign σ = 1) :
    permHom σ ∈ altImg :=
  Subgroup.mem_map.2 ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hσ, rfl⟩

theorem altImg_simple : IsSimpleGroup ↥altImg := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact (Subgroup.equivMapOfInjective (alternatingGroup (Fin 5)) permHom
    permHom_injective).symm.isSimpleGroup

theorem altImg_cent : ∀ g : MulAut Dm, (∀ a ∈ altImg, g * a = a * g) → g = 1 := by
  intro g hg
  exact cent_trivial g fun σ hσ => hg _ (mem_altImg hσ)

theorem exists_perm_of_mem_normalizer {g : MulAut Dm}
    (hg : g ∈ Subgroup.normalizer (altImg : Set (MulAut Dm))) :
    ∃ σ : Equiv.Perm (Fin 5), g = permHom σ := by
  let e : ↥(alternatingGroup (Fin 5)) ≃* ↥altImg :=
    Subgroup.equivMapOfInjective _ _ permHom_injective
  let c : MulAut ↥altImg := altImg.normalizerMonoidHom ⟨g, hg⟩
  let ψ : ↥(alternatingGroup (Fin 5)) ≃* ↥(alternatingGroup (Fin 5)) :=
    e.trans (c.trans e.symm)
  obtain ⟨σ, hσ⟩ := aut_inner ψ
  have key : ∀ a : ↥(alternatingGroup (Fin 5)),
      g * permHom (a : Equiv.Perm (Fin 5)) * g⁻¹ =
        permHom σ * permHom (a : Equiv.Perm (Fin 5)) * (permHom σ)⁻¹ := by
    intro a
    have h1 : permHom ((ψ a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
        g * permHom (a : Equiv.Perm (Fin 5)) * g⁻¹ := by
      have h2 : e (ψ a) = c (e a) := by
        show e (e.symm (c (e a))) = c (e a)
        exact e.apply_symm_apply _
      have h3 := congrArg (fun z : ↥altImg => (z : MulAut Dm)) h2
      have h4 : ((c (e a) : ↥altImg) : MulAut Dm) = g * ((e a : ↥altImg) : MulAut Dm) * g⁻¹ :=
        altImg.normalizerMonoidHom_apply_apply_coe ⟨g, hg⟩ (e a)
      exact h3.trans h4
    rw [← h1, hσ a]
    simp
  have hcent : (permHom σ)⁻¹ * g = 1 := by
    apply altImg_cent
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hx
    have h := key ⟨b, hb⟩
    calc (permHom σ)⁻¹ * g * permHom b = (permHom σ)⁻¹ * (g * permHom b * g⁻¹) * g := by group
      _ = (permHom σ)⁻¹ * (permHom σ * permHom b * (permHom σ)⁻¹) * g := by rw [h]
      _ = permHom b * ((permHom σ)⁻¹ * g) := by group
  exact ⟨σ, (inv_mul_eq_one.1 hcent).symm⟩

theorem nsc {Γ : Type*} [Group Γ] [Finite Γ] (ρ : Γ →* MulAut Dm) (L₀ : Subgroup Γ)
    (hsub : IsSubnormal L₀ ⊤) (hρ : L₀.map ρ = altImg) (γ : Γ) :
    ∃ σ : Equiv.Perm (Fin 5), ρ γ = permHom σ := by
  have h1 : IsSubnormal altImg ρ.range := by
    have := isSubnormal_map ρ hsub
    rwa [hρ, ← MonoidHom.range_eq_map] at this
  have h2 : ρ.range ≤ Subgroup.normalizer (altImg : Set (MulAut Dm)) :=
    le_normalizer_of_subnormal altImg_simple altImg_cent h1 le_rfl Subgroup.le_normalizer
  exact exists_perm_of_mem_normalizer (h2 ⟨γ, rfl⟩)

section Geometric

variable {G : Type} [Group G]

@[expose] noncomputable def rhoY (V Y : Subgroup G) (hYV : Y ≤ Subgroup.normalizer (V : Set G))
    (β : ↥V ≃* Dm) : ↥Y →* MulAut Dm :=
  (MulAut.congr β).toMonoidHom.comp ((V.normalizerMonoidHom).comp (Subgroup.inclusion hYV))

theorem rhoY_spec (V Y : Subgroup G) (hYV : Y ≤ Subgroup.normalizer (V : Set G)) (β : ↥V ≃* Dm)
    (y : ↥Y) (x : Dm) :
    ((β.symm (rhoY V Y hYV β y x) : ↥V) : G) = (y : G) * ((β.symm x : ↥V) : G) * (y : G)⁻¹ := by
  have h : rhoY V Y hYV β y x = β (V.normalizerMonoidHom (Subgroup.inclusion hYV y) (β.symm x)) := by
    simp [rhoY, MulAut.congr_apply]
  rw [h, MulEquiv.symm_apply_apply]
  exact V.normalizerMonoidHom_apply_apply_coe _ _

theorem nsc_perm [Finite G] {L Y V : Subgroup G} (hLY : L ≤ Y) (hYV : Y ≤ Subgroup.normalizer (V : Set G))
    (α : ↥L →* ↥(alternatingGroup (Fin 5))) (hα : Function.Surjective α) (β : ↥V ≃* Dm)
    (hβ : ∀ (l : ↥L) (v w : ↥V), (w : G) = l * v * l⁻¹ →
      Multiplicative.toAdd (β w) =
        vact ((α l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) (Multiplicative.toAdd (β v)))
    (hsub : IsSubnormal L Y) :
    ∀ y ∈ Y, ∃ σ : Equiv.Perm (Fin 5), ∀ v w : ↥V, (w : G) = y * v * y⁻¹ →
      Multiplicative.toAdd (β w) = vact σ (Multiplicative.toAdd (β v)) := by
  intro y hy
  have hsub' : IsSubnormal (L.subgroupOf Y) (⊤ : Subgroup ↥Y) := by
    have := isSubnormal_subgroupOf Y hsub
    rwa [Subgroup.subgroupOf_self] at this
  have hρ : (L.subgroupOf Y).map (rhoY V Y hYV β) = altImg := by
    have hL : ∀ l : ↥L, rhoY V Y hYV β ⟨l, hLY l.2⟩ = permHom ((α l : ↥(alternatingGroup (Fin 5))) :
        Equiv.Perm (Fin 5)) := by
      intro l
      refine MulEquiv.ext fun x => ?_
      have hw := rhoY_spec V Y hYV β ⟨l, hLY l.2⟩ x
      have h := hβ l (β.symm x) (β.symm (rhoY V Y hYV β ⟨l, hLY l.2⟩ x)) (by simpa using hw)
      simp only [MulEquiv.apply_symm_apply] at h
      rw [permHom_apply, ← h, ofAdd_toAdd]
    ext z
    constructor
    · rintro ⟨⟨l, hl⟩, hl', rfl⟩
      have hl'' : l ∈ L := hl'
      have := hL ⟨l, hl''⟩
      rw [this]
      exact mem_altImg (Equiv.Perm.mem_alternatingGroup.1 (α ⟨l, hl''⟩).2)
    · intro hz
      obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hz
      obtain ⟨l, hl⟩ := hα ⟨σ, hσ⟩
      refine ⟨⟨l, hLY l.2⟩, l.2, ?_⟩
      rw [hL l, hl]
  obtain ⟨σ, hσ⟩ := nsc (rhoY V Y hYV β) (L.subgroupOf Y) hsub' hρ ⟨y, hy⟩
  refine ⟨σ, fun v w hw => ?_⟩
  have h1 := rhoY_spec V Y hYV β ⟨y, hy⟩ (β v)
  rw [MulEquiv.symm_apply_apply] at h1
  have h2 : β.symm (rhoY V Y hYV β ⟨y, hy⟩ (β v)) = w := Subtype.ext (by rw [h1]; exact hw.symm)
  have h3 : rhoY V Y hYV β ⟨y, hy⟩ (β v) = β w := by rw [← h2]; simp
  rw [← h3, hσ, permHom_apply, toAdd_ofAdd]

end Geometric

end CFSG.QuasithinUnique.A5.Kc3NSC
