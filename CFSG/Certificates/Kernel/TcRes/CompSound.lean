module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.KC.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus Matrix

variable {τ : Tag} {M M' : Type*} [CommGroup M] [CommGroup M']

theorem eqvGen_map' {α β : Type*} {R : α → α → Prop} {R' : β → β → Prop} (f : α → β)
    (hf : ∀ x y, R x y → R' (f x) (f y)) {x y : α} (h : Relation.EqvGen R x y) :
    Relation.EqvGen R' (f x) (f y) := by
  induction h with
  | rel x y h => exact Relation.EqvGen.rel _ _ (hf x y h)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem exists_componentRoots_perm {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hker : kernelRoots χ' = ρ '' kernelRoots χ)
    (hform : ∀ α ∈ kernelRoots χ, ∀ β ∈ kernelRoots χ, iform (ρ α) (ρ β) = iform α β)
    (i : KernelComponent χ) :
    ∃ i' : KernelComponent χ', componentRoots χ' i' = ρ '' componentRoots χ i := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep i
  have hmem : ∀ {α}, α ∈ kernelRoots χ → ρ α ∈ kernelRoots χ' := fun h => hker ▸ ⟨_, h, rfl⟩
  have hmem' : ∀ {β}, β ∈ kernelRoots χ' → ρ.symm β ∈ kernelRoots χ := by
    intro β h
    rw [hker] at h
    obtain ⟨a, ha, rfl⟩ := h
    simpa using ha
  let F : kernelRoots χ → kernelRoots χ' := fun a => ⟨ρ a, hmem a.2⟩
  let G : kernelRoots χ' → kernelRoots χ := fun b => ⟨ρ.symm b, hmem' b.2⟩
  have hF : ∀ a b : kernelRoots χ,
      (a : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (b : Fin τ.rank → ℤ)) ≠ 0 →
      ((F a : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (F b : Fin τ.rank → ℤ))) ≠ 0 := by
    intro a b h
    rw [dotProduct_mulVec_eq_iform] at h ⊢
    rw [hform _ a.2 _ b.2]
    exact h
  have hG : ∀ a b : kernelRoots χ',
      (a : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (b : Fin τ.rank → ℤ)) ≠ 0 →
      ((G a : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (G b : Fin τ.rank → ℤ))) ≠ 0 := by
    intro a b h
    rw [dotProduct_mulVec_eq_iform] at h ⊢
    have := hform _ (G a).2 _ (G b).2
    simp only [G, Equiv.apply_symm_apply] at this
    rw [← this]
    exact h
  refine ⟨⟦F x⟧, ?_⟩
  ext β
  constructor
  · rintro ⟨hβ, hi⟩
    have hE := eqvGen_map' (R' := fun α β : kernelRoots χ =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) G hG
      (Quotient.exact hi)
    have hGF : G (F x) = x := Subtype.ext (by simp [F, G])
    refine ⟨ρ.symm β, ⟨hmem' hβ, ?_⟩, by simp⟩
    rw [← hGF]
    exact Quotient.sound hE
  · rintro ⟨α, ⟨hα, hi⟩, rfl⟩
    exact ⟨hmem hα, Quotient.sound (eqvGen_map' (R' := fun α β : kernelRoots χ' =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) F hF
      (Quotient.exact hi))⟩

theorem eq_of_mem_componentRoots {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {i j : KernelComponent χ} {α : Fin τ.rank → ℤ} (hi : α ∈ componentRoots χ i)
    (hj : α ∈ componentRoots χ j) : i = j := by
  obtain ⟨h1, rfl⟩ := hi
  obtain ⟨h2, rfl⟩ := hj
  rfl

theorem exists_componentRoots_iterate {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hker : kernelRoots χ = ρ '' kernelRoots χ)
    (hform : ∀ α ∈ kernelRoots χ, ∀ β ∈ kernelRoots χ, iform (ρ α) (ρ β) = iform α β)
    (i : KernelComponent χ) (s : ℕ) :
    ∃ i' : KernelComponent χ, componentRoots χ i' = (⇑ρ)^[s] '' componentRoots χ i := by
  induction s with
  | zero => exact ⟨i, by simp⟩
  | succ s ih =>
    obtain ⟨i', hi'⟩ := ih
    obtain ⟨i'', hi''⟩ := exists_componentRoots_perm ρ hker hform i'
    refine ⟨i'', ?_⟩
    rw [hi'', hi', Set.image_image, Function.iterate_succ']
    rfl

theorem componentOrbitLength_eq_of_first {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hker : kernelRoots χ = ρ '' kernelRoots χ)
    (hform : ∀ α ∈ kernelRoots χ, ∀ β ∈ kernelRoots χ, iform (ρ α) (ρ β) = iform α β)
    (i : KernelComponent χ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots χ i) {e : ℕ}
    (he : 0 < e) (hin : (⇑ρ)^[e] γ ∈ componentRoots χ i)
    (hout : ∀ s, 0 < s → s < e → (⇑ρ)^[s] γ ∉ componentRoots χ i) :
    componentOrbitLength ρ (componentRoots χ i) = e := by
  have key : ∀ s, ((⇑ρ)^[s] '' componentRoots χ i = componentRoots χ i ↔
      (⇑ρ)^[s] γ ∈ componentRoots χ i) := by
    intro s
    constructor
    · intro h
      rw [← h]
      exact Set.mem_image_of_mem _ hγ
    · intro h
      obtain ⟨i', hi'⟩ := exists_componentRoots_iterate ρ hker hform i s
      have h1 : (⇑ρ)^[s] γ ∈ componentRoots χ i' := hi' ▸ Set.mem_image_of_mem _ hγ
      rw [← hi', eq_of_mem_componentRoots h1 h]
  have hmem : e ∈ {s : ℕ | 0 < s ∧ (⇑ρ)^[s] '' componentRoots χ i = componentRoots χ i} :=
    ⟨he, (key e).2 hin⟩
  unfold componentOrbitLength
  refine le_antisymm (Nat.sInf_le hmem) ?_
  obtain ⟨h1, h2⟩ := Nat.sInf_mem ⟨e, hmem⟩
  by_contra hlt
  exact hout _ h1 (by omega) ((key _).1 h2)

theorem class_of_path
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {vec : ℕ → Fin τ.rank → ℤ}
    {Φ : Set ℕ} (hΦ : vec '' Φ = kernelRoots χ) {a b : ℕ}
    (hab : Relation.ReflTransGen (fun a b => a ∈ Φ ∧ b ∈ Φ ∧ iform (vec a) (vec b) ≠ 0) a b)
    (ha : vec a ∈ kernelRoots χ) :
    ∃ hb : vec b ∈ kernelRoots χ,
      (⟦⟨vec b, hb⟩⟧ : KernelComponent χ) = ⟦⟨vec a, ha⟩⟧ := by
  induction hab with
  | refl => exact ⟨ha, rfl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hcls⟩ := ih
    have hc : vec c ∈ kernelRoots χ := by
      rw [← hΦ]
      exact Set.mem_image_of_mem _ hbc.2.1
    refine ⟨hc, Eq.trans ?_ hcls⟩
    apply mk_eq_of_iform_ne_zero
    rw [CFSG.LieType.Steinberg.Adjoint.iform_comm]
    exact hbc.2.2

theorem exists_componentRoots_eq_image
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {vec : ℕ → Fin τ.rank → ℤ} {Φ ψ : Set ℕ} (hΦ : vec '' Φ = kernelRoots χ) (hψΦ : ψ ⊆ Φ)
    {rt : ℕ} (hrt : rt ∈ ψ)
    (hconn : ∀ g ∈ ψ, Relation.ReflTransGen
      (fun a b => a ∈ ψ ∧ b ∈ ψ ∧ iform (vec a) (vec b) ≠ 0) rt g)
    (hcl : ∀ g ∈ ψ, ∀ h ∈ Φ, iform (vec g) (vec h) ≠ 0 → h ∈ ψ) :
    ∃ i : KernelComponent χ, componentRoots χ i = vec '' ψ := by
  have hr0 : vec rt ∈ kernelRoots χ := by
    rw [← hΦ]
    exact Set.mem_image_of_mem _ (hψΦ hrt)
  refine ⟨⟦⟨vec rt, hr0⟩⟧, ?_⟩
  ext α
  constructor
  · rintro ⟨hα, hcls⟩
    have hE := Quotient.exact hcls
    have key : ∀ a b : kernelRoots χ, Relation.EqvGen (fun α β : kernelRoots χ =>
        (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) a b →
        ((a : Fin τ.rank → ℤ) ∈ vec '' ψ ↔ (b : Fin τ.rank → ℤ) ∈ vec '' ψ) := by
      intro a b h
      induction h with
      | rel x y hxy =>
        rw [dotProduct_mulVec_eq_iform] at hxy
        obtain ⟨gx, hgx, hx⟩ : (x : Fin τ.rank → ℤ) ∈ vec '' Φ := by rw [hΦ]; exact x.2
        obtain ⟨gy, hgy, hy⟩ : (y : Fin τ.rank → ℤ) ∈ vec '' Φ := by rw [hΦ]; exact y.2
        constructor
        · rintro ⟨g, hg, hgv⟩
          refine ⟨gy, hcl g hg gy hgy ?_, hy⟩
          rw [hgv, hy]
          exact hxy
        · rintro ⟨g, hg, hgv⟩
          refine ⟨gx, hcl g hg gx hgx ?_, hx⟩
          rw [hgv, hx, CFSG.LieType.Steinberg.Adjoint.iform_comm]
          exact hxy
      | refl x => exact Iff.rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    exact (key _ _ hE).2 ⟨rt, hrt, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    have hmono : ∀ g', Relation.ReflTransGen
        (fun a b => a ∈ ψ ∧ b ∈ ψ ∧ iform (vec a) (vec b) ≠ 0) rt g' → Relation.ReflTransGen
        (fun a b => a ∈ Φ ∧ b ∈ Φ ∧ iform (vec a) (vec b) ≠ 0) rt g' := by
      intro g' hp
      induction hp with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ h ih => exact Relation.ReflTransGen.tail ih ⟨hψΦ h.1, hψΦ h.2.1, h.2.2⟩
    have hpath' := hmono g (hconn g hg)
    obtain ⟨hb, hcls⟩ := class_of_path hΦ hpath' hr0
    exact ⟨hb, hcls⟩

theorem componentOrbitLength_eq_one_of_paths
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {vec : ℕ → Fin τ.rank → ℤ} {Φ : Set ℕ} {ph : ℕ → ℕ} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hker : kernelRoots χ = ρ '' kernelRoots χ)
    (hform : ∀ α ∈ kernelRoots χ, ∀ β ∈ kernelRoots χ, iform (ρ α) (ρ β) = iform α β)
    (hΦ : vec '' Φ = kernelRoots χ) (hph : ∀ g ∈ Φ, vec (ph g) = ρ (vec g))
    (hrec : ∀ g ∈ Φ, ∃ r ∈ Φ,
      Relation.ReflTransGen (fun a b => a ∈ Φ ∧ b ∈ Φ ∧ iform (vec a) (vec b) ≠ 0) r g ∧
      Relation.ReflTransGen (fun a b => a ∈ Φ ∧ b ∈ Φ ∧ iform (vec a) (vec b) ≠ 0) r (ph r))
    (i : KernelComponent χ) : componentOrbitLength ρ (componentRoots χ i) = 1 := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep i
  obtain ⟨g, hg, hgx⟩ : (x : Fin τ.rank → ℤ) ∈ vec '' Φ := by rw [hΦ]; exact x.2
  obtain ⟨r, hr, hrg, hrr⟩ := hrec g hg
  have hr0 : vec r ∈ kernelRoots χ := by
    rw [← hΦ]
    exact Set.mem_image_of_mem _ hr
  obtain ⟨hg', hcg⟩ := class_of_path hΦ hrg hr0
  obtain ⟨hp', hcp⟩ := class_of_path hΦ hrr hr0
  have hxg : (⟦x⟧ : KernelComponent χ) = ⟦⟨vec g, hg'⟩⟧ := by
    congr 1
    exact Subtype.ext hgx.symm
  have hrmem : vec r ∈ componentRoots χ ⟦x⟧ := ⟨hr0, by rw [hxg, hcg]⟩
  refine componentOrbitLength_eq_of_first ρ hker hform ⟦x⟧ hrmem one_pos ?_
    (fun s h1 h2 => absurd h2 (by omega))
  rw [Function.iterate_one, ← hph r hr]
  exact ⟨hp', by rw [hxg, hcp, ← hcg]⟩

end CFSG.KC.TcRes

end
