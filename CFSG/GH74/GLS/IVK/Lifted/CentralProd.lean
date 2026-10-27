module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup

@[expose] def commProd {H : Type} [Group H] (A₁ A₂ : Subgroup H) (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) :
    ↥A₁ × ↥A₂ →* H :=
  A₁.subtype.noncommCoprod A₂.subtype (fun a b => hc a a.2 b b.2)

theorem commProd_apply {H : Type} [Group H] {A₁ A₂ : Subgroup H} (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (p : ↥A₁ × ↥A₂) : commProd A₁ A₂ hc p = (p.1 : H) * (p.2 : H) := rfl

theorem range_commProd {H : Type} [Group H] {A₁ A₂ : Subgroup H} (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) :
    (commProd A₁ A₂ hc).range = A₁ ⊔ A₂ := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    rw [commProd_apply]
    exact mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)
  · apply sup_le
    · intro a ha
      exact ⟨(⟨a, ha⟩, 1), by rw [commProd_apply]; simp⟩
    · intro b hb
      exact ⟨(1, ⟨b, hb⟩), by rw [commProd_apply]; simp⟩

theorem exists_mulEquiv_sup_of_commute {H H' : Type} [Group H] [Group H'] {A₁ A₂ : Subgroup H}
    {A₁' A₂' : Subgroup H'} (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hc' : ∀ a ∈ A₁', ∀ b ∈ A₂', a * b = b * a) (η₁ : ↥A₁ ≃* ↥A₁') (η₂ : ↥A₂ ≃* ↥A₂')
    (hker : ∀ (a : ↥A₁) (b : ↥A₂),
      (a : H) * (b : H) = 1 ↔ ((η₁ a : ↥A₁') : H') * ((η₂ b : ↥A₂') : H') = 1) :
    ∃ θ : ↥(A₁ ⊔ A₂) ≃* ↥(A₁' ⊔ A₂'),
      (∀ a : ↥A₁, ((θ ⟨a, mem_sup_left a.2⟩ : ↥(A₁' ⊔ A₂')) : H') = ((η₁ a : ↥A₁') : H')) ∧
      (∀ b : ↥A₂, ((θ ⟨b, mem_sup_right b.2⟩ : ↥(A₁' ⊔ A₂')) : H') = ((η₂ b : ↥A₂') : H')) := by
  classical
  let μ := commProd A₁ A₂ hc
  let μ' := commProd A₁' A₂' hc'
  let ι : ↥A₁ × ↥A₂ ≃* ↥A₁' × ↥A₂' := MulEquiv.prodCongr η₁ η₂
  have hkerm : (MonoidHom.ker μ).map ι.toMonoidHom = MonoidHom.ker μ' := by
    ext ⟨a', b'⟩
    constructor
    · rintro ⟨⟨a, b⟩, hab, h⟩
      have hab' : (a : H) * (b : H) = 1 := by
        have h0 : μ (a, b) = 1 := hab
        rwa [commProd_apply] at h0
      have h1 : ι (a, b) = (a', b') := h
      have h2 := (hker a b).1 hab'
      have e1 : a' = η₁ a := (congrArg Prod.fst h1).symm
      have e2 : b' = η₂ b := (congrArg Prod.snd h1).symm
      show μ' (a', b') = 1
      rw [commProd_apply, e1, e2]
      exact h2
    · intro h
      have h0 : μ' (a', b') = 1 := h
      rw [commProd_apply] at h0
      refine ⟨(η₁.symm a', η₂.symm b'), ?_,
        Prod.ext (η₁.apply_symm_apply a') (η₂.apply_symm_apply b')⟩
      show μ (η₁.symm a', η₂.symm b') = 1
      rw [commProd_apply]
      apply (hker _ _).2
      simpa using h0
  let q := QuotientGroup.congr (MonoidHom.ker μ) (MonoidHom.ker μ') ι hkerm
  let θ₀ : ↥μ.range ≃* ↥μ'.range :=
    (QuotientGroup.quotientKerEquivRange μ).symm.trans (q.trans (QuotientGroup.quotientKerEquivRange μ'))
  let θ : ↥(A₁ ⊔ A₂) ≃* ↥(A₁' ⊔ A₂') :=
    (MulEquiv.subgroupCongr (range_commProd hc).symm).trans
      (θ₀.trans (MulEquiv.subgroupCongr (range_commProd hc')))
  have hθ₀ : ∀ p : ↥A₁ × ↥A₂, ((θ₀ ⟨μ p, p, rfl⟩ : ↥μ'.range) : H') = μ' (ι p) := by
    intro p
    have h1 : (⟨μ p, p, rfl⟩ : ↥μ.range) = QuotientGroup.quotientKerEquivRange μ (QuotientGroup.mk p) :=
      rfl
    rw [h1]
    simp [θ₀, q]
    rfl
  have hθ : ∀ (g : H) (hg : g ∈ A₁ ⊔ A₂) (p : ↥A₁ × ↥A₂), μ p = g →
      ((θ ⟨g, hg⟩ : ↥(A₁' ⊔ A₂')) : H') = μ' (ι p) := by
    intro g hg p hp
    have : (MulEquiv.subgroupCongr (range_commProd hc).symm ⟨g, hg⟩ : ↥μ.range) = ⟨μ p, p, rfl⟩ := by
      apply Subtype.ext
      exact hp.symm
    show ((MulEquiv.subgroupCongr (range_commProd hc')
      (θ₀ (MulEquiv.subgroupCongr (range_commProd hc).symm ⟨g, hg⟩)) : ↥(A₁' ⊔ A₂')) : H') = _
    rw [this]
    exact hθ₀ p
  refine ⟨θ, fun a => ?_, fun b => ?_⟩
  · rw [hθ a (mem_sup_left a.2) (a, 1) (by rw [commProd_apply]; simp)]
    rw [commProd_apply]
    show ((η₁ a : ↥A₁') : H') * ((η₂ 1 : ↥A₂') : H') = _
    simp
  · rw [hθ b (mem_sup_right b.2) (1, b) (by rw [commProd_apply]; simp)]
    rw [commProd_apply]
    show ((η₁ 1 : ↥A₁') : H') * ((η₂ b : ↥A₂') : H') = _
    simp

end CFSG.GH74.GLS.IVK.Lifted
