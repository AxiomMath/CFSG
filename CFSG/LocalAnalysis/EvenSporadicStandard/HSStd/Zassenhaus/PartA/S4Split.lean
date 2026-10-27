module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S4Core

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath
open scoped commutatorElement

theorem exists_mulEquiv_of_range {K H A : Type*} [Group K] [Group H] [Group A] (f : K →* H)
    (β : A →* H) (hβ : Function.Injective β) (hmem : ∀ k, f k ∈ β.range)
    (hinj : Function.Injective f) (hsurj : ∀ a, ∃ k, f k = β a) :
    ∃ e : K ≃* A, ∀ k, f k = β (e k) := by
  let θ : K →* A := (MonoidHom.ofInjective hβ).symm.toMonoidHom.comp
    (MonoidHom.codRestrict f β.range hmem)
  have hθ : ∀ k, β (θ k) = f k := by
    intro k
    have e := congrArg Subtype.val
      ((MonoidHom.ofInjective hβ).apply_symm_apply ⟨f k, hmem k⟩)
    rw [MonoidHom.ofInjective_apply] at e
    exact e
  have hθinj : Function.Injective θ := by
    intro a b hab
    apply hinj
    rw [← hθ, ← hθ, hab]
  have hθsurj : Function.Surjective θ := by
    intro a
    obtain ⟨k, hk⟩ := hsurj a
    refine ⟨k, hβ ?_⟩
    rw [hθ, hk]
  exact ⟨MulEquiv.ofBijective θ ⟨hθinj, hθsurj⟩, fun k => (hθ k).symm⟩

theorem s4_split {C : Type} [Group C] [Finite C]
    (O Y : Subgroup C) [O.Normal] (hOodd : Odd (Nat.card O)) (hYc : Y ≤ center C)
    (hOcomm : ∀ o₁ ∈ O, ∀ o₂ ∈ O, ⁅o₁, o₂⁆ ∈ Y) {t : C} (htt : t * t = 1)
    (hOinv : ∀ o ∈ O, t * o * t⁻¹ * o ∈ Y) (f : C →* Wr2 (Equiv.Perm (Fin 5)))
    (hker : ∀ g, f g = 1 ↔ g ∈ O) (ht : f t = tau)
    (hbase : ∀ x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5), ∃ g, f g = betaHom x) :
    ∃ K₁ K₂ : Subgroup C,
      (∀ k ∈ K₁, ∀ o ∈ O, k * o = o * k) ∧
      (∀ k ∈ K₁, ∀ k' ∈ K₂, k * k' = k' * k) ∧
      (∀ k ∈ K₁, k ∈ K₂ → k = 1) ∧
      (∀ k ∈ K₁, t * k * t⁻¹ ∈ K₂) ∧ (∀ k ∈ K₂, t * k * t⁻¹ ∈ K₁) ∧
      (∃ e : ↥K₁ ≃* alternatingGroup (Fin 5), ∀ k : ↥K₁, f k = betaHom (e k, 1)) ∧
      (∀ x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5), ∀ g, f g = betaHom x →
        ∃ o ∈ O, ∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, g = o * k₁ * k₂) ∧
      (∀ x ∈ K₁ ⊔ K₂, x ∈ O → x = 1) := by
  obtain ⟨R, hR1, hR2, hR3, hR4, hR5⟩ := s4_core O Y hOodd hYc hOcomm htt hOinv f hker ht hbase
  let β₁ : alternatingGroup (Fin 5) →* Wr2 (Equiv.Perm (Fin 5)) :=
    betaHom.comp (MonoidHom.inl _ _)
  let β₂ : alternatingGroup (Fin 5) →* Wr2 (Equiv.Perm (Fin 5)) :=
    betaHom.comp (MonoidHom.inr _ _)
  have hβ₁ : Function.Injective β₁ := fun a b h => (Prod.mk.inj (betaHom_injective h)).1
  have hconjf : ∀ g : C, f (t * g * t⁻¹) = tau * f g * tau⁻¹ := by
    intro g
    rw [map_mul, map_mul, map_inv, ht]
  have hR3' : ∀ r ∈ R, f r = 1 → r = 1 := fun r hr h => hR3 r hr ((hker r).1 h)
  let K₁ : Subgroup C := R ⊓ β₁.range.comap f
  let K₂ : Subgroup C := R ⊓ β₂.range.comap f
  have hK1 : ∀ k ∈ K₁, ∃ a, f k = betaHom (a, 1) := fun k hk => by
    obtain ⟨a, ha⟩ := (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hk).2 : f k ∈ β₁.range)
    exact ⟨a, ha.symm⟩
  have hK2 : ∀ k ∈ K₂, ∃ b, f k = betaHom (1, b) := fun k hk => by
    obtain ⟨b, hb⟩ := (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hk).2 : f k ∈ β₂.range)
    exact ⟨b, hb.symm⟩
  have hK1R : K₁ ≤ R := inf_le_left
  have hK2R : K₂ ≤ R := inf_le_left
  have hmk1 : ∀ r ∈ R, ∀ a, f r = betaHom (a, 1) → r ∈ K₁ := fun r hr a h =>
    Subgroup.mem_inf.2 ⟨hr, Subgroup.mem_comap.2 ⟨a, h.symm⟩⟩
  have hmk2 : ∀ r ∈ R, ∀ b, f r = betaHom (1, b) → r ∈ K₂ := fun r hr b h =>
    Subgroup.mem_inf.2 ⟨hr, Subgroup.mem_comap.2 ⟨b, h.symm⟩⟩
  refine ⟨K₁, K₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk o ho
    exact hR1 k (hK1R hk) o ho
  · intro k hk k' hk'
    obtain ⟨a, ha⟩ := hK1 k hk
    obtain ⟨b, hb⟩ := hK2 k' hk'
    have h1 : f ⁅k, k'⁆ = 1 := by
      rw [map_commutatorElement, ha, hb, ← map_commutatorElement]
      have : ⁅(((a, 1) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5))),
          ((1, b) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5))⁆ = 1 :=
        Prod.ext (by simp [commutatorElement_def]) (by simp [commutatorElement_def])
      rw [this, map_one]
    have h2 : ⁅k, k'⁆ = 1 := hR3' _ (Subgroup.commutator_le_self R
      (commutator_mem_commutator (hK1R hk) (hK2R hk'))) h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  · intro k hk hk'
    obtain ⟨a, ha⟩ := hK1 k hk
    obtain ⟨b, hb⟩ := hK2 k hk'
    have h1 : betaHom (a, 1) = betaHom (1, b) := ha.symm.trans hb
    have h2 := betaHom_injective h1
    have h3 : a = 1 := (Prod.mk.inj h2).1
    have h4 : f k = 1 := by rw [ha, h3, ← map_one betaHom]; rfl
    exact hR3' k (hK1R hk) h4
  · intro k hk
    obtain ⟨a, ha⟩ := hK1 k hk
    refine hmk2 _ (hR2 k (hK1R hk)) a ?_
    rw [hconjf, ha]
    exact tau_betaHom (a, 1)
  · intro k hk
    obtain ⟨b, hb⟩ := hK2 k hk
    refine hmk1 _ (hR2 k (hK2R hk)) b ?_
    rw [hconjf, hb]
    exact tau_betaHom (1, b)
  · refine exists_mulEquiv_of_range (f.comp K₁.subtype) β₁ hβ₁ ?_ ?_ ?_
    · intro k
      obtain ⟨a, ha⟩ := hK1 k.1 k.2
      exact ⟨a, ha.symm⟩
    · intro a b hab
      apply Subtype.ext
      have h1 : f (a : C) = f (b : C) := hab
      have h2 : ((a : C)⁻¹ * b) = 1 := by
        refine hR3' _ (R.mul_mem (R.inv_mem (hK1R a.2)) (hK1R b.2)) ?_
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      exact inv_mul_eq_one.1 h2
    · intro a
      obtain ⟨r, hr, hra⟩ := hR5 (a, 1)
      exact ⟨⟨r, hmk1 r hr a hra⟩, hra⟩
  · intro x g hg
    obtain ⟨a, b⟩ := x
    obtain ⟨r₁, hr₁, hr₁a⟩ := hR5 (a, 1)
    obtain ⟨r₂, hr₂, hr₂b⟩ := hR5 (1, b)
    have hprod : f (g * (r₁ * r₂)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, hg, hr₁a, hr₂b, ← map_mul]
      have : ((a, 1) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) * (1, b) = (a, b) := by
        simp
      rw [this, mul_inv_cancel]
    refine ⟨g * (r₁ * r₂)⁻¹, (hker _).1 hprod, r₁, hmk1 r₁ hr₁ a hr₁a, r₂, hmk2 r₂ hr₂ b hr₂b, ?_⟩
    group
  · intro x hx hxO
    have : x ∈ R := sup_le hK1R hK2R hx
    exact hR3 x this hxO

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
