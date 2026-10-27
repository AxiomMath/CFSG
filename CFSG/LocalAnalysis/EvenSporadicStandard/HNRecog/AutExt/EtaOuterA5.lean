module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Factors

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.EtaGz

open Equiv Equiv.Perm CFSG.EvenSporadicStandard.HNRecog.Fpf
  CFSG.EvenSporadicStandard.HNRecog.Swap

theorem exists_outer_aut :
    ∃ c : A5 ≃* A5, ¬ ∃ p : A5, ∀ y : A5, c y = p * y * p⁻¹ := by
  refine ⟨MulAut.conjNormal (swap (0 : Fin 5) 1), ?_⟩
  have key : ¬ ∃ p : A5, ∀ y : A5,
      (swap (0 : Fin 5) 1 * (y : Perm (Fin 5)) * (swap (0 : Fin 5) 1)⁻¹ : Perm (Fin 5)) =
        (p : Perm (Fin 5)) * (y : Perm (Fin 5)) * (p : Perm (Fin 5))⁻¹ := by
    decide +kernel
  rintro ⟨p, hp⟩
  exact key ⟨p, fun y => by simpa using congrArg Subtype.val (hp y)⟩

@[expose] def swapAut (x₀ : A5) : A5 × A5 ≃* A5 × A5 where
  toFun p := (x₀ * p.2 * x₀⁻¹, x₀⁻¹ * p.1 * x₀)
  invFun p := (x₀ * p.2 * x₀⁻¹, x₀⁻¹ * p.1 * x₀)
  left_inv p := by apply Prod.ext <;> group
  right_inv p := by apply Prod.ext <;> group
  map_mul' p q := by
    apply Prod.ext <;> simp only [Prod.fst_mul, Prod.snd_mul] <;> group

theorem swapAut_apply (x₀ : A5) (p : A5 × A5) :
    swapAut x₀ p = (x₀ * p.2 * x₀⁻¹, x₀⁻¹ * p.1 * x₀) := rfl

theorem eq_id_or_eq_swapAut_of_fix (x₀ : A5) (Ψ : A5 × A5 ≃* A5 × A5)
    (hΨ : ∀ q : A5, Ψ (x₀ * q * x₀⁻¹, q) = (x₀ * q * x₀⁻¹, q)) :
    (∀ p, Ψ p = p) ∨ ∀ p, Ψ p = swapAut x₀ p := by
  have hΨ' : ∀ q : A5, Ψ ((x₀ * q * x₀⁻¹, 1) * (1, q)) = (x₀ * q * x₀⁻¹, q) := fun q => by
    have : ((x₀ * q * x₀⁻¹, 1) * (1, q) : A5 × A5) = (x₀ * q * x₀⁻¹, q) := by simp
    rw [this]
    exact hΨ q
  have hconj : ∀ a : A5, x₀ * (x₀⁻¹ * a * x₀) * x₀⁻¹ = a := fun a => by group
  have hprod : ∀ p : A5 × A5, p = (p.1, 1) * (1, p.2) := fun p => by simp
  rcases exists_preserves_or_swaps Ψ with ⟨⟨h1, h2⟩, -⟩ | ⟨⟨h1, h2⟩, -⟩
  · left
    have key : ∀ q : A5, Ψ (x₀ * q * x₀⁻¹, 1) = (x₀ * q * x₀⁻¹, 1) ∧ Ψ (1, q) = (1, q) := by
      intro q
      obtain ⟨y', hy'⟩ := h2 q
      obtain ⟨x', hx'⟩ := h1 (x₀ * q * x₀⁻¹)
      have h := hΨ' q
      rw [map_mul, hx', hy'] at h
      simp only [Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.injEq] at h
      rw [hx', hy', h.1, h.2]
      exact ⟨rfl, rfl⟩
    have hA : ∀ a : A5, Ψ (a, 1) = (a, 1) := fun a => by
      have := (key (x₀⁻¹ * a * x₀)).1
      rwa [hconj a] at this
    intro p
    rw [hprod p, map_mul, hA, (key p.2).2]
  · right
    have key : ∀ q : A5, Ψ (x₀ * q * x₀⁻¹, 1) = (1, q) ∧ Ψ (1, q) = (x₀ * q * x₀⁻¹, 1) := by
      intro q
      obtain ⟨x', hx'⟩ := h2 q
      obtain ⟨y', hy'⟩ := h1 (x₀ * q * x₀⁻¹)
      have h := hΨ' q
      rw [map_mul, hx', hy'] at h
      simp only [Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.injEq] at h
      rw [hx', hy', h.1, h.2]
      exact ⟨rfl, rfl⟩
    have hA : ∀ a : A5, Ψ (a, 1) = (1, x₀⁻¹ * a * x₀) := fun a => by
      have := (key (x₀⁻¹ * a * x₀)).1
      rwa [hconj a] at this
    intro p
    calc Ψ p = Ψ ((p.1, 1) * (1, p.2)) := by rw [← hprod p]
      _ = Ψ (p.1, 1) * Ψ (1, p.2) := map_mul _ _ _
      _ = (1, x₀⁻¹ * p.1 * x₀) * (x₀ * p.2 * x₀⁻¹, 1) := by rw [hA, (key p.2).2]
      _ = swapAut x₀ p := by rw [swapAut_apply]; simp

theorem prod_ne_conj (c χ : A5 ≃* A5) (hc : ¬ ∃ p : A5, ∀ y : A5, c y = p * y * p⁻¹)
    (p : A5 × A5) : ¬ ∀ g : A5 × A5, (c g.1, χ g.2) = p * g * p⁻¹ := by
  intro h
  refine hc ⟨p.1, fun y => ?_⟩
  have := congrArg Prod.fst (h (y, 1))
  simpa using this

theorem prod_ne_conj_swapAut (c χ : A5 ≃* A5) (x₀ : A5) (p : A5 × A5) :
    ¬ ∀ g : A5 × A5, (c g.1, χ g.2) = p * swapAut x₀ g * p⁻¹ := by
  intro h
  have h1 : ∀ a : A5, c a = 1 := by
    intro a
    have := congrArg Prod.fst (h (a, 1))
    simpa [swapAut_apply] using this
  have h2 : (⟨swap (0 : Fin 5) 1 * swap (1 : Fin 5) 2,
      mem_alternatingGroup.2 (by decide)⟩ : A5) = 1 := by
    apply c.injective
    rw [h1, map_one]
  have h3 : (swap (0 : Fin 5) 1 * swap (1 : Fin 5) 2 : Perm (Fin 5)) = 1 :=
    congrArg Subtype.val h2
  revert h3
  decide

end CFSG.EvenSporadicStandard.HNRecog.Section4.EtaGz
