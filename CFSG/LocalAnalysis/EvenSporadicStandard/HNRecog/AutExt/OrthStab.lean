module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthFin
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv Equiv.Perm

theorem stab_hom_zero {K : Type*} [Group K] (ρ : K →* Perm (Fin 5))
    (hsign : ∀ k, sign (ρ k) = 1) (hsurj : ∀ g : Perm (Fin 5), sign g = 1 → ∃ k, ρ k = g)
    (f : K → ZMod 2) (hf : ∀ k k', ρ k 0 = 0 → f (k * k') = f k + f k')
    (hker : ∀ k, ρ k = 1 → f k = 0) :
    ∀ k, ρ k 0 = 0 → f k = 0 := by
  have hcube : ∀ (j : K) (c : Perm (Fin 5)), ρ j = c → c 0 = 0 → c ^ 3 = 1 → f j = 0 := by
    intro j c hjc hc0 hc3
    have h1 : ρ j 0 = 0 := by rw [hjc]; exact hc0
    have h2 : ρ (j * j) 0 = 0 := by
      rw [map_mul, hjc, Perm.mul_apply, hc0, hc0]
    have h3 : ρ (j * j * j) = 1 := by
      rw [map_mul, map_mul, hjc, ← pow_three', hc3]
    have h4 : f (j * j * j) = f j + f j + f j := by
      rw [hf (j * j) j h2, hf j j h1]
    have h5 : f (j * j * j) = 0 := hker _ h3
    rw [h4, CharTwo.add_self_eq_zero, zero_add] at h5
    exact h5
  intro k hk
  obtain ⟨a, b, ha, hb, ha0, hb0, ha3, hb3, hkab⟩ := stab_gen5 (ρ k) (hsign k) hk
  obtain ⟨ka, hka⟩ := hsurj a ha
  obtain ⟨kb, hkb⟩ := hsurj b hb
  have hfa : f ka = 0 := hcube ka a hka ha0 ha3
  have hfb : f kb = 0 := hcube kb b hkb hb0 hb3
  have hka0 : ρ ka 0 = 0 := by rw [hka]; exact ha0
  have hkab0 : ρ (ka * kb) 0 = 0 := by
    rw [map_mul, hka, hkb, Perm.mul_apply, hb0, ha0]
  have hm : ρ ((ka * kb)⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, map_mul, hka, hkb, ← hkab, inv_mul_cancel]
  have hfm : f ((ka * kb)⁻¹ * k) = 0 := hker _ hm
  have hk' : k = (ka * kb) * ((ka * kb)⁻¹ * k) := by group
  rw [hk', hf _ _ hkab0, hf _ _ hka0, hfa, hfb, hfm]
  simp

end CFSG.EvenSporadicStandard.HNRecog.Section4
