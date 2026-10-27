module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthFin
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv Equiv.Perm

theorem shapiro5 {K : Type*} [Group K] (ρ : K →* Perm (Fin 5))
    (htrans : ∀ i j : Fin 5, ∃ k : K, ρ k i = j) (D : K → Fv5)
    (hD : ∀ g h, D (g * h) = D g + fv5Act (ρ g) (D h))
    (hstab : ∀ k, ρ k 0 = 0 → D k 0 = 0) :
    ∃ c : Fv5, Fv5Even c ∧ ∀ g, D g = c + fv5Act (ρ g) c := by
  choose b hb using fun i : Fin 5 => htrans 0 i
  have hD' : ∀ g h i, D (g * h) i = D g i + D h ((ρ g)⁻¹ i) := fun g h i => by
    rw [hD]; rfl
  have hinv : ∀ i, (ρ (b i))⁻¹ i = 0 := fun i => by
    have h : (ρ (b i))⁻¹ (ρ (b i) 0) = 0 := by
      rw [Equiv.Perm.inv_def]; exact Equiv.symm_apply_apply _ _
    rwa [hb] at h
  have key : ∀ (g : K) (i : Fin 5),
      D g i = D (b i) i + D (b ((ρ g)⁻¹ i)) ((ρ g)⁻¹ i) := by
    intro g i
    have hgj : ρ g ((ρ g)⁻¹ i) = i := by
      rw [Equiv.Perm.inv_def]; exact Equiv.apply_symm_apply _ _
    obtain ⟨s, hs⟩ : ∃ s : K, s = (b i)⁻¹ * g * b ((ρ g)⁻¹ i) := ⟨_, rfl⟩
    have hs0 : ρ s 0 = 0 := by
      rw [hs, map_mul, map_mul, map_inv, Perm.mul_apply, Perm.mul_apply, hb, hgj]
      exact hinv i
    have h1 : b i * s = g * b ((ρ g)⁻¹ i) := by rw [hs]; group
    have h2 := congrArg (fun k => D k i) h1
    simp only [hD'] at h2
    rw [hinv i, hstab _ hs0] at h2
    have h3 : ∀ x y z : ZMod 2, x + 0 = y + z → y = x + z := by decide
    exact h3 _ _ _ h2
  set c : Fv5 := fun i => D (b i) i with hc
  have hcob : ∀ g, D g = c + fv5Act (ρ g) c := fun g => funext fun i => key g i
  refine ⟨fun i => c i + ∑ k, c k, ?_, fun g => ?_⟩
  · unfold Fv5Even
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    generalize ∑ k, c k = s
    revert s
    decide +kernel
  · funext i
    have h := key g i
    have h4 : ∀ x y z w : ZMod 2, x = y + z → x = (y + w) + (z + w) := by decide
    exact h4 _ _ _ _ h

end CFSG.EvenSporadicStandard.HNRecog.Section4
