module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finset.Card

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Classif

open Equiv

theorem mem_of_blockTrivial {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {W : Subgroup (Equiv.Perm Ω)}
    {ω : Equiv.Perm Ω} (hω : ∀ x, ω (ω x) = x) (hmatch : ∀ x, ω x ≠ x)
    (hsw : ∀ x, Equiv.swap x (ω x) ∈ W) {c : Equiv.Perm Ω}
    (hc : ∀ z, c z = z ∨ c z = ω z) : c ∈ W := by
  suffices H : ∀ n : ℕ, ∀ c : Equiv.Perm Ω, (∀ z, c z = z ∨ c z = ω z) →
      (Finset.univ.filter (fun z => c z ≠ z)).card = n → c ∈ W from H _ c hc rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hcn hn
  by_cases h1 : ∀ z, c z = z
  · have hc1 : c = 1 := Equiv.ext fun x => by simp [h1 x]
    rw [hc1]
    exact W.one_mem
  · push Not at h1
    obtain ⟨z, hz⟩ := h1
    have hcz : c z = ω z := (hcn z).resolve_left hz
    have hsz : swap z (ω z) z = ω z := swap_apply_left _ _
    have hsωz : swap z (ω z) (ω z) = z := swap_apply_right _ _
    have hs_other : ∀ w, w ≠ z → w ≠ ω z → swap z (ω z) w = w :=
      fun w h1 h2 => swap_apply_of_ne_of_ne h1 h2
    have hsv : ∀ v, swap z (ω z) v = v ∨ swap z (ω z) v = ω v := by
      intro v
      by_cases hv1 : v = z
      · subst hv1
        exact Or.inr hsz
      by_cases hv2 : v = ω z
      · subst hv2
        exact Or.inr (by rw [hω]; exact hsωz)
      · exact Or.inl (hs_other v hv1 hv2)
    have hc' : ∀ w, (swap z (ω z) * c) w = w ∨ (swap z (ω z) * c) w = ω w := by
      intro w
      rw [Perm.mul_apply]
      rcases hcn w with h | h
      · rw [h]
        exact hsv w
      · rw [h]
        rcases hsv (ω w) with h' | h'
        · exact Or.inr h'
        · exact Or.inl (by rw [h', hω w])
    have hle : ∀ w, (swap z (ω z) * c) w ≠ w → c w ≠ w := by
      intro w hw hcw
      by_cases hwz : w = z
      · rw [hwz] at hcw
        exact hmatch z ((hcw.symm.trans hcz).symm)
      by_cases hwωz : w = ω z
      · have hcωz : c (ω z) = ω z := by rw [← hwωz]; exact hcw
        exact hmatch z (c.injective (hcz.trans hcωz.symm)).symm
      · rw [Perm.mul_apply] at hw
        apply hw
        rw [hcw]
        exact hs_other w hwz hwωz
    have hsub : Finset.univ.filter (fun w => (swap z (ω z) * c) w ≠ w) ⊆
        Finset.univ.filter (fun w => c w ≠ w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hle w hw
    have hlt : (Finset.univ.filter (fun w => (swap z (ω z) * c) w ≠ w)).card < n := by
      rw [← hn]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hsub]
      refine ⟨z, Finset.mem_filter.2 ⟨Finset.mem_univ _, hz⟩, ?_⟩
      intro hmem
      apply (Finset.mem_filter.1 hmem).2
      rw [Perm.mul_apply, hcz, hsωz]
    have hc'W : swap z (ω z) * c ∈ W := ih _ hlt (swap z (ω z) * c) hc' rfl
    have hprod := W.mul_mem (hsw z) hc'W
    rwa [← mul_assoc, swap_mul_self, one_mul] at hprod

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Classif
