module

public import CFSG.ClassicalInvolution.Q3.TL4D1MAGL
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Matrix

@[expose] def ept : Fin 3 → Fin 8 := ![1, 2, 4]

theorem bin_ept : ∀ k, bin (ept k) = Pi.single k 1 := by decide

theorem bin_zero : bin 0 = 0 := by decide

theorem sum_bin_plane : ∀ s ∈ affinePlanes, ∑ x ∈ s, bin x = 0 := by decide +kernel

theorem sum_bin_map {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ agl32) {s : Finset (Fin 8)}
    (hs : s ∈ affinePlanes) : ∑ x ∈ s, bin (σ x) = 0 := by
  have h := sum_bin_plane _ (hσ s hs).1
  rwa [Finset.sum_map] at h

theorem vec_four : ∀ u v w t : Fin 3 → ZMod 2, u + v + w + t = 0 →
    t = (v + u) + (w + u) + u := by
  intro u v w t h
  funext i
  have := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
  revert this
  generalize u i = a
  generalize v i = b
  generalize w i = c
  generalize t i = d
  revert a b c d
  decide

theorem vec_four' : ∀ u v w t z : Fin 3 → ZMod 2, u + v + w + t = 0 →
    t = (u + z) + (v + z) + (w + z) + z := by
  intro u v w t z h
  funext i
  have := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
  revert this
  generalize u i = a
  generalize v i = b
  generalize w i = c
  generalize t i = d
  generalize z i = e
  revert a b c d e
  decide

theorem exists_aperm_eq {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ agl32) :
    ∃ (A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2), aperm A b = σ := by
  set b := bin (σ 0) with hb
  set A₀ : Matrix (Fin 3) (Fin 3) (ZMod 2) := Matrix.of fun r k => bin (σ (ept k)) r + b r
  have hcol : ∀ k, A₀ *ᵥ bin (ept k) = bin (σ (ept k)) + b := by
    intro k
    rw [bin_ept, mulVec_single_one]
    rfl
  have hsum : ∀ a c d e : Fin 8, ({a, c, d, e} : Finset (Fin 8)) ∈ affinePlanes → a ∉ ({c, d, e} :
      Finset (Fin 8)) → c ∉ ({d, e} : Finset (Fin 8)) → d ≠ e →
      bin (σ a) + bin (σ c) + bin (σ d) + bin (σ e) = 0 := by
    intro a c d e hs ha hc hd
    have h := sum_bin_map hσ hs
    rwa [Finset.sum_insert ha, Finset.sum_insert hc, Finset.sum_pair hd, ← add_assoc,
      ← add_assoc] at h
  have h0 : bin (σ 0) = A₀ *ᵥ bin 0 + b := by rw [bin_zero, mulVec_zero, zero_add]
  have he : ∀ k, bin (σ (ept k)) = A₀ *ᵥ bin (ept k) + b := by
    intro k
    rw [hcol, add_assoc, two_smul_zero, add_zero]
  have h1 := he 0
  have h2 := he 1
  have h4 := he 2
  have hall : ∀ x : Fin 8, bin (σ x) = A₀ *ᵥ bin x + b := by
    intro x
    fin_cases x
    · exact h0
    · exact h1
    · exact h2
    · show bin (σ 3) = A₀ *ᵥ bin 3 + b
      have h := hsum 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
      rw [show bin 3 = bin (ept 0) + bin (ept 1) by decide, mulVec_add, hcol, hcol]
      exact vec_four _ _ _ _ h
    · exact h4
    · show bin (σ 5) = A₀ *ᵥ bin 5 + b
      have h := hsum 0 1 4 5 (by decide) (by decide) (by decide) (by decide)
      rw [show bin 5 = bin (ept 0) + bin (ept 2) by decide, mulVec_add, hcol, hcol]
      exact vec_four _ _ _ _ h
    · show bin (σ 6) = A₀ *ᵥ bin 6 + b
      have h := hsum 0 2 4 6 (by decide) (by decide) (by decide) (by decide)
      rw [show bin 6 = bin (ept 1) + bin (ept 2) by decide, mulVec_add, hcol, hcol]
      exact vec_four _ _ _ _ h
    · show bin (σ 7) = A₀ *ᵥ bin 7 + b
      have h := hsum 1 2 4 7 (by decide) (by decide) (by decide) (by decide)
      rw [show bin 7 = bin (ept 0) + bin (ept 1) + bin (ept 2) by decide, mulVec_add,
        mulVec_add, hcol, hcol, hcol]
      exact vec_four' _ _ _ _ _ h
  have hdet : A₀.det = 1 := by
    have hne : A₀.det ≠ 0 := by
      intro hd
      obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
      have hx := hall (binIdx v)
      rw [bin_binIdx, hAv, zero_add, hb] at hx
      have : binIdx v = 0 := σ.injective (bin_injective hx)
      apply hv
      rw [← bin_binIdx v, this, bin_zero]
    generalize A₀.det = d at hne
    revert d
    decide
  let A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨A₀, hdet⟩
  refine ⟨A, b, Equiv.ext fun x => bin_injective ?_⟩
  rw [aperm_apply, bin_aapply]
  exact (hall x).symm

theorem aperm_inj {A A' : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)} {b b' : Fin 3 → ZMod 2}
    (h : aperm A b = aperm A' b') : A = A' ∧ b = b' := by
  have hb : b = b' := by
    have := congrArg bin (Equiv.congr_fun h 0)
    rwa [aperm_apply, aperm_apply, bin_aapply, bin_aapply, bin_zero, mulVec_zero, mulVec_zero,
      zero_add, zero_add] at this
  refine ⟨Subtype.ext (Matrix.ext fun r k => ?_), hb⟩
  have := congrArg bin (Equiv.congr_fun h (ept k))
  rw [aperm_apply, aperm_apply, bin_aapply, bin_aapply, hb, add_left_inj, bin_ept,
    mulVec_single_one, mulVec_single_one] at this
  exact congrFun this r

end CFSG.ClassicalInvolution.Q3.TL4
