module

public import Mathlib.GroupTheory.Perm.Cycle.Type
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterKGA8TAlt

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open Equiv Equiv.Perm

theorem comm_decomp_of_isConj {n : ℕ} {s s₀ u₀ v₀ : Perm (Fin n)} (hc : IsConj s s₀)
    (hu : sign u₀ = 1) (hv : sign v₀ = 1) (hus : u₀ * s₀ = s₀ * u₀) (hvs : v₀ * s₀ = s₀ * v₀)
    (hcomm : u₀ * v₀ * u₀⁻¹ * v₀⁻¹ = s₀) :
    ∃ u v : Perm (Fin n), sign u = 1 ∧ sign v = 1 ∧ u * s = s * u ∧ v * s = s * v ∧
      u * v * u⁻¹ * v⁻¹ = s := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  let φ : Perm (Fin n) →* Perm (Fin n) := (MulAut.conj c⁻¹ : Perm (Fin n) ≃* Perm (Fin n))
  have hφs : φ s₀ = s := by
    show c⁻¹ * s₀ * c⁻¹⁻¹ = s
    rw [← hc]
    group
  have hsign : ∀ x : Perm (Fin n), sign x = 1 → sign (φ x) = 1 := by
    intro x hx
    show sign (c⁻¹ * x * c⁻¹⁻¹) = 1
    rw [map_mul, map_mul, hx, mul_one, mul_comm, ← map_mul, inv_mul_cancel, map_one]
  refine ⟨φ u₀, φ v₀, hsign _ hu, hsign _ hv, ?_, ?_, ?_⟩
  · rw [← hφs, ← map_mul, ← map_mul, hus]
  · rw [← hφs, ← map_mul, ← map_mul, hvs]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hcomm, hφs]

private theorem ct_swap {α : Type*} [Fintype α] [DecidableEq α] {x y : α} (h : x ≠ y) :
    (swap x y).cycleType = {2} :=
  isSwap_iff_cycleType.1 (swap_isSwap_iff.2 h)

private theorem ct_two {α : Type*} [Fintype α] [DecidableEq α] {a b c d : α}
    (h : [a, b, c, d].Nodup) : (swap a b * swap c d).cycleType = Multiset.replicate 2 2 :=
  cycleType_swap_mul_swap_of_nodup h

private theorem ct_four {α : Type*} [Fintype α] [DecidableEq α] {a b c d e f g h : α}
    (h1 : [a, b, c, d].Nodup) (h2 : [a, b, e, f].Nodup) (h3 : [c, d, e, f].Nodup)
    (h4 : [a, b, g, h].Nodup) (h5 : [c, d, g, h].Nodup) (h6 : [e, f, g, h].Nodup) :
    (swap a b * swap c d * swap e f * swap g h).cycleType = Multiset.replicate 4 2 := by
  have hab : a ≠ b := by
    rintro rfl
    simp at h1
  have hcd : c ≠ d := by
    rintro rfl
    simp at h1
  have hef : e ≠ f := by
    rintro rfl
    simp at h2
  have hgh : g ≠ h := by
    rintro rfl
    simp at h4
  have d1 : Disjoint (swap a b) (swap c d) := disjoint_swap_swap h1
  have d12 : Disjoint (swap a b * swap c d) (swap e f) :=
    Disjoint.mul_left (disjoint_swap_swap h2) (disjoint_swap_swap h3)
  have d123 : Disjoint (swap a b * swap c d * swap e f) (swap g h) :=
    Disjoint.mul_left (Disjoint.mul_left (disjoint_swap_swap h4) (disjoint_swap_swap h5))
      (disjoint_swap_swap h6)
  rw [d123.cycleType_mul, d12.cycleType_mul, d1.cycleType_mul, ct_swap hab, ct_swap hcd,
    ct_swap hef, ct_swap hgh]
  rfl

private theorem std_two_ten : ∃ s₀ u₀ v₀ : Perm (Fin 10), s₀.cycleType = Multiset.replicate 2 2 ∧
    sign u₀ = 1 ∧ sign v₀ = 1 ∧ u₀ * s₀ = s₀ * u₀ ∧ v₀ * s₀ = s₀ * v₀ ∧
      u₀ * v₀ * u₀⁻¹ * v₀⁻¹ = s₀ :=
  ⟨swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 1 * swap 4 5, ct_two (by decide),
    by decide, by decide, by decide, by decide, by decide⟩

private theorem std_four_ten : ∃ s₀ u₀ v₀ : Perm (Fin 10), s₀.cycleType = Multiset.replicate 4 2 ∧
    sign u₀ = 1 ∧ sign v₀ = 1 ∧ u₀ * s₀ = s₀ * u₀ ∧ v₀ * s₀ = s₀ * v₀ ∧
      u₀ * v₀ * u₀⁻¹ * v₀⁻¹ = s₀ :=
  ⟨swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7,
    swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7, swap 0 1 * swap 4 5,
    ct_four (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by decide, by decide, by decide, by decide, by decide⟩

private theorem std_two_eleven : ∃ s₀ u₀ v₀ : Perm (Fin 11), s₀.cycleType = Multiset.replicate 2 2 ∧
    sign u₀ = 1 ∧ sign v₀ = 1 ∧ u₀ * s₀ = s₀ * u₀ ∧ v₀ * s₀ = s₀ * v₀ ∧
      u₀ * v₀ * u₀⁻¹ * v₀⁻¹ = s₀ :=
  ⟨swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 1 * swap 4 5, ct_two (by decide),
    by decide, by decide, by decide, by decide, by decide⟩

private theorem std_four_eleven : ∃ s₀ u₀ v₀ : Perm (Fin 11),
    s₀.cycleType = Multiset.replicate 4 2 ∧
    sign u₀ = 1 ∧ sign v₀ = 1 ∧ u₀ * s₀ = s₀ * u₀ ∧ v₀ * s₀ = s₀ * v₀ ∧
      u₀ * v₀ * u₀⁻¹ * v₀⁻¹ = s₀ :=
  ⟨swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7,
    swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7, swap 0 1 * swap 4 5,
    ct_four (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by decide, by decide, by decide, by decide, by decide⟩

theorem alt_involution_comm (n : ℕ) (hn : n = 10 ∨ n = 11) (s : Perm (Fin n)) (hs2 : s * s = 1)
    (hs1 : s ≠ 1) (hsign : sign s = 1) :
    ∃ u v : Perm (Fin n), sign u = 1 ∧ sign v = 1 ∧ u * s = s * u ∧ v * s = s * v ∧
      u * v * u⁻¹ * v⁻¹ = s := by
  obtain ⟨b, hb1, hb2, hct⟩ :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.cycleType_eq_replicate_two s hs2 hs1
  have hbeven : Even b := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [sign_of_cycleType, hct, Multiset.sum_replicate, Multiset.card_replicate] at hsign
    have h3 : Odd (b • 2 + b) := by
      rw [smul_eq_mul]
      exact (Nat.even_mul.2 (Or.inr even_two)).add_odd hodd
    rw [h3.neg_one_pow] at hsign
    exact absurd hsign (by decide)
  have hb5 : b ≤ 5 := by omega
  have hb24 : b = 2 ∨ b = 4 := by
    obtain ⟨k, hk⟩ := hbeven
    omega
  rcases hn with rfl | rfl
  · rcases hb24 with rfl | rfl
    · obtain ⟨s₀, u₀, v₀, h₀, hu, hv, hus, hvs, hc⟩ := std_two_ten
      exact comm_decomp_of_isConj (isConj_iff_cycleType_eq.2 (hct.trans h₀.symm)) hu hv hus hvs hc
    · obtain ⟨s₀, u₀, v₀, h₀, hu, hv, hus, hvs, hc⟩ := std_four_ten
      exact comm_decomp_of_isConj (isConj_iff_cycleType_eq.2 (hct.trans h₀.symm)) hu hv hus hvs hc
  · rcases hb24 with rfl | rfl
    · obtain ⟨s₀, u₀, v₀, h₀, hu, hv, hus, hvs, hc⟩ := std_two_eleven
      exact comm_decomp_of_isConj (isConj_iff_cycleType_eq.2 (hct.trans h₀.symm)) hu hv hus hvs hc
    · obtain ⟨s₀, u₀, v₀, h₀, hu, hv, hus, hvs, hc⟩ := std_four_eleven
      exact comm_decomp_of_isConj (isConj_iff_cycleType_eq.2 (hct.trans h₀.symm)) hu hv hus hvs hc

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
