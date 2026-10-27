module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc

open Equiv

private def threeCycle : Perm (Fin 6) := swap 0 1 * swap 1 2

private def twoThreeCycles : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 3 4 * swap 4 5

private theorem cycleType_threeCycle : threeCycle.cycleType = {3} := by
  have h : threeCycle.support.card = 3 := by decide +kernel
  exact card_support_eq_three_iff.mp h

private theorem cycleType_twoThreeCycles : twoThreeCycles.cycleType = {3, 3} := by
  have h : twoThreeCycles.support.card = 6 ∧ twoThreeCycles ^ 3 = 1 := by decide +kernel
  have htype := Perm.cycleType_of_pow_prime_eq_one h.2
  have hsum := Perm.sum_cycleType twoThreeCycles
  rw [htype, Multiset.sum_replicate, smul_eq_mul, h.1] at hsum
  have hcard : twoThreeCycles.cycleType.card = 2 := by omega
  simpa [hcard] using htype

private theorem exists_conj_rep (σ : Perm (Fin 6)) (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    ∃ g : Perm (Fin 6), g * threeCycle * g⁻¹ = σ ∨ g * twoThreeCycles * g⁻¹ = σ := by
  have horder : orderOf σ = 3 := orderOf_eq_prime h3 h1
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (horder ▸ Nat.prime_three)
  have hsum := Perm.sum_cycleType_le σ
  simp only [hk, horder, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · obtain ⟨g, hg⟩ := isConj_iff.mp (Perm.isConj_of_cycleType_eq
      (cycleType_threeCycle.trans (by simpa [horder] using hk.symm)))
    exact ⟨g, Or.inl hg⟩
  · obtain ⟨g, hg⟩ := isConj_iff.mp (Perm.isConj_of_cycleType_eq
      (cycleType_twoThreeCycles.trans (by simpa [horder] using hk.symm)))
    exact ⟨g, Or.inr hg⟩

private theorem rep_not_commute :
    ∀ x : Perm (Fin 6), x * x = 1 → x ≠ 1 → Perm.sign x = 1 →
      threeCycle * x ≠ x * threeCycle ∧ twoThreeCycles * x ≠ x * twoThreeCycles := by
  decide +kernel

private theorem comm_conj_rep {c x g σ : Perm (Fin 6)} (hg : g * c * g⁻¹ = σ)
    (h : σ * x = x * σ) : c * (g⁻¹ * x * g) = g⁻¹ * x * g * c := by
  subst hg
  calc c * (g⁻¹ * x * g) = g⁻¹ * (g * c * g⁻¹ * x) * g := by group
    _ = g⁻¹ * (x * (g * c * g⁻¹)) * g := by rw [h]
    _ = g⁻¹ * x * g * c := by group

theorem a6_order_three_not_commute_involution :
    ∀ σ : Perm (Fin 6), σ * σ * σ = 1 → σ ≠ 1 →
      ∀ x : Perm (Fin 6), x * x = 1 → x ≠ 1 → Perm.sign x = 1 → σ * x ≠ x * σ := by
  intro σ h3 h1 x hx2 hx1 hxs hcomm
  obtain ⟨g, hg⟩ := exists_conj_rep σ (by rw [pow_succ, pow_two]; exact h3) h1
  have hy2 : g⁻¹ * x * g * (g⁻¹ * x * g) = 1 := by
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hx2]; group
  have hy1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hys : Perm.sign (g⁻¹ * x * g) = 1 := by simp [hxs]
  rcases hg with hg | hg
  · exact (rep_not_commute _ hy2 hy1 hys).1 (comm_conj_rep hg hcomm)
  · exact (rep_not_commute _ hy2 hy1 hys).2 (comm_conj_rep hg hcomm)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc
