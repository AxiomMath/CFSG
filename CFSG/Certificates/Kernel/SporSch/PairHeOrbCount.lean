module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Basic

public section

namespace CFSG.KS.SporSch.OrbCount

open Finset

theorem sum_div_blocks (P : ℕ → Prop) [DecidablePred P] (L : ℕ) (hL : 0 < L) :
    ∀ n, ∑ t ∈ range (n * L), (if P (t / L) then 1 else 0) =
      L * ∑ j ∈ range n, (if P j then 1 else 0)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, sum_range_add, sum_div_blocks P L hL n, sum_range_succ, mul_add]
    congr 1
    have e : ∀ x ∈ range L, (if P ((n * L + x) / L) then 1 else 0) = (if P n then 1 else 0) :=
      fun x hx => by
        rw [Nat.mul_comm, Nat.mul_add_div hL, Nat.div_eq_of_lt (mem_range.1 hx), add_zero]
    rw [sum_congr rfl e, sum_const, card_range]
    rw [nsmul_eq_mul]
    rfl

theorem count_orb {G : Type*} [Group G] (P : G → Prop) [DecidablePred P] (x r : ℕ → G) (z : G)
    {n L c : ℕ} (hL : 0 < L) (hc : c = n * L) (σ : ℕ → ℕ) (hσ : ∀ t < c, σ t < c)
    (hinj : ∀ t < c, ∀ u < c, σ t = σ u → t = u)
    (hg : ∀ t < c, x (σ t) = z ^ (t % L) * r (t / L) * (z ^ (t % L))⁻¹)
    (hP : ∀ (k : ℕ) (g : G), P (z ^ k * g * (z ^ k)⁻¹) ↔ P g) :
    ((range c).filter fun i => P (x i)).card = L * ((range n).filter fun j => P (r j)).card := by
  classical
  have h1 : ((range c).filter fun i => P (x i)).card =
      ((range c).filter fun t => P (r (t / L))).card := by
    symm
    refine card_bij (fun t _ => σ t) (fun t ht => ?_) (fun t ht u hu h => ?_) (fun i hi => ?_)
    · obtain ⟨ht, hp⟩ := mem_filter.1 ht
      refine mem_filter.2 ⟨mem_range.2 (hσ t (mem_range.1 ht)), ?_⟩
      rw [hg t (mem_range.1 ht), hP]
      exact hp
    · exact hinj t (mem_range.1 (mem_filter.1 ht).1) u (mem_range.1 (mem_filter.1 hu).1) h
    · obtain ⟨hi, hp⟩ := mem_filter.1 hi
      have himg : (range c).image σ = range c := by
        refine eq_of_subset_of_card_le (fun i hi => ?_) ?_
        · obtain ⟨t, ht, rfl⟩ := mem_image.1 hi
          exact mem_range.2 (hσ t (mem_range.1 ht))
        · rw [card_image_of_injOn fun t ht u hu h => hinj t (mem_range.1 ht) u (mem_range.1 hu) h]
      rw [← himg] at hi
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hi
      refine ⟨t, mem_filter.2 ⟨ht, ?_⟩, rfl⟩
      rw [hg t (mem_range.1 ht), hP] at hp
      exact hp
  rw [h1, card_filter, card_filter, hc, sum_div_blocks (fun j => P (r j)) L hL n]

end CFSG.KS.SporSch.OrbCount

end
