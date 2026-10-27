module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Char

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t u : G}

private lemma y6_z_comm_t (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : z * t = t * z := by
  apply h.t_cent
  have ha : a₁ ∈ A := by
    rw [h.hA]
    exact Subgroup.subset_closure (by simp)
  have hmem : a₁ ^ 2 ∈ A := Subgroup.pow_mem A ha 2
  rwa [h.rel.a1_sq] at hmem

private lemma y6_tu3 (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : t * u ^ 3 = z * (t * u) := by
  have hzu : z * u = u ^ 3 := by
    rw [← h.u_sq]
    group
  rw [← mul_assoc, y6_z_comm_t h, mul_assoc, hzu]

private lemma y6_V_elems (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ v ∈ V, v = 1 ∨ v = u ∨ v = z ∨ v = u ^ 3 := by
  classical
  intro v hv
  rw [h.hV] at hv
  have h4 : u ^ 4 = 1 := by simpa [h.u_ord] using pow_orderOf_eq_one u
  have hfin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by omega, h4⟩
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, h.u_ord] at hv
  obtain ⟨n, hn, hnv⟩ := Finset.mem_image.mp hv
  rw [Finset.mem_range] at hn
  interval_cases n
  · left; rw [← hnv, pow_zero]
  · right; left; rw [← hnv, pow_one]
  · right; right; left; rw [← hnv, h.u_sq]
  · right; right; right; rw [← hnv]

private lemma y6_conj_t_cases (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {x : G}
    (hx2 : x ∈ normalizer (V : Set G)) (hx3 : x ∈ normalizer (C0 : Set G)) :
    x * t * x⁻¹ = t ∨ x * t * x⁻¹ = z * t ∨
      x * t * x⁻¹ = t * u ∨ x * t * x⁻¹ = z * (t * u) := by
  have hv : t⁻¹ * (x * t * x⁻¹) ∈ V := (y6_mem_NC0_iff h hx2).mp hx3
  have hkey : x * t * x⁻¹ = t * (t⁻¹ * (x * t * x⁻¹)) := by group
  rcases y6_V_elems h _ hv with h1 | h1 | h1 | h1
  · left; rw [hkey, h1, mul_one]
  · right; right; left; rw [hkey, h1]
  · right; left; rw [hkey, h1, y6_z_comm_t h]
  · right; right; right; rw [hkey, h1, y6_tu3 h]

private lemma y6_conj_t_alt (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {x : G}
    (hx2 : x ∈ normalizer (V : Set G)) (hx3 : x ∈ normalizer (C0 : Set G))
    (hx : ¬ (x * t * x⁻¹ = t ∨ x * t * x⁻¹ = z * t)) :
    x * t * x⁻¹ = t * u ∨ x * t * x⁻¹ = z * (t * u) := by
  rcases y6_conj_t_cases h hx2 hx3 with h1 | h1 | h1 | h1
  · exact absurd (Or.inl h1) hx
  · exact absurd (Or.inr h1) hx
  · exact Or.inl h1
  · exact Or.inr h1

theorem y6_three_way (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {C Y : Subgroup G}
    (hC2 : C ≤ normalizer (V : Set G)) (hC3 : C ≤ normalizer (C0 : Set G))
    (hY : ∀ x ∈ C, x ∈ Y ↔ (x * t * x⁻¹ = t ∨ x * t * x⁻¹ = z * t)) :
    ∀ x ∈ C, ∀ y ∈ C, x ∈ Y ∨ y ∈ Y ∨ x⁻¹ * y ∈ Y := by
  intro x hx y hy
  by_cases hxY : x ∈ Y
  · exact Or.inl hxY
  by_cases hyY : y ∈ Y
  · exact Or.inr (Or.inl hyY)
  have hxnot : ¬ (x * t * x⁻¹ = t ∨ x * t * x⁻¹ = z * t) := fun h' => hxY ((hY x hx).mpr h')
  have hynot : ¬ (y * t * y⁻¹ = t ∨ y * t * y⁻¹ = z * t) := fun h' => hyY ((hY y hy).mpr h')
  have hxm : x * t * x⁻¹ = t * u ∨ x * t * x⁻¹ = z * (t * u) :=
    y6_conj_t_alt h (hC2 hx) (hC3 hx) hxnot
  have hym : y * t * y⁻¹ = t * u ∨ y * t * y⁻¹ = z * (t * u) :=
    y6_conj_t_alt h (hC2 hy) (hC3 hy) hynot
  have hz2 : z * z = 1 := by rw [← pow_two]; exact h.rel.z_sq
  have hpair : y * t * y⁻¹ = x * t * x⁻¹ ∨ y * t * y⁻¹ = z * (x * t * x⁻¹) := by
    rcases hxm with hx1 | hx1 <;> rcases hym with hy1 | hy1
    · left; rw [hy1, hx1]
    · right; rw [hy1, hx1]
    · right; rw [hy1, hx1]; rw [← mul_assoc, hz2, one_mul]
    · left; rw [hy1, hx1]
  have hconj : x⁻¹ * (y * t * y⁻¹) * x = t ∨ x⁻¹ * (y * t * y⁻¹) * x = z * t := by
    rcases hpair with hp | hp
    · left; rw [hp]; group
    · right
      have hxz : x⁻¹ * z * x = z := by
        simpa using y6_fix_z h (hC2 (C.inv_mem hx))
      rw [hp]
      calc x⁻¹ * (z * (x * t * x⁻¹)) * x = (x⁻¹ * z * x) * t := by group
        _ = z * t := by rw [hxz]
  refine Or.inr (Or.inr ?_)
  have hid : (x⁻¹ * y) * t * (x⁻¹ * y)⁻¹ = x⁻¹ * (y * t * y⁻¹) * x := by group
  rw [hY (x⁻¹ * y) (C.mul_mem (C.inv_mem hx) hy), hid]
  exact hconj

end CFSG.OddStandard.HigherRank.YamadaG23
