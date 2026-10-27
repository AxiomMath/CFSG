module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

variable {G : Type*} [Group G]

theorem isConj_of_mem_of_not_mem_of_centralizer_le [Finite G] {G₀ : Subgroup G}
    (hC : ∀ x ∈ G₀, orderOf x = 2 → Subgroup.centralizer ({x} : Set G) ≤ G₀)
    {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxG : x ∈ G₀) (hyG : y ∉ G₀) :
    IsConj x y := by
  have hx2 : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
  have hy2 : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  set c := x * y with hc
  have hcinv : c⁻¹ = y * x := by rw [hc, mul_inv_rev, hxinv, hyinv]
  have hxc : x * c * x⁻¹ = c⁻¹ := by
    rw [hcinv, hc, hxinv, ← mul_assoc, hx2, one_mul]
  have hyc : y * c * y⁻¹ = c⁻¹ := by
    rw [hcinv, hc, hyinv, mul_assoc, mul_assoc, hy2, mul_one]
  rcases Nat.even_or_odd (orderOf c) with ⟨k, hk⟩ | ⟨k, hk⟩
  · exfalso
    have hpos : 0 < orderOf c := orderOf_pos c
    have hk0 : 0 < k := by omega
    set w := c ^ k with hw
    have hw1 : w ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
    have hww : w * w = 1 := by rw [hw, ← pow_add, ← hk, pow_orderOf_eq_one]
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hww) hw1
    have hxw : x * w * x⁻¹ = w := by rw [hw, ← conj_pow, hxc, inv_pow, ← hw, hwinv]
    have hyw : y * w * y⁻¹ = w := by rw [hw, ← conj_pow, hyc, inv_pow, ← hw, hwinv]
    have hwG : w ∈ G₀ := by
      apply hC x hxG hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc w * x = (x * w * x⁻¹) * x := by rw [hxw]
        _ = x * w := by group
    apply hyG
    apply hC w hwG hw2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * w = (y * w * y⁻¹) * y := by group
      _ = w * y := by rw [hyw]
  · have h2k : c ^ (2 * k) = c⁻¹ := by
      have h1 : c ^ (2 * k) * c = 1 := by rw [← pow_succ, ← hk, pow_orderOf_eq_one]
      exact eq_inv_of_mul_eq_one_left h1
    have hxc' : x * c⁻¹ * x⁻¹ = c := by
      calc x * c⁻¹ * x⁻¹ = (x * c * x⁻¹)⁻¹ := by group
        _ = c := by rw [hxc, inv_inv]
    have hxck : x * (c ^ k)⁻¹ * x⁻¹ = c ^ k := by
      rw [← inv_pow, ← conj_pow, hxc']
    refine isConj_iff.mpr ⟨c ^ k, ?_⟩
    calc c ^ k * x * (c ^ k)⁻¹ = c ^ k * (x * (c ^ k)⁻¹ * x⁻¹) * x := by group
      _ = c ^ (2 * k) * x := by rw [hxck, two_mul, pow_add]
      _ = y := by rw [h2k, hcinv, mul_assoc, hx2, mul_one]

private theorem orderOf_conj_eq (c a : G) : orderOf (c * a * c⁻¹) = orderOf a :=
  (SemiconjBy.orderOf_eq c (by
    change c * a = c * a * c⁻¹ * c
    group)).symm

theorem eq_top_of_centralizer_le [Finite G] {G₀ : Subgroup G}
    (hC : ∀ x ∈ G₀, orderOf x = 2 → Subgroup.centralizer ({x} : Set G) ≤ G₀)
    (hgen : Subgroup.closure {x | x ∈ G₀ ∧ orderOf x = 2} = G₀)
    (S : Sylow 2 G) (hSG : (S : Subgroup G) ≤ G₀)
    (hN : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ G₀)
    {x₁ x₂ : G} (h₁ : x₁ ∈ G₀) (h₂ : x₂ ∈ G₀) (ho₁ : orderOf x₁ = 2) (ho₂ : orderOf x₂ = 2)
    (hnc : ¬ IsConj x₁ x₂) : G₀ = ⊤ := by
  have hinv : ∀ y : G, orderOf y = 2 → y ∈ G₀ := by
    intro y hy
    by_contra hyG
    exact hnc ((isConj_of_mem_of_not_mem_of_centralizer_le hC ho₁ hy h₁ hyG).trans
      (isConj_of_mem_of_not_mem_of_centralizer_le hC ho₂ hy h₂ hyG).symm)
  have hset : {x | x ∈ G₀ ∧ orderOf x = 2} = {x : G | orderOf x = 2} := by
    ext y
    exact ⟨fun h => h.2, fun h => ⟨hinv y h, h⟩⟩
  have hnormal : G₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [← hgen, hset] at hn ⊢
    refine Subgroup.closure_induction (p := fun n _ => g * n * g⁻¹ ∈
      Subgroup.closure {x : G | orderOf x = 2}) (fun a ha => ?_) ?_ (fun a b _ _ ha hb => ?_)
      (fun a _ ha => ?_) hn
    · exact Subgroup.subset_closure (by
        show orderOf (g * a * g⁻¹) = 2
        rw [orderOf_conj_eq]; exact ha)
    · simp
    · have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]; exact mul_mem ha hb
    · have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem ha
  have hframe := Sylow.normalizer_sup_eq_top' (N := G₀) S hSG
  rw [eq_top_iff, ← hframe]
  exact sup_le hN le_rfl

end CFSG.ClassicalInvolution.Solomon73.Yamaki
