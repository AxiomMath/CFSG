module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.ComponentClassification.Foote47

open Subgroup

variable {G : Type} [Group G]

theorem exists_mem_centralizer_of_isPGroup {W O : Subgroup G} (hW : IsPGroup 2 W)
    (hWO : W ≤ normalizer (O : Set G)) (hO : Odd (Nat.card O)) {m : G}
    (hm : ∀ w ∈ W, m⁻¹ * (w * m * w⁻¹) ∈ O) : ∃ o ∈ O, m * o ∈ centralizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ (w : W) (x : G), m⁻¹ * x ∈ O → m⁻¹ * ((w : G) * x * (w : G)⁻¹) ∈ O := by
    intro w x hx
    have h1 : m⁻¹ * ((w : G) * x * (w : G)⁻¹) =
        (m⁻¹ * ((w : G) * m * (w : G)⁻¹)) * ((w : G) * (m⁻¹ * x) * (w : G)⁻¹) := by group
    rw [h1]
    exact mul_mem (hm w w.2) ((mem_normalizer_iff.mp (hWO w.2) _).mp hx)
  let α := {x : G // m⁻¹ * x ∈ O}
  let act : MulAction W α :=
    { smul := fun w x => ⟨(w : G) * x.1 * (w : G)⁻¹, hmem w x.1 x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : W) : G) * x.1 * ((1 : W) : G)⁻¹ = x.1
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        show ((a * b : W) : G) * x.1 * ((a * b : W) : G)⁻¹ =
          (a : G) * ((b : G) * x.1 * (b : G)⁻¹) * (a : G)⁻¹
        rw [Subgroup.coe_mul]
        group) }
  have hcard : Nat.card α = Nat.card O := by
    refine Nat.card_congr
      { toFun := fun x => ⟨m⁻¹ * x.1, x.2⟩
        invFun := fun o => ⟨m * o, by simp⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun o => Subtype.ext (by simp) }
  have hodd : ¬ 2 ∣ Nat.card α := by
    rw [hcard]
    have := Nat.odd_iff.mp hO
    omega
  obtain ⟨x, hx⟩ := hW.nonempty_fixed_point_of_prime_not_dvd_card α hodd
  refine ⟨m⁻¹ * x.1, x.2, ?_⟩
  rw [mul_inv_cancel_left, mem_centralizer_iff]
  intro w hw
  have h1 : (⟨w, hw⟩ : W) • x = x := hx ⟨w, hw⟩
  have h2 : w * x.1 * w⁻¹ = x.1 := congrArg Subtype.val h1
  calc w * x.1 = w * x.1 * w⁻¹ * w := by group
    _ = x.1 * w := by rw [h2]

theorem exists_conj_of_odd_orderOf_mul {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : Odd (orderOf (a * b))) : ∃ u ∈ zpowers (a * b), b = u⁻¹ * a * u := by
  obtain ⟨n, hn⟩ := hab
  set o := a * b with ho
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hinv : a * o * a⁻¹ = o⁻¹ := by
    rw [ho, hai, mul_inv_rev, hai, hbi]
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha, one_mul]
  set u := o ^ (n + 1) with hu
  have hu2 : u * u = o := by
    rw [hu, ← pow_add, show n + 1 + (n + 1) = 2 * n + 1 + 1 by ring, pow_succ, ← hn,
      pow_orderOf_eq_one, one_mul]
  have hau : a * u * a⁻¹ = u⁻¹ := by
    rw [hu, ← conj_pow, hinv, inv_pow]
  refine ⟨u, pow_mem (mem_zpowers o) _, ?_⟩
  have h1 : u⁻¹ * a * u = u⁻¹ * (a * u * a⁻¹) * a := by group
  rw [h1, hau, ← mul_inv_rev, hu2, ho, mul_inv_rev, hbi, hai]
  calc b = b * (a * a) := by rw [ha, mul_one]
    _ = b * a * a := (mul_assoc _ _ _).symm

end CFSG.ComponentClassification.Foote47
