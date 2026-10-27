module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def cx (x w : G) : G := w⁻¹ * (x * w * x⁻¹)

theorem cx_cube_identity {x : G} (hx : x ^ 3 = 1) (w : G) :
    cx x w ^ 2 * cx x (cx x w) * cx x w * cx x (cx x w) ^ 2 * cx x (cx x (cx x w)) = 1 := by
  have key : ∀ a : G, x * a * x⁻¹ = a * cx x a := fun a => by rw [cx, mul_inv_cancel_left]
  have conj : ∀ a b : G, x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := fun a b => by group
  have hw : x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹ = w := by
    have hx' : x * x * x = 1 := by simpa [pow_succ, mul_assoc] using hx
    calc x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * w * (x * x * x)⁻¹ := by group
      _ = w := by rw [hx']; simp
  generalize hc1 : cx x w = c1 at *
  generalize hc2 : cx x c1 = c2 at *
  generalize hc3 : cx x c2 = c3 at *
  have e1 : x * w * x⁻¹ = w * c1 := by rw [← hc1]; exact key w
  have e2 : x * c1 * x⁻¹ = c1 * c2 := by rw [← hc2]; exact key c1
  have e3 : x * c2 * x⁻¹ = c2 * c3 := by rw [← hc3]; exact key c2
  have h2 : x * (x * w * x⁻¹) * x⁻¹ = w * c1 * c1 * c2 := by
    simp only [conj, e1, e2]; group
  have h3 : x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹ = w * c1 * c1 * c2 * c1 * c2 * c2 * c3 := by
    rw [h2]; simp only [conj, e1, e2, e3]; group
  rw [h3] at hw
  have h4 : w * (c1 * c1 * c2 * c1 * c2 * c2 * c3) = w * 1 := by
    rw [mul_one]; simpa only [mul_assoc] using hw
  calc c1 ^ 2 * c2 * c1 * c2 ^ 2 * c3 = c1 * c1 * c2 * c1 * c2 * c2 * c3 := by
        simp only [sq, mul_assoc]
    _ = 1 := mul_left_cancel h4

theorem cube_reorder {c1 c2 c3 : G} (T : c1 ^ 2 * c2 * c1 * c2 ^ 2 * c3 = 1) :
    c1 ^ 3 * c2 ^ 3 * c3 = c1 ^ 2 * ⁅c1, c2⁆ * (c1 ^ 2)⁻¹ := by
  have h3 : c3 = (c1 ^ 2 * c2 * c1 * c2 ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right T
  subst h3
  simp only [commutatorElement_def, pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
  group

theorem cube_prod_mem {x : G} (hx : x ^ 3 = 1) (w : G) (N : Subgroup G) [N.Normal]
    (hN : ⁅cx x w, cx x (cx x w)⁆ ∈ N) :
    cx x w ^ 3 * cx x (cx x w) ^ 3 * cx x (cx x (cx x w)) ∈ N := by
  rw [cube_reorder (cx_cube_identity hx w)]
  have := Subgroup.Normal.conj_mem ‹N.Normal› _ hN (cx x w ^ 2)
  simpa [mul_assoc] using this

theorem mul_pow_three_mem_iff (N : Subgroup G) [N.Normal] {d w : G} (hc : ⁅d, w⁆ ∈ N)
    (hw : w ^ 3 ∈ N) : (d * w) ^ 3 ∈ N ↔ d ^ 3 ∈ N := by
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  have hcomm : Commute (π d) (π w) := by
    have : π ⁅d, w⁆ = 1 := (QuotientGroup.eq_one_iff _).2 hc
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hw1 : (π w) ^ 3 = 1 := by
    rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).2 hw
  have key : π ((d * w) ^ 3) = π (d ^ 3) := by
    rw [map_pow, map_mul, hcomm.mul_pow, hw1, mul_one, map_pow]
  rw [← QuotientGroup.eq_one_iff (N := N), ← QuotientGroup.eq_one_iff (N := N)]
  exact ⟨fun h => (key.symm.trans h), fun h => key.trans h⟩

structure CubeSetup (x : G) (A : ℕ → Subgroup G) (n : ℕ) : Prop where
  normal : ∀ j, (A j).Normal
  anti : ∀ j l, j ≤ l → A l ≤ A j
  comm : ∀ j l, 1 ≤ j → 1 ≤ l → ∀ a ∈ A j, ∀ b ∈ A l, ⁅a, b⁆ ∈ A (j + l)
  bot : A n = ⊥
  hx : x ^ 3 = 1
  hc : ∀ j, 1 ≤ j → ∀ w ∈ A j, cx x w ∈ A (j + 1)
  hsurj : ∀ j, 1 ≤ j → j + 2 ≤ n → ∀ z ∈ A (j + 1), ∃ y ∈ A j, ∃ w ∈ A (j + 2), z = cx x y * w
  hinj : ∀ j, 1 ≤ j → j + 2 ≤ n → ∀ y ∈ A j, y ∉ A (j + 1) → cx x y ∉ A (j + 2)

namespace CubeSetup

variable {x : G} {A : ℕ → Subgroup G} {n : ℕ} (S : CubeSetup x A n)

include S

theorem cube_prod_mem' {j : ℕ} (hj : 1 ≤ j) {y : G} (hy : y ∈ A j) :
    cx x y ^ 3 * cx x (cx x y) ^ 3 * cx x (cx x (cx x y)) ∈ A (2 * j + 3) := by
  have := S.normal (2 * j + 3)
  apply cube_prod_mem S.hx y
  have h1 : cx x y ∈ A (j + 1) := S.hc j hj y hy
  have h2 : cx x (cx x y) ∈ A (j + 2) := S.hc (j + 1) (by omega) _ h1
  have := S.comm (j + 1) (j + 2) (by omega) (by omega) _ h1 _ h2
  rwa [show j + 1 + (j + 2) = 2 * j + 3 by ring] at this

theorem cube_mem : ∀ d k : ℕ, n - k = d → 2 ≤ k → ∀ z ∈ A k, z ^ 3 ∈ A (k + 2) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k hd hk z hz
    by_cases hkn : n ≤ k
    · have : A k = ⊥ := le_bot_iff.1 (S.bot ▸ S.anti n k hkn)
      rw [this, Subgroup.mem_bot] at hz
      subst hz
      simp [one_pow, (A (k + 2)).one_mem]
    · push Not at hkn
      obtain ⟨y, hy, w, hw, rfl⟩ := S.hsurj (k - 1) (by omega) (by omega) z
        (by rwa [show k - 1 + 1 = k by omega])
      rw [show k - 1 + 2 = k + 1 by omega] at hw
      set d1 := cx x y with hd1
      have hy' : y ∈ A (k - 1) := hy
      have hd1k : d1 ∈ A k := by
        have := S.hc (k - 1) (by omega) y hy'
        rwa [show k - 1 + 1 = k by omega] at this
      have hd2 : cx x d1 ∈ A (k + 1) := S.hc k (by omega) _ hd1k
      have hd3 : cx x (cx x d1) ∈ A (k + 2) := S.hc (k + 1) (by omega) _ hd2
      have IH : ∀ u ∈ A (k + 1), u ^ 3 ∈ A (k + 3) := fun u hu =>
        ih (n - (k + 1)) (by omega) (k + 1) rfl (by omega) u hu
      have := S.normal (k + 2)
      have hprod : d1 ^ 3 * cx x d1 ^ 3 * cx x (cx x d1) ∈ A (2 * k + 1) := by
        have := S.cube_prod_mem' (j := k - 1) (by omega) hy'
        rwa [show 2 * (k - 1) + 3 = 2 * k + 1 by omega] at this
      have hle : A (2 * k + 1) ≤ A (k + 2) := S.anti _ _ (by omega)
      have hd3' : d1 ^ 3 ∈ A (k + 2) := by
        have h2 : cx x d1 ^ 3 ∈ A (k + 2) := S.anti _ _ (by omega) (IH _ hd2)
        have h4 := (A (k + 2)).mul_mem
          ((A (k + 2)).mul_mem (hle hprod) ((A (k + 2)).inv_mem hd3))
          ((A (k + 2)).inv_mem h2)
        have e : d1 ^ 3 * cx x d1 ^ 3 * cx x (cx x d1) * (cx x (cx x d1))⁻¹ * (cx x d1 ^ 3)⁻¹ =
            d1 ^ 3 := by group
        rwa [e] at h4
      have hcomm : ⁅d1, w⁆ ∈ A (k + 2) := by
        have := S.comm k (k + 1) (by omega) (by omega) _ hd1k _ hw
        exact hle (by rwa [show k + (k + 1) = 2 * k + 1 by ring] at this)
      have hw3 : w ^ 3 ∈ A (k + 2) := S.anti _ _ (by omega) (IH w hw)
      exact (mul_pow_three_mem_iff (A (k + 2)) hcomm hw3).2 hd3'

theorem cube_mem' {k : ℕ} (hk : 2 ≤ k) {z : G} (hz : z ∈ A k) : z ^ 3 ∈ A (k + 2) :=
  S.cube_mem (n - k) k rfl hk z hz

theorem cube_not_mem {k : ℕ} (hk : 2 ≤ k) (hkn : k + 3 ≤ n) {z : G} (hz : z ∈ A k)
    (hz' : z ∉ A (k + 1)) : z ^ 3 ∉ A (k + 3) := by
  obtain ⟨y, hy, w, hw, rfl⟩ := S.hsurj (k - 1) (by omega) (by omega) z
    (by rwa [show k - 1 + 1 = k by omega])
  rw [show k - 1 + 2 = k + 1 by omega] at hw
  have hd1k : cx x y ∈ A k := by
    have := S.hc (k - 1) (by omega) y hy
    rwa [show k - 1 + 1 = k by omega] at this
  have hyk : y ∉ A k := fun hyk => hz' (by
    have h1 : cx x y ∈ A (k + 1) := S.hc k (by omega) y hyk
    exact (A (k + 1)).mul_mem h1 hw)
  have hd1' : cx x y ∉ A (k + 1) := by
    have := S.hinj (k - 1) (by omega) (by omega) y hy (by rwa [show k - 1 + 1 = k by omega])
    rwa [show k - 1 + 2 = k + 1 by omega] at this
  have hd2 : cx x (cx x y) ∈ A (k + 1) := S.hc k (by omega) _ hd1k
  have hd2' : cx x (cx x y) ∉ A (k + 2) := S.hinj k (by omega) (by omega) _ hd1k hd1'
  have hd3' : cx x (cx x (cx x y)) ∉ A (k + 3) := S.hinj (k + 1) (by omega) (by omega) _ hd2 hd2'
  have := S.normal (k + 3)
  have hle : A (2 * k + 1) ≤ A (k + 3) := S.anti _ _ (by omega)
  have hw3 : w ^ 3 ∈ A (k + 3) := S.cube_mem' (by omega) hw
  have hcomm : ⁅cx x y, w⁆ ∈ A (k + 3) := by
    have := S.comm k (k + 1) (by omega) (by omega) _ hd1k _ hw
    exact hle (by rwa [show k + (k + 1) = 2 * k + 1 by ring] at this)
  intro hcube
  have hcube' : cx x y ^ 3 ∈ A (k + 3) := (mul_pow_three_mem_iff (A (k + 3)) hcomm hw3).1 hcube
  have hprod : cx x y ^ 3 * cx x (cx x y) ^ 3 * cx x (cx x (cx x y)) ∈ A (2 * k + 1) := by
    have := S.cube_prod_mem' (j := k - 1) (by omega) hy
    rwa [show 2 * (k - 1) + 3 = 2 * k + 1 by omega] at this
  have h2 : cx x (cx x y) ^ 3 ∈ A (k + 3) := S.cube_mem' (by omega) hd2
  apply hd3'
  have h5 := (A (k + 3)).mul_mem
    ((A (k + 3)).mul_mem ((A (k + 3)).inv_mem h2) ((A (k + 3)).inv_mem hcube'))
    (hle hprod)
  have e : (cx x (cx x y) ^ 3)⁻¹ * (cx x y ^ 3)⁻¹ *
      (cx x y ^ 3 * cx x (cx x y) ^ 3 * cx x (cx x (cx x y))) = cx x (cx x (cx x y)) := by
    group
  rwa [e] at h5

theorem pow_three_eq_one_mem {z : G} (hz : z ∈ A 2) (hz3 : z ^ 3 = 1) : z ∈ A (n - 2) := by
  have key : ∀ d k : ℕ, k + d = n - 2 → 2 ≤ k → ∀ z ∈ A k, z ^ 3 = 1 → z ∈ A (n - 2) := by
    intro d
    induction d with
    | zero =>
      intro k hk _ z hz _
      rwa [show n - 2 = k by omega]
    | succ d ih =>
      intro k hk hk2 z hz hz3
      by_cases hz' : z ∈ A (k + 1)
      · exact ih (k + 1) (by omega) (by omega) z hz' hz3
      · exfalso
        exact S.cube_not_mem hk2 (by omega) hz hz' (hz3 ▸ (A (k + 3)).one_mem)
  by_cases h : 2 ≤ n - 2
  · exact key (n - 2 - 2) 2 (by omega) le_rfl z hz hz3
  · exact S.anti _ _ (by omega) hz

end CubeSetup

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
