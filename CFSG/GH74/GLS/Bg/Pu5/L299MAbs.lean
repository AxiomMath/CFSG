module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sq_centralizes_of_normalizes_four [Finite G] {U : Subgroup G} {v : G}
    (hU4 : Nat.card ↥U = 4) (hvN : v ∈ normalizer (U : Set G))
    (hv : ∃ k : ℕ, v ^ (2 ^ k) = 1) : ∀ u ∈ U, (v * v) * u = u * (v * v) := by
  intro u hu
  by_cases hu1 : u = 1
  · rw [hu1]
    simp
  obtain ⟨k, hk⟩ := hv
  set g : ℕ → G := fun i => v ^ i * u * (v ^ i)⁻¹ with hg
  have hgU : ∀ i : ℕ, g i ∈ (U : Set G) \ {1} := by
    intro i
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (pow_mem hvN i) u).1 hu
    · intro h1
      apply hu1
      have h2 : v ^ i * u * (v ^ i)⁻¹ = 1 := h1
      calc u = (v ^ i)⁻¹ * (v ^ i * u * (v ^ i)⁻¹) * v ^ i := by group
        _ = 1 := by rw [h2]; group
  have hUc : (U : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hU4
  have hT : ((U : Set G) \ {1}).ncard = 3 := by
    rw [Set.ncard_sdiff_singleton_of_mem (one_mem U), hUc]
  have hs : ((Finset.range 4 : Finset ℕ) : Set ℕ).ncard = 4 := by
    rw [Set.ncard_coe_finset, Finset.card_range]
  obtain ⟨x, hx, y, hy, hxy, hgxy⟩ := Set.exists_ne_map_eq_of_ncard_lt_of_maps_to
    (s := ((Finset.range 4 : Finset ℕ) : Set ℕ)) (t := (U : Set G) \ {1}) (by omega) (f := g)
    (fun i _ => hgU i) (Set.toFinite _)
  have key : ∀ x y : ℕ, x < y → y < 4 → g x = g y → (v * v) * u = u * (v * v) := by
    intro x y hxy hy4 hgxy
    obtain ⟨d, rfl⟩ : ∃ d, y = x + d := ⟨y - x, by omega⟩
    have hd1 : 1 ≤ d := by omega
    have hd3 : d ≤ 3 := by omega
    have hcomm : v ^ d * u = u * v ^ d := by
      have h1 : v ^ x * u * (v ^ x)⁻¹ = v ^ (x + d) * u * (v ^ (x + d))⁻¹ := hgxy
      have h2 : u = v ^ d * u * (v ^ d)⁻¹ := by
        calc u = (v ^ x)⁻¹ * (v ^ x * u * (v ^ x)⁻¹) * v ^ x := by group
          _ = (v ^ x)⁻¹ * (v ^ (x + d) * u * (v ^ (x + d))⁻¹) * v ^ x := by rw [h1]
          _ = v ^ d * u * (v ^ d)⁻¹ := by
            rw [pow_add]
            group
      calc v ^ d * u = (v ^ d * u * (v ^ d)⁻¹) * v ^ d := by group
        _ = u * v ^ d := by rw [← h2]
    have hC : ∀ n : ℕ, v ^ n * u = u * v ^ n → v ^ (n * 2) * u = u * v ^ (n * 2) := by
      intro n hn
      rw [pow_mul]
      exact ((Commute.pow_left (show Commute (v ^ n) u from hn) 2).eq)
    have hCz : ∀ n : ℤ, Commute (v ^ n) u → Commute (v ^ n * v ^ n) u := fun n hn => hn.mul_left hn
    interval_cases d
    ·
      have := hC 1 (by simpa using hcomm)
      simpa [pow_two] using this
    ·
      simpa [pow_two] using hcomm
    ·
      have hcop : IsCoprime (3 : ℤ) ((2 ^ k : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right k (by norm_num))
      obtain ⟨a, b, hab⟩ := hcop
      have hv : v = (v ^ 3) ^ a := by
        have h1 : v ^ (1 : ℤ) = (v ^ 3) ^ a * (v ^ (2 ^ k)) ^ b := by
          rw [← zpow_natCast v 3, ← zpow_natCast v (2 ^ k), ← zpow_mul, ← zpow_mul, ← zpow_add]
          congr 1
          push_cast at hab ⊢
          linarith
        rw [hk, one_zpow, mul_one, zpow_one] at h1
        exact h1
      have hvu : v * u = u * v := by
        have h1 : Commute (v ^ 3) u := hcomm
        have h2 : Commute ((v ^ 3) ^ a) u := h1.zpow_left a
        rw [← hv] at h2
        exact h2.eq
      have := ((Commute.pow_left (show Commute v u from hvu) 2).eq)
      simpa [pow_two] using this
  have hx4 : x < 4 := Finset.mem_range.1 (Finset.mem_coe.1 hx)
  have hy4 : y < 4 := Finset.mem_range.1 (Finset.mem_coe.1 hy)
  rcases lt_or_gt_of_ne hxy with h | h
  · exact key x y h hy4 hgxy
  · exact key y x h hx4 hgxy.symm

theorem eq_one_or_eq_of_mem_zpowers_sq {z x : G} (hz : z * z = 1) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  by_cases hz1 : z = 1
  · left
    rw [hz1]
    simp
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
  rw [← zpow_mod_orderOf, hord]
  have h2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by
    push_cast
    omega
  rcases h2 with h | h
  · left
    rw [h]
    simp
  · right
    rw [h]
    simp

theorem mem_or_mul_mem_of_mem_sup {Q : Subgroup G} {r : G} (hr2 : r * r = 1)
    (hrQ : r ∈ normalizer (Q : Set G)) {x : G} (hx : x ∈ Q ⊔ zpowers r) : x ∈ Q ∨ x * r ∈ Q := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hconj : ∀ q ∈ Q, r * q * r⁻¹ ∈ Q := fun q hq => (mem_normalizer_iff.mp hrQ q).mp hq
  let H : Subgroup G :=
    { carrier := {x | x ∈ Q ∨ x * r ∈ Q}
      one_mem' := Or.inl (one_mem Q)
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (mul_mem hx hy)
        · exact Or.inr (by rw [mul_assoc]; exact mul_mem hx hy)
        · right
          have h1 := hconj y hy
          rw [hri] at h1
          rw [show x * y * r = (x * r) * (r * y * r) by
            rw [show (x * r) * (r * y * r) = x * (r * r) * y * r by group, hr2, mul_one]]
          exact mul_mem hx h1
        · left
          have h1 := hconj _ hy
          rw [hri, show r * (y * r) * r = r * y * (r * r) by group, hr2, mul_one] at h1
          rw [show x * y = (x * r) * (r * y) by
            rw [show (x * r) * (r * y) = x * (r * r) * y by group, hr2, mul_one]]
          exact mul_mem hx h1
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (inv_mem hx)
        · right
          have h1 := hconj _ (inv_mem hx)
          rwa [hri, show r * (x * r)⁻¹ * r = x⁻¹ * r by
            rw [mul_inv_rev, hri]
            calc r * (r * x⁻¹) * r = (r * r) * x⁻¹ * r := by group
              _ = x⁻¹ * r := by rw [hr2, one_mul]] at h1 }
  have hle : Q ⊔ zpowers r ≤ H :=
    sup_le (fun q hq => Or.inl hq) (zpowers_le.mpr (Or.inr (by rw [hr2]; exact one_mem Q)))
  exact hle hx

end CFSG.GH74.GLS.Bg.Pu5
