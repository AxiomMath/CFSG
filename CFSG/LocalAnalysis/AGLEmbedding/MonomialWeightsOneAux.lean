module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.AGLEmbedding

open Subgroup

section Isotropic

variable {A V Z : Type*} [CommGroup A] [CommGroup V] [MulDistribMulAction A V] [CommGroup Z]
  {x : A} {W : Subgroup V}

theorem pow_smul_mem (hW : ∀ v ∈ W, x • v ∈ W) (k : ℕ) {v : V} (hv : v ∈ W) :
    x ^ k • v ∈ W := by
  induction k with
  | zero => rwa [pow_zero, one_smul]
  | succ k ih =>
    rw [pow_succ', mul_smul]
    exact hW _ ih

theorem norm_eq_one (hx : x ^ 5 = 1) (hW : ∀ v ∈ W, x • v ∈ W)
    (hfpf : ∀ v ∈ W, x • v = v → v = 1) {v : V} (hv : v ∈ W) :
    v * (x • v) * (x ^ 2 • v) * (x ^ 3 • v) * (x ^ 4 • v) = 1 := by
  apply hfpf
  · exact mul_mem (mul_mem (mul_mem (mul_mem hv (hW v hv)) (pow_smul_mem hW 2 hv))
      (pow_smul_mem hW 3 hv)) (pow_smul_mem hW 4 hv)
  · simp only [smul_mul', smul_smul, ← sq, ← pow_succ']
    rw [hx, one_smul, mul_comm _ v]
    simp only [mul_assoc]

theorem smul_pow_smul (k : ℕ) (v : V) : x • (x ^ k • v) = x ^ (k + 1) • v := by
  rw [smul_smul, ← pow_succ']

theorem smul_mul_pow_four_smul_sq (hx : x ^ 5 = 1) (hW : ∀ v ∈ W, x • v ∈ W)
    (hfpf : ∀ v ∈ W, x • v = v → v = 1) {v : V} (hv : v ∈ W) :
    x • (x • v * x ^ 4 • v) * x ^ 4 • (x • v * x ^ 4 • v) * (x • v * x ^ 4 • v) = v := by
  have hn := norm_eq_one hx hW hfpf hv
  have h1 : x • (x • v * x ^ 4 • v) = x ^ 2 • v * v := by
    rw [smul_mul', smul_pow_smul, smul_smul, ← sq, hx, one_smul]
  have h4 : x ^ 4 • (x • v * x ^ 4 • v) = v * x ^ 3 • v := by
    rw [smul_mul', smul_smul, smul_smul, show x ^ 4 * x = 1 by rw [← pow_succ, hx],
      ← pow_add, show 4 + 4 = 5 + 3 from rfl, pow_add, hx, one_mul, one_smul]
  rw [h1, h4]
  calc x ^ 2 • v * v * (v * x ^ 3 • v) * (x • v * x ^ 4 • v)
      = v * (v * (x • v) * (x ^ 2 • v) * (x ^ 3 • v) * (x ^ 4 • v)) := by ac_rfl
    _ = v := by rw [hn, mul_one]

theorem sq_smul_mul_pow_three_smul (hx : x ^ 5 = 1) (hW : ∀ v ∈ W, x • v ∈ W)
    (hfpf : ∀ v ∈ W, x • v = v → v = 1) {v : V} (hv : v ∈ W) :
    x ^ 3 • v * x ^ 2 • v = (v * (x • v * x ^ 4 • v))⁻¹ := by
  have hn := norm_eq_one hx hW hfpf hv
  rw [eq_inv_iff_mul_eq_one, ← hn]
  ac_rfl

theorem apply_pow_smul {β : MulAut V} (hβ : ∀ v, β (x • v) = x ^ 2 • β v) (k : ℕ) (v : V) :
    β (x ^ k • v) = x ^ (2 * k) • β v := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_smul, ih, hβ, smul_smul, ← pow_add, Nat.mul_succ, add_comm]

theorem smul_mul_pow_four_smul_apply (hx : x ^ 5 = 1) (hW : ∀ v ∈ W, x • v ∈ W)
    (hfpf : ∀ v ∈ W, x • v = v → v = 1) {β : MulAut V} (hβ : ∀ v, β (x • v) = x ^ 2 • β v)
    {v : V} (hv : v ∈ W) :
    x • β v * x ^ 4 • β v = β ((v * (x • v * x ^ 4 • v))⁻¹) := by
  rw [← sq_smul_mul_pow_three_smul hx hW hfpf hv, map_mul, apply_pow_smul hβ, apply_pow_smul hβ,
    show x ^ (2 * 3) = x by rw [show 2 * 3 = 5 + 1 from rfl, pow_add, hx, one_mul, pow_one]]

theorem pairing_pow_smul (B : V →* V →* Z) (hB : ∀ u v, B (x • u) (x • v) = B u v) (k : ℕ)
    (u v : V) : B (x ^ k • u) (x ^ k • v) = B u v := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, mul_smul, hB, ih]

theorem pairing_smul_mul_pow_four_smul_left (hx : x ^ 5 = 1) (B : V →* V →* Z)
    (hB : ∀ u v, B (x • u) (x • v) = B u v) (u v : V) :
    B (x • u * x ^ 4 • u) v = B u (x • v * x ^ 4 • v) := by
  have h1 : B (x • u) v = B u (x ^ 4 • v) := by
    rw [← pairing_pow_smul B hB 4, smul_smul, show x ^ 4 * x = 1 by rw [← pow_succ, hx], one_smul]
  have h4 : B (x ^ 4 • u) v = B u (x • v) := by
    rw [← hB, smul_smul, show x * x ^ 4 = 1 by rw [← pow_succ', hx], one_smul]
  rw [map_mul, MonoidHom.mul_apply, h1, h4, map_mul, mul_comm]

theorem pairing_swap (B : V →* V →* Z) (halt : ∀ v, B v v = 1) (u v : V) :
    B v u = (B u v)⁻¹ := by
  have h := halt (u * v)
  rw [map_mul (B (u * v)), map_mul B, MonoidHom.mul_apply, MonoidHom.mul_apply, halt, halt,
    one_mul, mul_one] at h
  exact eq_inv_of_mul_eq_one_left h

theorem pairing_smul_mul_pow_four_smul_self (hx : x ^ 5 = 1) (B : V →* V →* Z)
    (hB : ∀ u v, B (x • u) (x • v) = B u v) (halt : ∀ v, B v v = 1) (v : V) :
    B v (x • v * x ^ 4 • v) = 1 := by
  have h4 : B v (x ^ 4 • v) = B (x • v) v := by
    rw [← hB, smul_smul, show x * x ^ 4 = 1 by rw [← pow_succ', hx], one_smul]
  rw [map_mul, h4, pairing_swap B halt v, mul_inv_cancel]

theorem smul_mul_pow_four_smul_zpow (v : V) (k : ℤ) :
    x • v ^ k * x ^ 4 • v ^ k = (x • v * x ^ 4 • v) ^ k := by
  rw [smul_zpow', smul_zpow', mul_zpow]

theorem not_dvd_two_mul_add_one {s : ℕ} (hs : s.Prime) (hs5 : s ≠ 5) {l : ℤ}
    (hl : (s : ℤ) ∣ l * l + l - 1) : ¬ (s : ℤ) ∣ 2 * l + 1 := by
  intro h
  have h5 : (s : ℤ) ∣ 5 := by
    have he : (5 : ℤ) = (2 * l + 1) * (2 * l + 1) - 4 * (l * l + l - 1) := by ring
    rw [he]
    exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right hl _)
  have h5' : s ∣ 5 := by exact_mod_cast h5
  exact hs5 ((Nat.prime_dvd_prime_iff_eq hs (by norm_num)).mp h5')

theorem dvd_of_zpow_eq_one {G : Type*} [Group G] {s : ℕ} (hs : s.Prime) {v : G}
    (hv : v ^ s = 1) (hv1 : v ≠ 1) {k : ℤ} (hk : v ^ k = 1) : (s : ℤ) ∣ k := by
  have : Fact s.Prime := ⟨hs⟩
  rw [← orderOf_eq_prime hv hv1]
  exact orderOf_dvd_iff_zpow_eq_one.mpr hk

theorem exists_isotropic_of_fpf {s : ℕ} (hs : s.Prime) (hs5 : s ≠ 5) (hV : ∀ v : V, v ^ s = 1)
    (hx : x ^ 5 = 1) (hW : ∀ v ∈ W, x • v ∈ W) (hfpf : ∀ v ∈ W, x • v = v → v = 1)
    {β : MulAut V} (hβ : ∀ v, β (x • v) = x ^ 2 • β v) (hβW : ∀ v ∈ W, β v ∈ W)
    (B : V →* V →* Z) (hB : ∀ u v, B (x • u) (x • v) = B u v) (halt : ∀ v, B v v = 1) {w : V}
    (hw : w ∈ W) (hw1 : w ≠ 1) : ∃ w' ∈ W, w' ∉ zpowers w ∧ B w w' = 1 := by
  by_cases hcase : x • w * x ^ 4 • w ∈ zpowers w
  swap
  · exact ⟨_, mul_mem (hW w hw) (pow_smul_mem hW 4 hw), hcase,
      pairing_smul_mul_pow_four_smul_self hx B hB halt w⟩
  obtain ⟨l, hl⟩ := mem_zpowers_iff.mp hcase
  have h2 := smul_mul_pow_four_smul_sq hx hW hfpf hw
  rw [← hl, smul_mul_pow_four_smul_zpow, ← hl, ← zpow_mul, ← zpow_add] at h2
  have hdvd : (s : ℤ) ∣ l * l + l - 1 := by
    refine dvd_of_zpow_eq_one hs (hV w) hw1 ?_
    rw [zpow_sub, zpow_one, h2, mul_inv_cancel]
  have hndvd := not_dvd_two_mul_add_one hs hs5 hdvd
  have hu1 : β w ≠ 1 := fun h => hw1 (β.injective (h.trans (map_one β).symm))
  have hTu : x • β w * x ^ 4 • β w = β w ^ (-(l + 1)) := by
    rw [smul_mul_pow_four_smul_apply hx hW hfpf hβ hw, ← hl, ← zpow_one_add, ← zpow_neg,
      map_zpow, add_comm]
  refine ⟨β w, hβW w hw, fun hmem => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    have h1 : x • β w * x ^ 4 • β w = β w ^ l := by
      rw [← hk, smul_mul_pow_four_smul_zpow, ← hl, ← zpow_mul, ← zpow_mul, mul_comm]
    refine hndvd (dvd_of_zpow_eq_one hs (hV _) hu1 ?_)
    rw [show 2 * l + 1 = l - -(l + 1) by ring, zpow_sub, ← h1, hTu, mul_inv_cancel]
  · have hself := pairing_smul_mul_pow_four_smul_left hx B hB w (β w)
    rw [← hl, hTu, map_zpow, map_zpow, MonoidHom.zpow_apply] at hself
    by_contra hne
    have hBs : B w (β w) ^ s = 1 := by rw [← map_pow, hV, map_one]
    refine hndvd (dvd_of_zpow_eq_one hs hBs hne ?_)
    rw [show 2 * l + 1 = l - -(l + 1) by ring, zpow_sub, hself, mul_inv_cancel]

end Isotropic

end CFSG.AGLEmbedding
