module

public import CFSG.LargeExtraspecial.Asc611OutB

public section

namespace CFSG.LargeExtraspecial.Asc611

open Subgroup Matrix CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

namespace SemiInv

variable {S : (Fin m → K) → Fin m → K} (hS : SemiInv S)
include hS

theorem herm_add_add {x y : Fin m → K} (hx : S x = x) (hy : S y = y) :
    herm frob (x + y) (x + y) = herm frob x x + herm frob y y := by
  have h1 : herm frob y x = herm frob x y := by
    rw [herm_conj frob frob_frob x y]
    exact (frob_eq_self_iff _).mpr (hS.herm_fix hx hy)
  rw [herm_add_left, herm_add_right, herm_add_right, h1]
  linear_combination (herm frob x y) * two_eq_zero

theorem herm_symm {x y : Fin m → K} (hx : S x = x) (hy : S y = y) :
    herm frob y x = herm frob x y := by
  rw [herm_conj frob frob_frob x y]
  exact (frob_eq_self_iff _).mpr (hS.herm_fix hx hy)

theorem eq_zero_or_char {d : Fin m → K} (hd : S d = d)
    (horth : ∀ v, S v = v → herm frob v v = 0 → herm frob v d = 0) :
    d = 0 ∨ ∀ x, S x = x → herm frob x d = herm frob x x := by
  by_cases hq : ∀ x, S x = x → herm frob x x = 0
  · left
    exact hS.eq_zero_of_herm fun x hx => horth x hx (hq x hx)
  push Not at hq
  obtain ⟨x₀, hx₀, hq₀⟩ := hq
  have hq₀' : herm frob x₀ x₀ = 1 := (herm_self_eq_zero_or_one x₀).resolve_left hq₀
  have hlin : ∀ x, S x = x → herm frob x d = herm frob x x * herm frob x₀ d := by
    intro x hx
    rcases herm_self_eq_zero_or_one x with h0 | h1
    · rw [horth x hx h0, h0, zero_mul]
    · have hfix : S (x + x₀) = x + x₀ := by rw [hS.add, hx, hx₀]
      have hiso : herm frob (x + x₀) (x + x₀) = 0 := by
        rw [hS.herm_add_add hx hx₀, h1, hq₀', add_self_K]
      have h2 := horth _ hfix hiso
      rw [herm_add_left] at h2
      rw [h1, one_mul]
      linear_combination h2 - herm frob x₀ d * two_eq_zero
  rcases hS.herm_fix hx₀ hd with h0 | h1
  · left
    exact hS.eq_zero_of_herm fun x hx => by rw [hlin x hx, h0, mul_zero]
  · right
    intro x hx
    rw [hlin x hx, h1, mul_one]

theorem char_unique {c c' : Fin m → K} (hc : S c = c) (hc' : S c' = c')
    (h : ∀ x, S x = x → herm frob x c = herm frob x x)
    (h' : ∀ x, S x = x → herm frob x c' = herm frob x x) : c = c' := by
  have hd : S (c + c') = c + c' := by rw [hS.add, hc, hc']
  have h0 := hS.eq_zero_of_herm (d := c + c') fun x hx => by
    rw [herm_add_right, h x hx, h' x hx, add_self_K]
  calc c = c + (c + c') := by rw [h0, add_zero]
    _ = c' := by rw [← add_assoc, ← two_smul K c, two_eq_zero, zero_smul, zero_add]

end SemiInv

section Commutators

variable {S : (Fin m → K) → Fin m → K} (hS : SemiInv S) {U : Subgroup (PG m)}
  (hU : IsPGroup 2 U)
  (hnorm : ∀ v : Fin m → K, S v = v → v ≠ 0 → herm frob v v = 0 →
    ∀ u ∈ U, tq v * u * (tq v)⁻¹ ∈ U)
include hS hU hnorm

omit hS in
theorem herm_smul_eq_zero_of_fix (hm : 3 ≤ m) {g : SUid frob m}
    (hgU : (QuotientGroup.mk g : PG m) ∈ U) {v : Fin m → K} (hvS : S v = v) (hv0 : v ≠ 0)
    (hv : herm frob v v = 0) :
    tq (g • v) * tq v ∈ U ∧ herm frob (g • v) v = 0 := by
  have hgv : herm frob (g • v) (g • v) = 0 := by rw [herm_smul_smul, hv]
  have hgv0 : g • v ≠ 0 := (smul_ne_zero_iff_ne g).mpr hv0
  have hmem : tq (g • v) * tq v ∈ U := by
    have h1 := commutator_mem (c := tq v) (hnorm v hvS hv0 hv) hgU
    rwa [conj_tq g hv, inv_eq_of_mul_eq_one_right (tq_mul_self hv)] at h1
  exact ⟨hmem, herm_eq_zero_of_mem hm hU hgv0 hgv hv0 hv hmem⟩

theorem herm_smul_eq_of_fix (hm : 3 ≤ m) {g : SUid frob m}
    (hgU : (QuotientGroup.mk g : PG m) ∈ U) (hgS : ∀ x, S (g • x) = g • S x) {v v'' : Fin m → K}
    (hvS : S v = v) (hv0 : v ≠ 0) (hv : herm frob v v = 0) (hv''S : S v'' = v'')
    (hv''0 : v'' ≠ 0) (hv'' : herm frob v'' v'' = 0) :
    herm frob v'' (g • v) = herm frob v'' v := by
  obtain ⟨hmem, hT1⟩ := herm_smul_eq_zero_of_fix hU hnorm hm hgU hvS hv0 hv
  have hgvS : S (g • v) = g • v := by rw [hgS, hvS]
  have hgv : herm frob (g • v) (g • v) = 0 := by rw [herm_smul_smul, hv]
  set t := tvU (g • v) * tvU v with ht
  have htU : (QuotientGroup.mk t : PG m) ∈ U := by
    rw [ht, QuotientGroup.mk_mul]
    exact hmem
  have h1 := commutator_mem (c := tq v'') (hnorm v'' hv''S hv''0 hv'') htU
  rw [conj_tq t hv'', inv_eq_of_mul_eq_one_right (tq_mul_self hv'')] at h1
  have htv0 : t • v'' ≠ 0 := (smul_ne_zero_iff_ne t).mpr hv''0
  have htv : herm frob (t • v'') (t • v'') = 0 := by rw [herm_smul_smul, hv'']
  have h2 := herm_eq_zero_of_mem hm hU htv0 htv hv''0 hv'' h1
  set α := herm frob v v'' with hα
  set β := herm frob (g • v) v'' with hβ
  have htv' : t • v'' = v'' + α • v + β • (g • v) := by
    rw [ht, mul_smul, tvU_smul hv, tvU_smul hgv, herm_add_right, herm_smul_right, hT1, mul_zero,
      add_zero]
  rw [htv', herm_add_left, herm_add_left, herm_smul_left, herm_smul_left, hv'', ← hα, ← hβ,
    zero_add] at h2
  have hαF := hS.herm_fix hvS hv''S
  have hβF := hS.herm_fix hgvS hv''S
  rw [frob_mul_self_of_mem hαF, frob_mul_self_of_mem hβF] at h2
  have h3 : α = β := by linear_combination h2 - β * two_eq_zero
  rw [hS.herm_symm hgvS hv''S, hS.herm_symm hvS hv''S]
  exact h3.symm

end Commutators

end CFSG.LargeExtraspecial.Asc611
