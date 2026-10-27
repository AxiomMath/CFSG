module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec67_conjugate_eq_of_centralizer {L : Subgroup G} {g : G}
    (hg : g ∈ centralizer (L : Set G)) : CFSG.conjugate L g = L := by
  have hfix : ∀ x ∈ L, g * x * g⁻¹ = x := by
    intro x hx
    rw [← Subgroup.mem_centralizer_iff.mp hg x hx, mul_inv_cancel_right]
  have hfix' : ∀ x ∈ L, g⁻¹ * x * g = x := by
    intro x hx
    have h := Subgroup.mem_centralizer_iff.mp ((centralizer (L : Set G)).inv_mem hg) x hx
    rw [← h, mul_assoc, inv_mul_cancel, mul_one]
  ext x
  rw [mem_conjugate_iff]
  constructor
  · intro hx
    have h1 : g⁻¹ * (g * x * g⁻¹) * g = g * x * g⁻¹ := hfix' _ hx
    have h2 : x = g * x * g⁻¹ := by rw [← h1]; group
    rw [h2]
    exact hx
  · intro hx
    rw [hfix x hx]
    exact hx

theorem sec67_conj_mem_centralizer {L : Subgroup G} {t y : G}
    (htC : t ∈ centralizer (L : Set G)) (hyN : y ∈ normalizer (L : Set G)) :
    y * t * y⁻¹ ∈ centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hyinv : y⁻¹ ∈ normalizer (L : Set G) := (normalizer (L : Set G)).inv_mem hyN
  have hl' : y⁻¹ * l * y ∈ L := by
    have h := (Subgroup.mem_normalizer_iff.mp hyinv l).mp hl
    simpa using h
  have h := Subgroup.mem_centralizer_iff.mp htC _ hl'
  calc l * (y * t * y⁻¹) = y * ((y⁻¹ * l * y) * t) * y⁻¹ := by group
    _ = y * (t * (y⁻¹ * l * y)) * y⁻¹ := by rw [h]
    _ = (y * t * y⁻¹) * l := by group

theorem sec67_odd_order [Finite G] {L : Subgroup G}
    (hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (L : Set G)) → IsCyclic P)
    {t y : G} (ht2 : orderOf t = 2) (htC : t ∈ centralizer (L : Set G))
    (hy2 : orderOf y = 2) (hyN : y ∈ normalizer (L : Set G)) :
    Odd (orderOf (t * (y * t * y⁻¹))) := by
  set t' := y * t * y⁻¹ with ht'def
  set w := t * t' with hw
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have h2dvd : 2 ∣ orderOf w := even_iff_two_dvd.mp hodd
  have hpos : orderOf w ≠ 0 := (orderOf_pos w).ne'
  have ht2' : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have ht'C : t' ∈ centralizer (L : Set G) := by
    rw [ht'def]
    exact sec67_conj_mem_centralizer htC hyN
  have ht'2 : orderOf t' = 2 := by
    have hconj : y * t * y⁻¹ = (y⁻¹)⁻¹ * t * y⁻¹ := by rw [inv_inv]
    rw [ht'def, hconj, orderOf_conjugate_eq, ht2]
  have ht'' : t' * t' = 1 := by rw [← pow_two, ← ht'2, pow_orderOf_eq_one]
  have hwC : w ∈ centralizer (L : Set G) := by
    rw [hw]
    exact mul_mem htC ht'C
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2'
  have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht''
  have hwinv : w⁻¹ = t' * t := by rw [hw, mul_inv_rev, ht'inv, htinv]
  have htw : t * w * t⁻¹ = w⁻¹ := by
    calc t * w * t⁻¹ = t * (t * t') * t⁻¹ := by rw [hw]
      _ = (t * t) * (t' * t⁻¹) := by group
      _ = t' * t⁻¹ := by rw [ht2', one_mul]
      _ = t' * t := by rw [htinv]
      _ = w⁻¹ := hwinv.symm
  have ht'w : t' * w * t'⁻¹ = w⁻¹ := by
    calc t' * w * t'⁻¹ = t' * (t * t') * t'⁻¹ := by rw [hw]
      _ = (t' * t) * (t' * t'⁻¹) := by group
      _ = t' * t := by rw [mul_inv_cancel, mul_one]
      _ = w⁻¹ := hwinv.symm
  set e := w ^ (orderOf w / 2) with he
  have he2 : orderOf e = 2 := by
    rw [he]
    exact orderOf_pow_orderOf_div hpos h2dvd
  have hee : e * e = 1 := by rw [← pow_two, ← he2, pow_orderOf_eq_one]
  have heC : e ∈ centralizer (L : Set G) := by
    rw [he]
    exact (centralizer (L : Set G)).pow_mem hwC _
  have hte : t * e * t⁻¹ = e := by
    have h1 : t * e * t⁻¹ = e⁻¹ := by rw [he, ← conj_pow, htw, inv_pow]
    rw [h1, inv_eq_of_mul_eq_one_right hee]
  have hcommt : e * t = t * e := by
    calc e * t = (t * e * t⁻¹) * t := by rw [hte]
      _ = t * e * (t⁻¹ * t) := by group
      _ = t * e := by rw [inv_mul_cancel, mul_one]
  rcases eq_one_or_eq_of_commute hcyc heC htC hee ht2 hcommt with he1 | het
  · rw [he1, orderOf_one] at he2
    exact absurd he2 (by decide)
  have ht'e : t' * e * t'⁻¹ = e := by
    have h1 : t' * e * t'⁻¹ = e⁻¹ := by rw [he, ← conj_pow, ht'w, inv_pow]
    rw [h1, inv_eq_of_mul_eq_one_right hee]
  have hcommt' : e * t' = t' * e := by
    calc e * t' = (t' * e * t'⁻¹) * t' := by rw [ht'e]
      _ = t' * e * (t'⁻¹ * t') := by group
      _ = t' * e := by rw [inv_mul_cancel, mul_one]
  rcases eq_one_or_eq_of_commute hcyc heC ht'C hee ht'2 hcommt' with he1 | het'
  · rw [he1, orderOf_one] at he2
    exact absurd he2 (by decide)
  have htt' : t = t' := het.symm.trans het'
  have hw1 : w = 1 := by
    calc w = t * t' := hw
      _ = t' * t' := by rw [htt']
      _ = 1 := ht''
  rw [hw1, orderOf_one] at hodd
  exact Nat.not_even_one hodd

theorem sec67_exists_root {w : G} (hw : Odd (orderOf w)) : ∃ k : ℕ, w ^ (4 * k) = w⁻¹ := by
  obtain ⟨a, ha⟩ := hw
  rcases Nat.even_or_odd' a with ⟨b, hb | hb⟩
  · refine ⟨b, ?_⟩
    have hord : orderOf w = 4 * b + 1 := by rw [ha, hb]; omega
    have hpow : w ^ (4 * b) * w = 1 := by
      rw [← pow_succ, ← hord, pow_orderOf_eq_one]
    exact eq_inv_of_mul_eq_one_left hpow
  · refine ⟨3 * b + 2, ?_⟩
    have hord : orderOf w = 4 * b + 3 := by rw [ha, hb]; omega
    have hk : 4 * (3 * b + 2) + 1 = orderOf w * 3 := by rw [hord]; omega
    have hpow : w ^ (4 * (3 * b + 2)) * w = 1 := by
      rw [← pow_succ, hk, pow_mul, pow_orderOf_eq_one, one_pow]
    exact eq_inv_of_mul_eq_one_left hpow

theorem sec67_dihedral_commute {t y : G} (ht2 : t * t = 1) (hy2 : y * y = 1) {k : ℕ}
    (hk : (t * (y * t * y⁻¹)) ^ (4 * k) = (t * (y * t * y⁻¹))⁻¹) :
    y * ((t * (y * t * y⁻¹)) ^ k * t * ((t * (y * t * y⁻¹)) ^ k)⁻¹) =
      ((t * (y * t * y⁻¹)) ^ k * t * ((t * (y * t * y⁻¹)) ^ k)⁻¹) * y := by
  set t' := y * t * y⁻¹ with ht'def
  set w := t * t' with hw
  set v := w ^ k with hv
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have ht'2 : t' * t' = 1 := by
    rw [ht'def]
    calc (y * t * y⁻¹) * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
      _ = y * 1 * y⁻¹ := by rw [ht2]
      _ = 1 := by group
  have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
  have hwinv : w⁻¹ = t' * t := by rw [hw, mul_inv_rev, ht'inv, htinv]
  have htw : t * w * t⁻¹ = w⁻¹ := by
    calc t * w * t⁻¹ = t * (t * t') * t⁻¹ := by rw [hw]
      _ = (t * t) * (t' * t⁻¹) := by group
      _ = t' * t⁻¹ := by rw [ht2, one_mul]
      _ = t' * t := by rw [htinv]
      _ = w⁻¹ := hwinv.symm
  have hyt' : y * t' * y⁻¹ = t := by
    rw [ht'def]
    calc y * (y * t * y⁻¹) * y⁻¹ = (y * y) * t * (y⁻¹ * y⁻¹) := by group
      _ = t := by rw [hy2, hyinv, hy2]; group
  have hyw : y * w * y⁻¹ = w⁻¹ := by
    calc y * w * y⁻¹ = y * (t * t') * y⁻¹ := by rw [hw]
      _ = (y * t * y⁻¹) * (y * t' * y⁻¹) := by group
      _ = t' * t := by rw [← ht'def, hyt']
      _ = w⁻¹ := hwinv.symm
  have hyv : y * v * y⁻¹ = v⁻¹ := by
    rw [hv, ← conj_pow, hyw, inv_pow]
  have hyvinv : y * v⁻¹ * y⁻¹ = v := by
    have h : y * v⁻¹ * y⁻¹ = (y * v * y⁻¹)⁻¹ := by group
    rw [h, hyv, inv_inv]
  have htv : t * v * t⁻¹ = v⁻¹ := by
    rw [hv, ← conj_pow, htw, inv_pow]
  have htvinv : t * v⁻¹ * t⁻¹ = v := by
    have h : t * v⁻¹ * t⁻¹ = (t * v * t⁻¹)⁻¹ := by group
    rw [h, htv, inv_inv]
  have htv' : t * v⁻¹ = v * t := by
    calc t * v⁻¹ = (t * v⁻¹ * t⁻¹) * t := by group
      _ = v * t := by rw [htvinv]
  have htv'' : t * v = v⁻¹ * t := by
    calc t * v = (t * v * t⁻¹) * t := by group
      _ = v⁻¹ * t := by rw [htv]
  have ht'w : t' = w⁻¹ * t := by rw [hwinv, mul_assoc, ht2, mul_one]
  have hv4 : v ^ 4 = w⁻¹ := by
    rw [hv, ← pow_mul, show k * 4 = 4 * k by omega, hk]
  have hYX : y * (v * t * v⁻¹) * y⁻¹ = v⁻¹ * t' * v := by
    calc y * (v * t * v⁻¹) * y⁻¹
        = (y * v * y⁻¹) * (y * t * y⁻¹) * (y * v⁻¹ * y⁻¹) := by group
      _ = v⁻¹ * t' * v := by rw [hyv, hyvinv, ← ht'def]
  have hL : v⁻¹ * t' * v = t * (v⁻¹) ^ 2 := by
    calc v⁻¹ * t' * v = v⁻¹ * (v ^ 4 * t) * v := by rw [ht'w, ← hv4]
      _ = v ^ 3 * (t * v) := by group
      _ = v ^ 3 * (v⁻¹ * t) := by rw [htv'']
      _ = v ^ 2 * t := by group
      _ = v * (v * t) := by rw [pow_two]; group
      _ = v * (t * v⁻¹) := by rw [htv'.symm]
      _ = (v * t) * v⁻¹ := by group
      _ = (t * v⁻¹) * v⁻¹ := by rw [htv'.symm]
      _ = t * (v⁻¹) ^ 2 := by rw [pow_two]; group
  have hR : v * t * v⁻¹ = t * (v⁻¹) ^ 2 := by
    calc v * t * v⁻¹ = (v * t) * v⁻¹ := rfl
      _ = (t * v⁻¹) * v⁻¹ := by rw [htv'.symm]
      _ = t * (v⁻¹) ^ 2 := by rw [pow_two]; group
  have hfinal : y * (v * t * v⁻¹) * y⁻¹ = v * t * v⁻¹ :=
    hYX.trans (hL.trans hR.symm)
  rwa [mul_inv_eq_iff_eq_mul] at hfinal

theorem sec67_reduce [Finite G] {L : Subgroup G}
    (hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (L : Set G)) → IsCyclic P)
    {t y : G} (ht2 : orderOf t = 2) (htC : t ∈ centralizer (L : Set G))
    (hy2 : orderOf y = 2) (hyN : y ∈ normalizer (L : Set G)) :
    ∃ v ∈ centralizer (L : Set G), y * (v * t * v⁻¹) = (v * t * v⁻¹) * y := by
  have ht2' : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hy2' : y * y = 1 := by rw [← pow_two, ← hy2, pow_orderOf_eq_one]
  have ht'C : y * t * y⁻¹ ∈ centralizer (L : Set G) :=
    sec67_conj_mem_centralizer htC hyN
  have hwC : t * (y * t * y⁻¹) ∈ centralizer (L : Set G) := mul_mem htC ht'C
  have hodd : Odd (orderOf (t * (y * t * y⁻¹))) :=
    sec67_odd_order hcyc ht2 htC hy2 hyN
  obtain ⟨k, hk⟩ := sec67_exists_root hodd
  exact ⟨(t * (y * t * y⁻¹)) ^ k, (centralizer (L : Set G)).pow_mem hwC k,
    sec67_dihedral_commute ht2' hy2' hk⟩

end CFSG.OddStandard.SmallF3.Omega
