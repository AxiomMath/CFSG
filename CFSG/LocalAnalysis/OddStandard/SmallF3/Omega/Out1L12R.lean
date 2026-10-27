module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1L12Def
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.OddStandard.SmallF3.Omega

private abbrev aor_E12 : Type := Multiplicative (ZMod 2) × Multiplicative (ZMod 4)

private def aor_u12 : aor_E12 :=
  (Multiplicative.ofAdd (0 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 4))

private def aor_z12 : aor_E12 :=
  (Multiplicative.ofAdd (0 : ZMod 2), Multiplicative.ofAdd (2 : ZMod 4))

private lemma aor_E12_card : Nat.card aor_E12 = 8 := by
  rw [Nat.card_prod,
    ← Nat.card_congr (Multiplicative.ofAdd (α := ZMod 2)),
    ← Nat.card_congr (Multiplicative.ofAdd (α := ZMod 4)),
    Nat.card_zmod, Nat.card_zmod]

private lemma aor_E12_sq (e : aor_E12) : e ^ 2 = 1 ∨ e ^ 2 = aor_z12 := by
  revert e
  decide

private lemma aor_E12_coord_fin : ∀ a : aor_E12, a ^ 2 = 1 → a ≠ 1 → a ≠ aor_z12 →
    ∀ b : aor_E12, ∃ i : Fin 4, ∃ j : Fin 2,
      b = aor_u12 ^ (i : ℕ) * a ^ (j : ℕ) := by
  intro a
  fin_cases a <;> decide

private lemma aor_E12_coord (a : aor_E12) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1)
    (haz : a ≠ aor_z12) (b : aor_E12) :
    ∃ i j : ℕ, b = aor_u12 ^ i * a ^ j := by
  obtain ⟨i, j, hij⟩ := aor_E12_coord_fin a ha2 ha1 haz b
  exact ⟨i, j, hij⟩

private lemma aor_E12_u12_order : orderOf aor_u12 = 4 := by
  have h : orderOf aor_u12 = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (x := aor_u12) (p := 2) (n := 1) (by decide) (by decide)
  rw [show (2 : ℕ) ^ (1 + 1) = 4 by decide] at h
  exact h

private lemma aor_E12_mem_zpowers_iff (a : aor_E12) :
    a ∈ Subgroup.zpowers aor_u12 ↔ ∃ i : Fin 4, aor_u12 ^ (i : ℕ) = a := by
  rw [mem_zpowers_iff_mem_range_orderOf (x := aor_u12) (y := a), aor_E12_u12_order]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, hna⟩
    exact ⟨⟨n, hn⟩, hna⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, i.isLt, hi⟩

private lemma aor_E12_notMem_zpowers (a : aor_E12) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1)
    (haz : a ≠ aor_z12) : a ∉ Subgroup.zpowers aor_u12 := by
  rw [aor_E12_mem_zpowers_iff]
  rintro ⟨i, hi⟩
  fin_cases i
  · exact ha1 (by rw [← hi]; decide)
  · have hP : (aor_u12 ^ (1 : ℕ)) ^ 2 = 1 := by rw [hi]; exact ha2
    exact absurd hP (by decide)
  · exact haz (by rw [← hi]; decide)
  · have hP : (aor_u12 ^ (3 : ℕ)) ^ 2 = 1 := by rw [hi]; exact ha2
    exact absurd hP (by decide)

theorem aor_l12_coord_or_square {S : Type} [Group S] {t : S} (ht : orderOf t = 2)
    (hR : Nonempty (↥(Subgroup.centralizer ({t} : Set S)) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 4)))) :
    (∃ u : S, L12Coord S t u) ∨ ∃ x : S, x * t = t * x ∧ x ^ 2 = t := by
  obtain ⟨φ⟩ := hR
  let t' : L12R t := ⟨t, (Subgroup.mem_centralizer_singleton_iff).mpr rfl⟩
  let a : aor_E12 := φ t'
  have ht' : orderOf t' = 2 := by
    change orderOf (⟨t, (Subgroup.mem_centralizer_singleton_iff).mpr rfl⟩ : L12R t) = 2
    rw [Subgroup.orderOf_mk, ht]
  have ha_order : orderOf a = 2 := (MulEquiv.orderOf_eq φ t').trans ht'
  have ha2 : a ^ 2 = 1 := ((orderOf_eq_iff (by decide : (0 : ℕ) < 2)).mp ha_order).1
  have hane : a ≠ 1 := by
    have h := ((orderOf_eq_iff (by decide : (0 : ℕ) < 2)).mp ha_order).2 1
      (by decide) (by decide)
    simpa using h
  let y : L12R t := φ.symm aor_u12
  have hyu : φ y = aor_u12 := by
    change φ (φ.symm aor_u12) = aor_u12
    exact MulEquiv.apply_symm_apply φ aor_u12
  by_cases haz : a = aor_z12
  · right
    refine ⟨(y : S), ?_, ?_⟩
    · exact (Subgroup.mem_centralizer_singleton_iff).mp y.property
    · have hu2 : aor_u12 ^ 2 = aor_z12 := by decide
      have h1 : φ (y ^ 2) = φ t' := by
        rw [map_pow, hyu, hu2, ← haz]
      have hy2 : y ^ 2 = t' := φ.injective h1
      have hcoe := congrArg (Subgroup.subtype (L12R t)) hy2
      rw [map_pow] at hcoe
      simpa using hcoe
  · left
    refine ⟨(y : S), ?_⟩
    refine ⟨ht, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq φ y, hyu, aor_E12_u12_order]
    · exact (Subgroup.mem_centralizer_singleton_iff).mp y.property
    · intro htmem
      have ht'mem : t' ∈ Subgroup.zpowers y := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htmem
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
        apply Subtype.ext
        change (Subgroup.subtype (L12R t)) (y ^ k) = t
        rw [map_zpow]
        exact hk
      have ha_mem : a ∈ Subgroup.zpowers aor_u12 := by
        change φ t' ∈ Subgroup.zpowers aor_u12
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht'mem
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨k, ?_⟩
        calc aor_u12 ^ k = (φ y) ^ k := (congrArg (fun z => z ^ k) hyu).symm
          _ = φ (y ^ k) := (map_zpow φ.toMonoidHom y k).symm
          _ = φ t' := congrArg φ hk
      exact (aor_E12_notMem_zpowers a ha2 hane haz) ha_mem
    · intro x hx
      let x' : L12R t := ⟨x, (Subgroup.mem_centralizer_singleton_iff).mpr hx⟩
      obtain ⟨i, j, hij⟩ := aor_E12_coord a ha2 hane haz (φ x')
      refine ⟨i, j, ?_⟩
      have hx' : x' = y ^ i * t' ^ j := by
        apply φ.injective
        rw [map_mul, map_pow, map_pow, hyu, hij]
      have hcoe := congrArg (Subgroup.subtype (L12R t)) hx'
      rw [map_mul, map_pow, map_pow] at hcoe
      simpa using hcoe
    · rw [Nat.card_congr φ.toEquiv, aor_E12_card]

theorem aor_l12_card_of_central {S : Type} [Group S] {t : S}
    (hR : Nonempty (↥(Subgroup.centralizer ({t} : Set S)) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 4))))
    (hc : ∀ x : S, x * t = t * x) : Nat.card S = 8 := by
  obtain ⟨φ⟩ := hR
  have htop : L12R t = ⊤ := by
    rw [Subgroup.eq_top_iff' (L12R t)]
    intro x
    exact (Subgroup.mem_centralizer_singleton_iff).mpr (hc x)
  calc Nat.card S = Nat.card (↥(⊤ : Subgroup S)) := by rw [Subgroup.card_top]
    _ = Nat.card (↥(L12R t)) := by rw [htop]
    _ = Nat.card aor_E12 := Nat.card_congr φ.toEquiv
    _ = 8 := aor_E12_card

theorem aor_l12_card_of_square {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S) {t : S}
    (hR : Nonempty (↥(Subgroup.centralizer ({t} : Set S)) ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 4))))
    (hsq : ∃ x : S, x * t = t * x ∧ x ^ 2 = t) : Nat.card S = 8 := by
  by_cases ht1 : t = 1
  · refine aor_l12_card_of_central hR (fun y => ?_)
    rw [ht1, mul_one, one_mul]
  · obtain ⟨φ⟩ := hR
    obtain ⟨x, hxt, hx2⟩ := hsq
    let t' : L12R t := ⟨t, (Subgroup.mem_centralizer_singleton_iff).mpr rfl⟩
    let a : aor_E12 := φ t'
    let x' : L12R t := ⟨x, (Subgroup.mem_centralizer_singleton_iff).mpr hxt⟩
    have hx'2 : x' ^ 2 = t' := by
      apply Subtype.ext
      change (Subgroup.subtype (L12R t)) (x' ^ 2) = t
      rw [map_pow]
      exact hx2
    have ha : a = (φ x') ^ 2 := by
      rw [← map_pow, hx'2]
    have ha_or : a = 1 ∨ a = aor_z12 := by
      rw [ha]
      exact aor_E12_sq (φ x')
    have hane : a ≠ 1 := by
      intro h1
      have hφ : φ t' = 1 := h1
      have ht'_one : t' = 1 := by
        apply φ.injective
        rw [hφ, map_one]
      exact ht1 (congrArg (Subgroup.subtype (L12R t)) ht'_one)
    have haz : a = aor_z12 := ha_or.resolve_left hane
    have hsq_R : ∀ y : L12R t, y ^ 2 = 1 ∨ y ^ 2 = t' := by
      intro y
      have h := aor_E12_sq (φ y)
      rw [← map_pow] at h
      rcases h with h | h
      · left
        exact φ.injective (h.trans (map_one φ).symm)
      · right
        exact φ.injective (h.trans haz.symm)
    have hNR : L12N t ≤ L12R t := by
      intro n hn
      have hxR : x ∈ L12R t := (Subgroup.mem_centralizer_singleton_iff).mpr hxt
      have hnxR : n * x * n⁻¹ ∈ L12R t := (Subgroup.mem_normalizer_iff.mp hn x).mp hxR
      have hconj : (n * x * n⁻¹) ^ 2 = n * t * n⁻¹ := by
        rw [conj_pow, hx2]
      have hcases : n * t * n⁻¹ = 1 ∨ n * t * n⁻¹ = t := by
        have hsq := hsq_R ⟨n * x * n⁻¹, hnxR⟩
        rcases hsq with h | h
        · left
          rw [← hconj]
          have hcoe := congrArg (Subgroup.subtype (L12R t)) h
          rw [map_pow] at hcoe
          simpa using hcoe
        · right
          rw [← hconj]
          have hcoe := congrArg (Subgroup.subtype (L12R t)) h
          rw [map_pow] at hcoe
          simpa using hcoe
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases hcases with h1 | htconj
      · exfalso
        have hnt : n * t = n := by
          calc n * t = (n * t * n⁻¹) * n := by rw [mul_assoc, inv_mul_cancel, mul_one]
            _ = 1 * n := by rw [h1]
            _ = n := one_mul n
        have h' : n * t = n * 1 := by simpa using hnt
        exact ht1 (mul_left_cancel h')
      · calc n * t = (n * t * n⁻¹) * n := by rw [mul_assoc, inv_mul_cancel, mul_one]
          _ = t * n := by rw [htconj]
    have hle : L12R t ≤ L12N t := Subgroup.le_normalizer
    have hRN : L12N t = L12R t := le_antisymm hNR hle
    haveI : Group.IsNilpotent S := hS.isNilpotent
    have htop : L12R t = ⊤ :=
      (normalizerCondition_iff_only_full_group_self_normalizing.mp
        (Group.normalizerCondition_of_isNilpotent (G := S))) (L12R t) hRN
    refine aor_l12_card_of_central ⟨φ⟩ (fun z => ?_)
    exact (Subgroup.mem_centralizer_singleton_iff).mp
      ((le_of_eq htop.symm) (Subgroup.mem_top z))

end CFSG.OddStandard.SmallF3.Omega
