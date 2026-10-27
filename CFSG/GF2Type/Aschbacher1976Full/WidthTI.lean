module

public import CFSG.GF2Type.Aschbacher1976Full.WidthCore

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Width

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} :
    x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold conjugate
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
    show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ ∈ H
    rw [e]
    exact hy
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
    group

theorem conjugate_conjugate (H : Subgroup G) (g g' : G) :
    conjugate (conjugate H g) g' = conjugate H (g * g') := by
  ext x
  have e : g * (g' * x * g'⁻¹) * g⁻¹ = g * g' * x * (g * g')⁻¹ := by group
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff, e]

section TI

variable {z : G} {w : ℕ} {Z A : Subgroup G}

theorem conjugate_Z_of_mem_H (hD : Z4Data z w Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    {c : G} (hc : c ∈ Hz z) : conjugate Z c = Z := by
  ext x
  rw [mem_conjugate_iff]
  constructor
  · intro hx
    have h := Z_conj_mem hD hz (Subgroup.inv_mem _ hc) hx
    have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
    rw [← e]
    exact h
  · intro hx
    exact Z_conj_mem hD hz hc hx

theorem conjugate_Z_mul_of_mem (hD : Z4Data z w Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 (Fz z)) {c x : G} (hc : c ∈ Hz z) :
    conjugate Z (c * x) = conjugate Z x := by
  rw [← conjugate_conjugate, conjugate_Z_of_mem_H hD hz hF2 hc]

theorem exists_gen_Z (hD : Z4Data z w Z A) (hz : orderOf z = 2) :
    ∃ k : G, k ∈ Z ∧ orderOf k = 4 ∧ (∀ x ∈ Z, ∃ i : ℤ, x = k ^ i) ∧ k ^ 2 = z := by
  haveI := hD.cyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Z)
  have hord : orderOf g = 4 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hD.card_Z]
  have hk4 : (g : G) ^ 4 = 1 := by
    have h1 := congrArg Subtype.val (pow_orderOf_eq_one g)
    rw [hord] at h1
    simpa using h1
  have hkord : orderOf (g : G) = 4 := by rw [Subgroup.orderOf_coe, hord]
  have hkZ : (g : G) ∈ Z := g.2
  refine ⟨g, hkZ, hkord, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    refine ⟨i, ?_⟩
    have := congrArg Subtype.val hi
    simpa using this.symm
  · have hsq : (g : G) ^ 2 ≠ 1 := by
      intro h
      have h4 : orderOf (g : G) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hkord] at h4
      norm_num at h4
    have hsq2 : ((g : G) ^ 2) ^ 2 = 1 := by
      rw [← pow_mul]
      exact hk4
    exact involution_eq hD hz (Z.pow_mem hkZ 2) hsq2 hsq

theorem sq_trivial (hD : Z4Data z w Z A) (hz : orderOf z = 2) {h : G} (hh : h ∈ Hz z) :
    ∀ x ∈ Z, h * (h * x * h⁻¹) * h⁻¹ = x := by
  obtain ⟨k, hkZ, hkord, hgen, hk2⟩ := exists_gen_Z hD hz
  have hk4 : k ^ (4 : ℤ) = 1 := by
    rw [zpow_ofNat, ← hkord]
    exact pow_orderOf_eq_one k
  have hzc : Commute h z := mem_centralizer_singleton_iff.mp hh
  have hy : h * k * h⁻¹ ∈ Z := Z_conj_mem hD hz hh hkZ
  obtain ⟨j, hj⟩ := hgen _ hy
  have hz1 : z ≠ 1 := fun h1 => by simp [h1] at hz
  have hjodd : j % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · exfalso
      obtain ⟨i, hi⟩ : ∃ i : ℤ, j = 2 * i := ⟨j / 2, by omega⟩
      have hu : h * k * h⁻¹ = z ^ i := by
        rw [hj, hi, zpow_mul, zpow_ofNat, hk2]
      have hkz : k ∈ zpowers z := by
        have hcomm : Commute h (z ^ i) := hzc.zpow_right i
        have hk : k = z ^ i := by
          calc k = h⁻¹ * (h * k * h⁻¹) * h := by group
            _ = h⁻¹ * (z ^ i) * h := by rw [hu]
            _ = h⁻¹ * (z ^ i * h) := by group
            _ = h⁻¹ * (h * z ^ i) := by rw [← hcomm.eq]
            _ = z ^ i := by group
        rw [hk]
        exact zpow_mem_zpowers z i
      rcases mem_zpowers_involution hz hkz with h2 | h2
      · apply hz1
        rw [h2, one_pow] at hk2
        exact hk2.symm
      · apply hz1
        rw [h2] at hk2
        have hz2 := z_sq hz
        rw [hk2] at hz2
        exact hz2
    · exact h1
  obtain ⟨i, hi⟩ : ∃ i : ℤ, j = 2 * i + 1 := ⟨j / 2, by omega⟩
  have hbase : h * (h * k * h⁻¹) * h⁻¹ = k := by
    rw [hj, ← conj_zpow, hj, ← zpow_mul]
    have hjj : j * j = 4 * (i * i + i) + 1 := by rw [hi]; ring
    rw [hjj, zpow_add, zpow_mul, hk4, one_zpow, one_mul, zpow_one]
  intro x hx
  obtain ⟨m, rfl⟩ := hgen x hx
  rw [← conj_zpow, ← conj_zpow, hbase]

theorem conj_pair_eq_or_disjoint (hD : Z4Data z w Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 (Fz z)) (x y : G) :
    conjugate Z x = conjugate Z y ∨ conjugate Z x ⊓ conjugate Z y = ⊥ := by
  by_cases hne : conjugate Z x = conjugate Z y
  · exact Or.inl hne
  right
  by_contra hbot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : ∀ g : G, Nat.card ↥(conjugate Z g) = 4 := fun g => by
    unfold conjugate
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hD.card_Z]
  have hdvd : Nat.card ↥(conjugate Z x ⊓ conjugate Z y) ∣ 2 ^ 2 := by
    have h1 := Subgroup.card_dvd_of_le (inf_le_left : conjugate Z x ⊓ conjugate Z y ≤ conjugate Z x)
    rw [hcard x] at h1
    simpa using h1
  have hne1 : Nat.card ↥(conjugate Z x ⊓ conjugate Z y) ≠ 1 := by
    rw [Ne, Subgroup.card_eq_one]
    exact hbot
  have h2dvd : 2 ∣ Nat.card ↥(conjugate Z x ⊓ conjugate Z y) := by
    obtain ⟨i, hi, hi2⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases i
    · exact absurd (by simpa using hi2) hne1
    · rw [hi2]; norm_num
    · rw [hi2]; norm_num
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(conjugate Z x ⊓ conjugate Z y)) 2 h2dvd
  have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have hs2 : (t : G) ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ht2]
  have hs1 : (t : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht2
    omega
  have htx : (t : G) ∈ conjugate Z x := t.2.1
  have hty : (t : G) ∈ conjugate Z y := t.2.2
  have hxs : x * (t : G) * x⁻¹ = z := by
    apply involution_eq hD hz (mem_conjugate_iff.mp htx)
    · rw [conj_pow, hs2, mul_one, mul_inv_cancel]
    · intro h1
      apply hs1
      calc (t : G) = x⁻¹ * (x * (t : G) * x⁻¹) * x := by group
        _ = x⁻¹ * 1 * x := by rw [h1]
        _ = 1 := by group
  have hys : y * (t : G) * y⁻¹ = z := by
    apply involution_eq hD hz (mem_conjugate_iff.mp hty)
    · rw [conj_pow, hs2, mul_one, mul_inv_cancel]
    · intro h1
      apply hs1
      calc (t : G) = y⁻¹ * (y * (t : G) * y⁻¹) * y := by group
        _ = y⁻¹ * 1 * y := by rw [h1]
        _ = 1 := by group
  have hcz : x * y⁻¹ * z = z * (x * y⁻¹) := by
    calc x * y⁻¹ * z = x * y⁻¹ * (y * (t : G) * y⁻¹) := by rw [← hys]
      _ = x * (t : G) * y⁻¹ := by group
      _ = (x * (t : G) * x⁻¹) * (x * y⁻¹) := by group
      _ = z * (x * y⁻¹) := by rw [hxs]
  have hc : x * y⁻¹ ∈ Hz z := mem_centralizer_singleton_iff.mpr hcz
  have e : conjugate Z (x * y⁻¹ * y) = conjugate Z y := conjugate_Z_mul_of_mem hD hz hF2 hc
  rw [show x * y⁻¹ * y = x by group] at e
  exact hne e

theorem conjugate_le_H_of_comm (hD : Z4Data z w Z A) (hz : orderOf z = 2)
    {g : G} (hcomm : g⁻¹ * z * g ∈ centralizer (Z : Set G)) :
    ∀ x ∈ Z, g⁻¹ * x * g ∈ Hz z := by
  obtain ⟨k, hkZ, hkord, hgen, hk2⟩ := exists_gen_Z hD hz
  have hk_comm : k * (g⁻¹ * z * g) = (g⁻¹ * z * g) * k := mem_centralizer_iff.mp hcomm k hkZ
  have hh : g * k * g⁻¹ ∈ Hz z := by
    rw [mem_centralizer_singleton_iff]
    calc g * k * g⁻¹ * z = g * (k * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * k) * g⁻¹ := by rw [hk_comm]
      _ = z * (g * k * g⁻¹) := by group
  intro x hx
  have hsq := sq_trivial hD hz hh x hx
  set h := g * k * g⁻¹ with hhdef
  have hxh : h * h * x = x * (h * h) := by
    calc h * h * x = (h * (h * x * h⁻¹) * h⁻¹) * (h * h) := by group
      _ = x * (h * h) := by rw [hsq]
  have hzeq : z = g⁻¹ * (h * h) * g := by
    rw [← hk2, hhdef, sq]
    group
  rw [mem_centralizer_singleton_iff, hzeq]
  calc g⁻¹ * x * g * (g⁻¹ * (h * h) * g) = g⁻¹ * (x * (h * h)) * g := by group
    _ = g⁻¹ * (h * h * x) * g := by rw [hxh]
    _ = g⁻¹ * (h * h) * g * (g⁻¹ * x * g) := by group

end TI

end CFSG.GF2Type.Aschbacher1976Full.Width
