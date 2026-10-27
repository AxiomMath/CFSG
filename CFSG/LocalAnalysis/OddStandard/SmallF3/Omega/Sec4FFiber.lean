module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FFiberCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FTwoPart

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

private lemma sec4F_sq_eq_one_of_eq_conj (h : Sec4FSetup t L S z A B φ) {y g : G}
    (hy : y = g⁻¹ * t * g) : y * y = 1 := by
  rw [hy]
  calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
    _ = 1 := by rw [h.t_sq]; group

private lemma sec4F_inv_mul_mem_centralizer (h : Sec4FSetup t L S z A B φ) {y y' : G}
    {a b : Option (Fin 7)} (hσ : Sec4MRealizes t φ y (Equiv.swap a b))
    (hσ' : Sec4MRealizes t φ y' (Equiv.swap a b)) :
    y⁻¹ * y' ∈ centralizer (A : Set G) :=
  h.mem_centralizer_iff_realizes_one.mpr (by simpa using hσ.inv.mul hσ')

private lemma sec4F_conj_eq_inv_of_mul_eq_one {y y' c : G} (hy : y * y = 1)
    (hy' : y' * y' = 1) (hc : c = y⁻¹ * y') : y * c * y⁻¹ = c⁻¹ := by
  have hyc : y * c = y' := by rw [hc]; group
  have h1 : (y * c * y) * c = 1 := by rw [mul_assoc, hyc, hy']
  have h2 : y * c * y = c⁻¹ := mul_eq_one_iff_eq_inv.mp h1
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  rw [hyinv, h2]

private lemma sec4F_conj_zpowers_eq_inv {y c v : G} (hyc : y * c * y⁻¹ = c⁻¹)
    (hv : v ∈ Subgroup.zpowers c) : y * v * y⁻¹ = v⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [← conj_zpow, hyc, inv_zpow]

private lemma sec4F_commute_mem_zpowers {c v w : G} (hv : v ∈ Subgroup.zpowers c)
    (hw : w ∈ Subgroup.zpowers c) : v * w = w * v := by
  obtain ⟨kv, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  obtain ⟨kw, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact (Commute.zpow_zpow_self c kv kw).eq

theorem Sec4FSetup.fiber (h : Sec4FSetup t L S z A B φ) {y y' : G}
    (hy : ∃ g : G, y = g⁻¹ * t * g) (hy' : ∃ g : G, y' = g⁻¹ * t * g)
    (hyN : y ∈ normalizer (A : Set G)) (hy'N : y' ∈ normalizer (A : Set G))
    {a b : Option (Fin 7)} (hab : a ≠ b) (hσ : Sec4MRealizes t φ y (Equiv.swap a b))
    (hσ' : Sec4MRealizes t φ y' (Equiv.swap a b)) :
    ∃ o : G, o ∈ centralizer (A : Set G) ∧ Odd (orderOf o) ∧
      (y⁻¹ * y' = o ∨ y⁻¹ * y' = sec4MPt t φ a * sec4MPt t φ b * o) := by
  have hy_copy : ∃ g : G, y = g⁻¹ * t * g := hy
  obtain ⟨g, hy_eq⟩ := hy_copy
  have hy'_copy : ∃ g : G, y' = g⁻¹ * t * g := hy'
  obtain ⟨g', hy'_eq⟩ := hy'_copy
  have hy2 : y * y = 1 := sec4F_sq_eq_one_of_eq_conj h hy_eq
  have hy'2 : y' * y' = 1 := sec4F_sq_eq_one_of_eq_conj h hy'_eq
  have hcC : y⁻¹ * y' ∈ centralizer (A : Set G) :=
    sec4F_inv_mul_mem_centralizer h hσ hσ'
  have hyc : y * (y⁻¹ * y') * y⁻¹ = (y⁻¹ * y')⁻¹ :=
    sec4F_conj_eq_inv_of_mul_eq_one hy2 hy'2 rfl
  obtain ⟨x, o, hxz, hoz, hc, hx2, hodd⟩ := sec4F_two_part (y⁻¹ * y')
  have hxA : x ∈ A := h.cent_two_elt (Subgroup.zpowers_le.mpr hcC hxz) hx2
  have hxsq : x * x = 1 := h.A_sq hxA
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxsq
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hxconj : y * x * y⁻¹ = x := by
    rw [sec4F_conj_zpowers_eq_inv hyc hxz, hxinv]
  have hxcomm : x * y = y * x := by
    have h1 : y * x * y = x := by simpa [hyinv] using hxconj
    calc x * y = y * x * y * y := by rw [h1]
      _ = y * x := by rw [mul_assoc, hy2, mul_one]
  have hodd' : Odd (orderOf o) := hodd
  obtain ⟨j, hj⟩ := hodd'
  let w : G := o ^ (j + 1)
  have hwz : w ∈ Subgroup.zpowers (y⁻¹ * y') :=
    (Subgroup.zpowers (y⁻¹ * y')).pow_mem hoz (j + 1)
  have hw2 : w * w = o := by
    change o ^ (j + 1) * o ^ (j + 1) = o
    have hexp : j + 1 + (j + 1) = orderOf o + 1 := by omega
    rw [← pow_add, hexp, pow_succ, pow_orderOf_eq_one, one_mul]
  have hyw : y * w * y = w⁻¹ := by
    simpa [hyinv] using sec4F_conj_zpowers_eq_inv hyc hwz
  have hwy : w⁻¹ * y = y * w := by
    rw [← hyw, mul_assoc, hy2, mul_one]
  have hwyw : w⁻¹ * y * w = y * o := by
    rw [hwy, mul_assoc, hw2]
  have hxw : x * w = w * x := sec4F_commute_mem_zpowers hxz hwz
  have hox : o * x = x * o := sec4F_commute_mem_zpowers hoz hxz
  have hconj_yx : w⁻¹ * (y * x) * w = y' := by
    calc w⁻¹ * (y * x) * w = w⁻¹ * y * (x * w) := by group
      _ = w⁻¹ * y * (w * x) := by rw [hxw]
      _ = (w⁻¹ * y * w) * x := by group
      _ = (y * o) * x := by rw [hwyw]
      _ = y * (o * x) := by group
      _ = y * (x * o) := by rw [hox]
      _ = y * (y⁻¹ * y') := by rw [← hc]
      _ = y' := by group
  have hyx_conj : ∃ g : G, y * x = g⁻¹ * t * g := by
    refine ⟨g' * w⁻¹, ?_⟩
    calc y * x = w * (w⁻¹ * (y * x) * w) * w⁻¹ := by group
      _ = w * y' * w⁻¹ := by rw [hconj_yx]
      _ = w * (g'⁻¹ * t * g') * w⁻¹ := by rw [hy'_eq]
      _ = (g' * w⁻¹)⁻¹ * t * (g' * w⁻¹) := by group
  have hcore : x = 1 ∨ x = sec4MPt t φ a * sec4MPt t φ b :=
    h.fiber_core hy hyN hab hσ hxA hxcomm hyx_conj
  have hmem : o ∈ centralizer (A : Set G) := Subgroup.zpowers_le.mpr hcC hoz
  rcases hcore with hx1 | hxab
  · exact ⟨o, hmem, hodd, Or.inl (by rw [hc, hx1, one_mul])⟩
  · exact ⟨o, hmem, hodd, Or.inr (by rw [hc, hxab])⟩

theorem Sec4FSetup.fiber_two (h : Sec4FSetup t L S z A B φ) {y y' : G}
    (hy : ∃ g : G, y = g⁻¹ * t * g) (hy' : ∃ g : G, y' = g⁻¹ * t * g)
    (hyN : y ∈ normalizer (A : Set G)) (hy'N : y' ∈ normalizer (A : Set G))
    {a b : Option (Fin 7)} (hab : a ≠ b) (hσ : Sec4MRealizes t φ y (Equiv.swap a b))
    (hσ' : Sec4MRealizes t φ y' (Equiv.swap a b))
    (hn : ∃ n : ℕ, (y⁻¹ * y') ^ (2 ^ n) = 1) :
    y' = y ∨ y' = y * (sec4MPt t φ a * sec4MPt t φ b) := by
  have hy_copy : ∃ g : G, y = g⁻¹ * t * g := hy
  obtain ⟨g, hy_eq⟩ := hy_copy
  have hy'_copy : ∃ g : G, y' = g⁻¹ * t * g := hy'
  obtain ⟨g', hy'_eq⟩ := hy'_copy
  have hy2 : y * y = 1 := sec4F_sq_eq_one_of_eq_conj h hy_eq
  have hy'2 : y' * y' = 1 := sec4F_sq_eq_one_of_eq_conj h hy'_eq
  have hcC : y⁻¹ * y' ∈ centralizer (A : Set G) :=
    sec4F_inv_mul_mem_centralizer h hσ hσ'
  have hcA : y⁻¹ * y' ∈ A := h.cent_two_elt hcC hn
  have hcsq : (y⁻¹ * y') * (y⁻¹ * y') = 1 := h.A_sq hcA
  have hcinv : (y⁻¹ * y')⁻¹ = y⁻¹ * y' := inv_eq_of_mul_eq_one_right hcsq
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hyc : y * (y⁻¹ * y') * y⁻¹ = (y⁻¹ * y')⁻¹ :=
    sec4F_conj_eq_inv_of_mul_eq_one hy2 hy'2 rfl
  have hconv : y * (y⁻¹ * y') * y = y⁻¹ * y' := by
    have h' := hyc
    rw [hcinv] at h'
    simpa [hyinv] using h'
  have hcomm : (y⁻¹ * y') * y = y * (y⁻¹ * y') := by
    have h1 : y * (y⁻¹ * y') * y = y⁻¹ * y' := hconv
    calc (y⁻¹ * y') * y = y * (y⁻¹ * y') * y * y := by rw [h1]
      _ = y * (y⁻¹ * y') := by rw [mul_assoc, hy2, mul_one]
  have hconj : ∃ g : G, y * (y⁻¹ * y') = g⁻¹ * t * g :=
    ⟨g', by rw [hy'_eq]; group⟩
  have hcore : y⁻¹ * y' = 1 ∨
      y⁻¹ * y' = sec4MPt t φ a * sec4MPt t φ b :=
    h.fiber_core hy hyN hab hσ hcA hcomm hconj
  have hy'c : y' = y * (y⁻¹ * y') := by group
  rcases hcore with h1 | h1
  · left
    rw [hy'c, h1, mul_one]
  · right
    rw [hy'c, h1]

end CFSG.OddStandard.SmallF3.Omega
