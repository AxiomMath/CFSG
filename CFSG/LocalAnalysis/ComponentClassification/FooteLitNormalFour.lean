module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.ComponentClassification.FooteLit

open Subgroup
open scoped Pointwise

theorem isCyclic_of_unique_involution {A : Type*} [CommGroup A] [Finite A] (hA : IsPGroup 2 A)
    (huniq : ∀ x y : A, x ^ 2 = 1 → y ^ 2 = 1 → x = 1 ∨ y = 1 ∨ x = y) : IsCyclic A := by
  classical
  have hexp : Monoid.ExponentExists A := Monoid.ExponentExists.of_finite
  obtain ⟨a, ha⟩ := Monoid.exists_orderOf_eq_exponent hexp
  by_contra hcyc
  have hne : ∃ b : A, b ∉ zpowers a := by
    by_contra h
    push Not at h
    exact hcyc ⟨a, fun x => h x⟩
  have hex : ∃ n, ∃ b : A, b ∉ zpowers a ∧ orderOf b = n := by
    obtain ⟨b, hb⟩ := hne
    exact ⟨_, b, hb, rfl⟩
  obtain ⟨b, hb, hbn⟩ := Nat.find_spec hex
  have hmin : ∀ c : A, c ∉ zpowers a → Nat.find hex ≤ orderOf c := fun c hc =>
    Nat.find_min' hex ⟨c, hc, rfl⟩
  have hb1 : b ≠ 1 := fun h => hb (h ▸ one_mem _)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hA) b
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hb1 (orderOf_eq_one_iff.mp (by rw [hj, pow_zero]))
  have h2b : 2 ∣ orderOf b := by rw [hj]; exact dvd_pow_self 2 hj0
  have hb2 : b ^ 2 ∈ zpowers a := by
    by_contra h
    have h1 := hmin (b ^ 2) h
    rw [orderOf_pow_of_dvd two_ne_zero h2b, ← hbn] at h1
    have hpos : 0 < orderOf b := orderOf_pos b
    omega
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hb2
  set N := orderOf a with hN
  have hbN : orderOf b ∣ N := ha ▸ Monoid.order_dvd_exponent b
  have h2N : 2 ∣ N := h2b.trans hbN
  obtain ⟨M, hM⟩ := h2N
  have hMpos : 0 < M := by
    have := orderOf_pos a
    omega
  have hi2 : 2 ∣ i := by
    have h1 : a ^ (i * M) = 1 := by
      rw [zpow_mul, hi, zpow_natCast, ← pow_mul, ← hM]
      exact orderOf_dvd_iff_pow_eq_one.mp hbN
    have h2 : (N : ℤ) ∣ i * M := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hM] at h2
    push_cast at h2
    obtain ⟨k, hk⟩ := h2
    have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast hMpos.ne'
    exact ⟨k, mul_right_cancel₀ hM0 (by rw [hk]; ring)⟩
  obtain ⟨k, hk⟩ := hi2
  set c := b * a ^ (-k) with hc
  have hc2 : c ^ 2 = 1 := by
    rw [hc, mul_pow, ← zpow_natCast (a ^ (-k)), ← zpow_mul, ← hi, hk, ← zpow_add,
      show 2 * k + -k * ((2 : ℕ) : ℤ) = 0 by push_cast; ring, zpow_zero]
  have hcA : c ∉ zpowers a := fun h => hb (by
    have e1 : b = c * a ^ k := by rw [hc, mul_assoc, ← zpow_add]; simp
    rw [e1]
    exact mul_mem h (zpow_mem_zpowers a k))
  have hc1 : c ≠ 1 := fun h => hcA (h ▸ one_mem _)
  set z := a ^ M with hz
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← pow_mul, mul_comm, ← hM, hN, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rw [hz]
    exact pow_ne_one_of_lt_orderOf hMpos.ne' (by omega)
  rcases huniq c z hc2 hz2 with h | h | h
  · exact hc1 h
  · exact hz1 h
  · exact hcA (h ▸ npow_mem_zpowers a M)

variable {P : Type*} [Group P] [Finite P]

theorem card_comap_zpowers_eq_four {z y : P} [(zpowers z).Normal] (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) (hy : QuotientGroup.mk' (zpowers z) y ≠ 1) (hy2 : y ^ 2 = 1) :
    Nat.card ((zpowers (QuotientGroup.mk' (zpowers z) y)).comap (QuotientGroup.mk' (zpowers z))) =
      4 := by
  set π := QuotientGroup.mk' (zpowers z) with hπ
  set U := (zpowers (π y)).comap π with hU
  have hZ : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz2 hz1
  have hY : Nat.card (zpowers (π y)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [← map_pow, hy2, map_one]) hy
  have h1 := U.card_mul_index
  have h2 := (zpowers (π y)).card_mul_index
  rw [hU, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers z)
  rw [hZ] at h3
  rw [hY] at h2
  have hidx : 0 < (zpowers (π y)).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 : Nat.card U * (zpowers (π y)).index = 4 * (zpowers (π y)).index := by
    rw [hU, h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hidx h4

theorem exists_normal_four_of_normal_elementary (hP : IsPGroup 2 P) {B : Subgroup P} [B.Normal]
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hB4 : 4 ≤ Nat.card B) :
    ∃ U : Subgroup P, U.Normal ∧ U ≤ B ∧ Nat.card U = 4 := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hB1 : B ≠ ⊥ := fun h => by rw [h, card_bot] at hB4; omega
  obtain ⟨⟨z, hzm⟩, hz1⟩ :=
    ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hB1)
  obtain ⟨hzB, hzC⟩ := mem_inf.mp hzm
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hZ : (zpowers z).Normal := normal_of_le_center (zpowers_le.mpr hzC)
  set π := QuotientGroup.mk' (zpowers z) with hπ
  have hPq : IsPGroup 2 (P ⧸ zpowers z) := hP.to_quotient _
  have : Group.IsNilpotent (P ⧸ zpowers z) := hPq.isNilpotent
  have hBq : (B.map π).Normal := (inferInstance : B.Normal).map _ (QuotientGroup.mk'_surjective _)
  have hBq1 : B.map π ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    have h1 := Subgroup.card_le_of_le h
    rw [Nat.card_zpowers, orderOf_eq_prime (hB2 z hzB) hz1'] at h1
    omega
  obtain ⟨⟨yb, hybm⟩, hyb1⟩ :=
    ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hBq1)
  obtain ⟨hybB, hybC⟩ := mem_inf.mp hybm
  obtain ⟨y, hyB, rfl⟩ := mem_map.mp hybB
  have hy1 : π y ≠ 1 := fun h => hyb1 (Subtype.ext h)
  set U := (zpowers (π y)).comap π with hU
  refine ⟨U, ?_, ?_, card_comap_zpowers_eq_four (hB2 z hzB) hz1' hy1 (hB2 y hyB)⟩
  · exact (normal_of_le_center (zpowers_le.mpr hybC)).comap π
  · intro u hu
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (show π u ∈ zpowers (π y) from hu)
    rw [← map_zpow, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hk
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hk
    have e1 : u = y ^ k * z ^ m := by rw [hm]; group
    rw [e1]
    exact mul_mem (zpow_mem hyB k) (zpow_mem hzB m)

theorem centralizer_le_of_maximal (hP : IsPGroup 2 P) {A : Subgroup P} [A.Normal]
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hmax : ∀ A' : Subgroup P, A'.Normal → (∀ x ∈ A', ∀ y ∈ A', x * y = y * x) →
      Nat.card A' ≤ Nat.card A) :
    centralizer (A : Set P) ≤ A := by
  by_contra hC
  have hCn : (centralizer (A : Set P)).Normal := inferInstance
  set π := QuotientGroup.mk' A with hπ
  have hPq : IsPGroup 2 (P ⧸ A) := hP.to_quotient _
  have : Group.IsNilpotent (P ⧸ A) := hPq.isNilpotent
  have hCq : ((centralizer (A : Set P)).map π).Normal :=
    hCn.map _ (QuotientGroup.mk'_surjective _)
  have hCq1 : (centralizer (A : Set P)).map π ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact hC h
  obtain ⟨⟨cb, hcbm⟩, hcb1⟩ :=
    ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hCq1)
  obtain ⟨hcbC, hcbZ⟩ := mem_inf.mp hcbm
  obtain ⟨c, hcC, rfl⟩ := mem_map.mp hcbC
  have hcA : c ∉ A := fun h => hcb1 (Subtype.ext (by
    show π c = 1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h))
  set A' := A ⊔ zpowers c with hA'
  have hA'set : (A' : Set P) = (A : Set P) * (zpowers c : Set P) := normal_mul A (zpowers c)
  have hcomm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    rw [← SetLike.mem_coe, hA'set] at hx hy
    obtain ⟨a₁, ha₁, c₁, hc₁, rfl⟩ := hx
    obtain ⟨a₂, ha₂, c₂, hc₂, rfl⟩ := hy
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hc₁
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hc₂
    have h1 : ∀ a ∈ A, ∀ k : ℤ, a * c ^ k = c ^ k * a := fun a ha k =>
      ((Commute.zpow_right (show Commute a c from
        ((mem_centralizer_iff.mp hcC) a ha)) k)).eq
    calc a₁ * c ^ m * (a₂ * c ^ n) = a₁ * a₂ * (c ^ m * c ^ n) := by
          rw [mul_assoc, ← mul_assoc (c ^ m), ← h1 a₂ ha₂ m]; group
      _ = a₂ * a₁ * (c ^ n * c ^ m) := by
          rw [hAc a₁ ha₁ a₂ ha₂, ← zpow_add, ← zpow_add, add_comm]
      _ = a₂ * c ^ n * (a₁ * c ^ m) := by
          rw [mul_assoc a₂ (c ^ n), ← mul_assoc (c ^ n), ← h1 a₁ ha₁ n]; group
  have hnorm : A'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hle : A' ≤ A'.comap (MulAut.conj g).toMonoidHom := by
      rw [hA', sup_le_iff]
      refine ⟨fun a ha => ?_, ?_⟩
      · show g * a * g⁻¹ ∈ A'
        exact mem_sup_left ((inferInstance : A.Normal).conj_mem a ha g)
      · rw [zpowers_le]
        show g * c * g⁻¹ ∈ A'
        have h1 : π (g * c * g⁻¹) = π c := by
          rw [map_mul, map_mul, map_inv, (mem_center_iff.mp hcbZ) (π g), mul_assoc,
            mul_inv_cancel, mul_one]
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
        have h2 := inv_mem h1
        rw [mul_inv_rev, inv_inv] at h2
        have e1 : g * c * g⁻¹ = c * (c⁻¹ * (g * c * g⁻¹)) := by group
        rw [e1]
        exact mul_mem (mem_sup_right (mem_zpowers c)) (mem_sup_left h2)
    exact hle hx
  have hlt : A < A' := lt_of_le_of_ne le_sup_left fun h =>
    hcA (h ▸ mem_sup_right (mem_zpowers c))
  have h1 := hmax A' hnorm hcomm
  exact absurd (Subgroup.card_lt_of_lt hlt) (not_lt.mpr h1)

omit [Finite P] in
theorem conj_eq_zpow_of_mem_zpowers {a g : P} (hga : g * a * g⁻¹ ∈ zpowers a) :
    ∃ k : ℤ, ∀ x ∈ zpowers a, g * x * g⁻¹ = x ^ k := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hga
  refine ⟨k, fun x hx => ?_⟩
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
  have h1 : g * a ^ m * g⁻¹ = (g * a * g⁻¹) ^ m := by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
  rw [h1, ← hk, ← zpow_mul, ← zpow_mul, mul_comm]

theorem card_le_two_mul_card_inf_centralizer {H : Subgroup P} {x : P}
    (h : ∀ g ∈ H, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹) :
    Nat.card H ≤ 2 * Nat.card ↥(H ⊓ centralizer ({x} : Set P)) := by
  classical
  have hmemC : ∀ g : P, g ∈ centralizer ({x} : Set P) ↔ g * x * g⁻¹ = x := fun g => by
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hg; rw [hg]; group
    · intro hg
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [hg]
  by_cases hall : ∀ g ∈ H, g * x * g⁻¹ = x
  · have hle : H ≤ H ⊓ centralizer ({x} : Set P) := fun g hg =>
      mem_inf.mpr ⟨hg, (hmemC g).mpr (hall g hg)⟩
    have := Subgroup.card_le_of_le hle
    omega
  push Not at hall
  obtain ⟨g₀, hg₀, hg₀x⟩ := hall
  have hg₀inv : g₀ * x * g₀⁻¹ = x⁻¹ := (h g₀ hg₀).resolve_left hg₀x
  set C := H ⊓ centralizer ({x} : Set P) with hC
  have hsub : (H : Set P) ⊆ (C : Set P) ∪ (fun y => g₀ * y) '' (C : Set P) := by
    intro g hg
    rcases h g hg with hgx | hgx
    · exact Or.inl (mem_inf.mpr ⟨hg, (hmemC g).mpr hgx⟩)
    · right
      refine ⟨g₀⁻¹ * g, mem_inf.mpr ⟨mul_mem (inv_mem hg₀) hg, ?_⟩, by simp⟩
      rw [hmemC]
      calc g₀⁻¹ * g * x * (g₀⁻¹ * g)⁻¹ = g₀⁻¹ * (g * x * g⁻¹) * g₀ := by group
        _ = g₀⁻¹ * x⁻¹ * g₀ := by rw [hgx]
        _ = x := by
          have e1 : x⁻¹ = g₀ * x * g₀⁻¹ := hg₀inv.symm
          rw [e1]; group
  have hfin : ((C : Set P) ∪ (fun y => g₀ * y) '' (C : Set P)).Finite :=
    (Set.toFinite (C : Set P)).union ((Set.toFinite (C : Set P)).image _)
  calc Nat.card H = (H : Set P).ncard := (Nat.card_coe_set_eq _)
    _ ≤ ((C : Set P) ∪ (fun y => g₀ * y) '' (C : Set P)).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ (C : Set P).ncard + ((fun y => g₀ * y) '' (C : Set P)).ncard := Set.ncard_union_le _ _
    _ = 2 * Nat.card C := by
      rw [Set.ncard_image_of_injective _ (mul_right_injective g₀), ← Nat.card_coe_set_eq,
        two_mul]
      rfl

omit [Finite P] in
theorem zpow_eq_or_eq_inv_of_orderOf_dvd_four {x : P} (hx : orderOf x ∣ 4) {k : ℤ}
    (hk : Odd k) : x ^ k = x ∨ x ^ k = x⁻¹ := by
  obtain ⟨m, rfl⟩ := hk
  rcases Int.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    have h1 : x ^ (4 * j) = 1 := by
      rw [zpow_mul]
      have : x ^ (4 : ℤ) = 1 := by
        rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
        exact orderOf_dvd_iff_pow_eq_one.mp hx
      rw [this, one_zpow]
    rw [show 2 * (j + j) + 1 = 4 * j + 1 by ring, zpow_add, h1, one_mul, zpow_one]
  · right
    have h1 : x ^ (4 * (j + 1)) = 1 := by
      rw [zpow_mul]
      have : x ^ (4 : ℤ) = 1 := by
        rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
        exact orderOf_dvd_iff_pow_eq_one.mp hx
      rw [this, one_zpow]
    rw [show 2 * (2 * j + 1) + 1 = 4 * (j + 1) + -1 by ring, zpow_add, h1, one_mul, zpow_neg_one]

omit [Finite P] in
theorem odd_of_orderOf_zpow_eq {x : P} {n : ℕ} (hn : orderOf x = 2 ^ n) (hn1 : 1 ≤ n) {k : ℤ}
    (hk : orderOf (x ^ k) = orderOf x) : Odd k := by
  by_contra hodd
  rw [Int.not_odd_iff_even] at hodd
  obtain ⟨j, rfl⟩ := hodd
  have h1 : (x ^ (j + j)) ^ (2 ^ (n - 1)) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, show (j + j) * ((2 ^ (n - 1) : ℕ) : ℤ) =
      j * ((2 ^ n : ℕ) : ℤ) by
        rw [show (2 ^ n : ℕ) = 2 * 2 ^ (n - 1) by
          rw [← pow_succ']; congr 1; omega]
        push_cast; ring, mul_comm, zpow_mul, zpow_natCast, ← hn, pow_orderOf_eq_one, one_zpow]
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hk, hn] at h2
  have h3 : 2 ^ n ≤ 2 ^ (n - 1) := Nat.le_of_dvd (by positivity) h2
  have h4 : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem exists_normal_four_of_zpowers (hP : IsPGroup 2 P) {a : P} (hAn : (zpowers a).Normal)
    (hCA : centralizer ((zpowers a : Subgroup P) : Set P) ≤ zpowers a) {E : Subgroup P}
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) (hE8 : Nat.card E = 8) :
    ∃ U : Subgroup P, U.Normal ∧ Nat.card U = 4 ∧ ∀ u ∈ U, u ^ 2 = 1 := by
  set A := zpowers a with hA
  have hpow : ∀ g : P, ∃ k : ℤ, ∀ x ∈ A, g * x * g⁻¹ = x ^ k := fun g =>
    conj_eq_zpow_of_mem_zpowers (hAn.conj_mem a (mem_zpowers a) g)
  have hCa : centralizer ({a} : Set P) ≤ A := by
    have h1 : centralizer ((A : Subgroup P) : Set P) = centralizer ({a} : Set P) := by
      rw [hA, zpowers_eq_closure, centralizer_closure]
    rw [← h1]
    exact hCA
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP) a
  have hodd : 1 ≤ n → ∀ g : P, ∀ k : ℤ, (∀ x ∈ A, g * x * g⁻¹ = x ^ k) → Odd k := by
    intro hn1 g k hk
    refine odd_of_orderOf_zpow_eq hn hn1 ?_
    rw [← hk a (mem_zpowers a), ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hcommA : ∀ g h : P, g * h * g⁻¹ * h⁻¹ ∈ A := by
    intro g h
    obtain ⟨k, hk⟩ := hpow g
    obtain ⟨l, hl⟩ := hpow h
    have e1 : (g * h) * a * (g * h)⁻¹ = a ^ (l * k) := by
      calc (g * h) * a * (g * h)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ := by group
        _ = g * a ^ l * g⁻¹ := by rw [hl a (mem_zpowers a)]
        _ = (a ^ l) ^ k := hk _ (zpow_mem_zpowers a l)
        _ = a ^ (l * k) := by rw [← zpow_mul]
    have e2 : (h * g) * a * (h * g)⁻¹ = a ^ (k * l) := by
      calc (h * g) * a * (h * g)⁻¹ = h * (g * a * g⁻¹) * h⁻¹ := by group
        _ = h * a ^ k * h⁻¹ := by rw [hk a (mem_zpowers a)]
        _ = (a ^ k) ^ l := hl _ (zpow_mem_zpowers a k)
        _ = a ^ (k * l) := by rw [← zpow_mul]
    have e3 : (g * h) * a * (g * h)⁻¹ = (h * g) * a * (h * g)⁻¹ := by rw [e1, e2, mul_comm]
    have h1 : (h * g)⁻¹ * (g * h) ∈ centralizer ({a} : Set P) := by
      rw [mem_centralizer_singleton_iff]
      calc (h * g)⁻¹ * (g * h) * a = (h * g)⁻¹ * ((g * h) * a * (g * h)⁻¹) * (g * h) := by group
        _ = (h * g)⁻¹ * ((h * g) * a * (h * g)⁻¹) * (g * h) := by rw [e3]
        _ = a * ((h * g)⁻¹ * (g * h)) := by group
    have e4 : g * h * g⁻¹ * h⁻¹ = (h * g) * ((h * g)⁻¹ * (g * h)) * (h * g)⁻¹ := by group
    rw [e4]
    exact hAn.conj_mem _ (hCa h1) _
  have hEA_card : ∀ z : P, (∀ x ∈ A, x ^ 2 = 1 → x = 1 ∨ x = z) →
      Nat.card ↥(E ⊓ A) ≤ 2 := by
    intro z hz
    have hsub : ((E ⊓ A : Subgroup P) : Set P) ⊆ {1, z} := fun x hx =>
      hz x (mem_inf.mp hx).2 (hE2 x (mem_inf.mp hx).1)
    calc Nat.card ↥(E ⊓ A) = ((E ⊓ A : Subgroup P) : Set P).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, z} : Set P).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({z} : Set P).ncard + 1 := Set.ncard_insert_le 1 {z}
      _ = 2 := by rw [Set.ncard_singleton]
  set z := a ^ (2 ^ (n - 1)) with hz
  have hz_uniq : ∀ x ∈ A, x ^ 2 = 1 → x = 1 ∨ x = z := by
    intro x hx hx2
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · left
      have ha1 : a = 1 := orderOf_eq_one_iff.mp (by rw [hn, h0, pow_zero])
      rw [ha1, one_zpow]
    · have h1 : a ^ (2 * m) = 1 := by
        rw [mul_comm, zpow_mul, zpow_two, ← sq]
        exact hx2
      have h2 : ((2 ^ n : ℕ) : ℤ) ∣ 2 * m := by
        rw [← hn]; exact orderOf_dvd_iff_zpow_eq_one.mpr h1
      have h3 : ((2 ^ (n - 1) : ℕ) : ℤ) ∣ m := by
        have e1 : ((2 ^ n : ℕ) : ℤ) = 2 * ((2 ^ (n - 1) : ℕ) : ℤ) := by
          rw [show n = (n - 1) + 1 by omega, pow_succ]; push_cast; ring_nf
        rw [e1] at h2
        exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h2
      obtain ⟨t, rfl⟩ := h3
      have hzz : z ^ 2 = 1 := by
        rw [hz, ← pow_mul, ← pow_succ, show n - 1 + 1 = n by omega, ← hn, pow_orderOf_eq_one]
      rw [zpow_mul, zpow_natCast, ← hz]
      rcases Int.even_or_odd t with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · left
        rw [← two_mul, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hzz,
          one_zpow]
      · right
        rw [zpow_add, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hzz,
          one_zpow, one_mul, zpow_one]
  have hEA2 := hEA_card z hz_uniq
  have hn3 : 3 ≤ n := by
    by_contra hlt
    push Not at hlt
    have hdich : ∀ g ∈ E, g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹ := by
      intro g _
      obtain ⟨k, hk⟩ := hpow g
      rw [hk a (mem_zpowers a)]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · left
        have ha1 : a = 1 := orderOf_eq_one_iff.mp (by rw [hn, h0, pow_zero])
        rw [ha1, one_zpow]
      · refine zpow_eq_or_eq_inv_of_orderOf_dvd_four ?_ (hodd hpos g k hk)
        rw [hn, show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.pow_dvd_pow 2 (by omega)
    have h1 := card_le_two_mul_card_inf_centralizer hdich
    have h2 := Subgroup.card_le_of_le (inf_le_inf_left E hCa)
    omega
  set u := a ^ (2 ^ (n - 2)) with hu
  have huA : u ∈ A := npow_mem_zpowers a _
  have hu4 : orderOf u = 4 := by
    rw [hu, orderOf_pow_of_dvd (by positivity) (by rw [hn]; exact Nat.pow_dvd_pow 2 (by omega)),
      hn, Nat.pow_div (by omega) (by norm_num), show n - (n - 2) = 2 by omega]
  have hdich_u : ∀ g ∈ E, g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u⁻¹ := by
    intro g _
    obtain ⟨k, hk⟩ := hpow g
    rw [hk u huA]
    exact zpow_eq_or_eq_inv_of_orderOf_dvd_four (by rw [hu4]) (hodd (by omega) g k hk)
  have hEu := card_le_two_mul_card_inf_centralizer hdich_u
  obtain ⟨f, hfEu, hfA⟩ : ∃ f ∈ E ⊓ centralizer ({u} : Set P), f ∉ A := by
    by_contra hcon
    push Not at hcon
    have hle : E ⊓ centralizer ({u} : Set P) ≤ E ⊓ A := fun x hx =>
      mem_inf.mpr ⟨(mem_inf.mp hx).1, hcon x hx⟩
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨hfE, hfu⟩ := mem_inf.mp hfEu
  have hff : f * f = 1 := by rw [← sq]; exact hE2 f hfE
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← pow_mul, ← pow_succ, show n - 1 + 1 = n by omega, ← hn, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rw [hz]
    exact pow_ne_one_of_lt_orderOf (by positivity)
      (by rw [hn]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hzA : z ∈ A := npow_mem_zpowers a _
  have hzC : z ∈ center P := by
    rw [mem_center_iff]
    intro g
    have h1 : g * z * g⁻¹ ∈ A := hAn.conj_mem z hzA g
    have h2 : (g * z * g⁻¹) ^ 2 = 1 := by
      rw [sq, show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, ← sq, hz2]
      group
    rcases hz_uniq _ h1 h2 with h3 | h3
    · exfalso
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h3]; group
    · calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h3]
  have key : ∀ g : P, g * f * g⁻¹ = f ∨ g * f * g⁻¹ = z * f := by
    intro g
    set c := g * f * g⁻¹ * f⁻¹ with hc
    have hcA : c ∈ A := hcommA g f
    have hgf : g * f * g⁻¹ = c * f := by rw [hc]; group
    have hsq : c * f * (c * f) = 1 := by
      rw [← hgf, show g * f * g⁻¹ * (g * f * g⁻¹) = g * (f * f) * g⁻¹ by group, hff]
      group
    have hfc : f * c * f⁻¹ = c⁻¹ := by
      rw [hfinv]
      calc f * c * f = c⁻¹ * (c * f * (c * f)) := by group
        _ = c⁻¹ := by rw [hsq, mul_one]
    obtain ⟨kf, hkf⟩ := hpow f
    have h1 : c ^ kf = c⁻¹ := by rw [← hkf c hcA, hfc]
    have h2 : u ^ kf = u := by
      rw [← hkf u huA]
      calc f * u * f⁻¹ = u * f * f⁻¹ := by rw [mem_centralizer_singleton_iff.mp hfu]
        _ = u := by group
    have h3 : (4 : ℤ) ∣ kf - 1 := by
      have : u ^ (kf - 1) = 1 := by rw [zpow_sub, h2, zpow_one, mul_inv_cancel]
      have h := orderOf_dvd_iff_zpow_eq_one.mpr this
      rw [hu4] at h
      exact_mod_cast h
    have h4 : c ^ (kf + 1) = 1 := by rw [zpow_add, h1, zpow_one, inv_mul_cancel]
    have hc2 : c ^ 2 = 1 := by
      by_contra hc2
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hP) c
      have hj2 : 2 ≤ j := by
        by_contra hj2
        push Not at hj2
        apply hc2
        rw [← orderOf_dvd_iff_pow_eq_one, hj]
        exact (pow_dvd_pow 2 (by omega : j ≤ 1)).trans (by norm_num)
      have h5 : ((orderOf c : ℕ) : ℤ) ∣ kf + 1 := orderOf_dvd_iff_zpow_eq_one.mpr h4
      have h6 : (4 : ℤ) ∣ kf + 1 := by
        refine dvd_trans ?_ h5
        rw [hj]
        exact_mod_cast (Nat.pow_dvd_pow 2 hj2 : 2 ^ 2 ∣ 2 ^ j)
      obtain ⟨r, hr⟩ := h3
      obtain ⟨s, hs⟩ := h6
      omega
    rcases hz_uniq c hcA hc2 with hc1 | hcz
    · left; rw [hgf, hc1, one_mul]
    · right; rw [hgf, hcz]
  have hZn : (zpowers z).Normal := normal_of_le_center (zpowers_le.mpr hzC)
  set π := QuotientGroup.mk' (zpowers z) with hπ
  have hfZ : π f ≠ 1 := by
    intro h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact hfA (zpowers_le.mpr hzA h)
  have hπz : π z = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact mem_zpowers z
  have hfC : π f ∈ center (P ⧸ zpowers z) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (zpowers z) q
    have h1 : π (g * f * g⁻¹) = π f := by
      rcases key g with h | h
      · rw [h]
      · rw [h, map_mul, hπz, one_mul]
    calc π g * π f = π (g * f * g⁻¹) * π g := by rw [map_mul, map_mul, map_inv]; group
      _ = π f * π g := by rw [h1]
  refine ⟨(zpowers (π f)).comap π, (normal_of_le_center (zpowers_le.mpr hfC)).comap π,
    card_comap_zpowers_eq_four hz2 hz1 hfZ (hE2 f hfE), ?_⟩
  intro v hv
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (show π v ∈ zpowers (π f) from hv)
  rw [← map_zpow, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hk
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hk
  have e1 : v = f ^ k * z ^ m := by rw [hm]; group
  have hzc : ∀ x : P, x * z = z * x := fun x => mem_center_iff.mp hzC x
  have hcomm : Commute (f ^ k) (z ^ m) :=
    Commute.zpow_right (show Commute (f ^ k) z from hzc (f ^ k)) m
  have hfk : (f ^ k) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hE2 f hfE, one_zpow]
  have hzm : (z ^ m) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
  rw [e1, hcomm.mul_pow, hfk, hzm, one_mul]

theorem exists_normal_four (hP : IsPGroup 2 P) {E : Subgroup P} (hE2 : ∀ e ∈ E, e ^ 2 = 1)
    (hE8 : Nat.card E = 8) :
    ∃ U : Subgroup P, U.Normal ∧ Nat.card U = 4 ∧ ∀ u ∈ U, u ^ 2 = 1 := by
  classical
  set S : Set (Subgroup P) := {A | A.Normal ∧ ∀ x ∈ A, ∀ y ∈ A, x * y = y * x} with hS
  have hSne : S.Nonempty := ⟨⊥, inferInstance, fun x hx y hy => by
    rw [mem_bot] at hx hy; rw [hx, hy]⟩
  obtain ⟨A, hAS, hmax'⟩ := Finset.exists_max_image (Set.toFinite S).toFinset
    (fun A => Nat.card A) ((Set.Finite.toFinset_nonempty _).mpr hSne)
  obtain ⟨hAn, hAc⟩ := (Set.Finite.mem_toFinset _).mp hAS
  have hmax : ∀ A' ∈ S, Nat.card A' ≤ Nat.card A := fun A' hA' =>
    hmax' A' ((Set.Finite.mem_toFinset _).mpr hA')
  have hCA : centralizer (A : Set P) ≤ A :=
    centralizer_le_of_maximal hP hAc fun A' hA'n hA'c => hmax A' ⟨hA'n, hA'c⟩
  set B : Subgroup P :=
    { carrier := {x | x ∈ A ∧ x ^ 2 = 1}
      one_mem' := ⟨one_mem A, one_pow 2⟩
      mul_mem' := by
        rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
        refine ⟨mul_mem hx hy, ?_⟩
        rw [(Commute.mul_pow (show Commute x y from hAc x hx y hy) 2), hx2, hy2, one_mul]
      inv_mem' := by
        rintro x ⟨hx, hx2⟩
        exact ⟨inv_mem hx, by rw [inv_pow, hx2, inv_one]⟩ } with hB
  have hBn : B.Normal := ⟨fun x hx g => ⟨hAn.conj_mem x hx.1 g, by
    rw [sq, show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, ← sq, hx.2]
    group⟩⟩
  by_cases hB4 : 4 ≤ Nat.card B
  · obtain ⟨U, hUn, hUB, hU4⟩ := exists_normal_four_of_normal_elementary hP
      (B := B) (fun b (hb : b ∈ A ∧ b ^ 2 = 1) => hb.2) hB4
    exact ⟨U, hUn, hU4, fun u hu => (hUB hu).2⟩
  ·
    push Not at hB4
    have huniq : ∀ x ∈ A, ∀ y ∈ A, x ^ 2 = 1 → y ^ 2 = 1 → x = 1 ∨ y = 1 ∨ x = y := by
      intro x hx y hy hx2 hy2
      by_contra hcon
      push Not at hcon
      obtain ⟨hx1, hy1, hxy⟩ := hcon
      have hsub : ({1, x, y} : Set P) ⊆ (B : Set P) := by
        intro w hw
        rcases hw with rfl | rfl | rfl
        · exact one_mem B
        · exact ⟨hx, hx2⟩
        · exact ⟨hy, hy2⟩
      have h3 : ({1, x, y} : Set P).ncard = 3 := by
        rw [Set.ncard_eq_three]
        exact ⟨1, x, y, hx1.symm, hy1.symm, hxy, rfl⟩
      have h4 : ({1, x, y} : Set P).ncard ≤ Nat.card B := by
        have h := Set.ncard_le_ncard hsub (Set.toFinite _)
        rwa [← Nat.card_coe_set_eq (B : Set P)] at h
      have hxyB : x * y ∈ B := mul_mem (show x ∈ B from ⟨hx, hx2⟩) (show y ∈ B from ⟨hy, hy2⟩)
      have hxy1 : x * y ∉ ({1, x, y} : Set P) := by
        rintro (h | h | h)
        · apply hxy
          calc x = x * (y * y) := by rw [← sq, hy2, mul_one]
            _ = (x * y) * y := by group
            _ = y := by rw [h, one_mul]
        · apply hy1
          calc y = x⁻¹ * (x * y) := by group
            _ = 1 := by rw [h, inv_mul_cancel]
        · apply hx1
          calc x = (x * y) * y⁻¹ := by group
            _ = 1 := by rw [h, mul_inv_cancel]
      have hsub' : insert (x * y) ({1, x, y} : Set P) ⊆ (B : Set P) :=
        Set.insert_subset hxyB hsub
      have h5 : (insert (x * y) ({1, x, y} : Set P)).ncard ≤ Nat.card B := by
        have h := Set.ncard_le_ncard hsub' (Set.toFinite _)
        rwa [← Nat.card_coe_set_eq (B : Set P)] at h
      rw [Set.ncard_insert_of_notMem hxy1 (Set.toFinite _), h3] at h5
      omega
    let : CommGroup A := { A.toGroup with mul_comm := fun x y => Subtype.ext (hAc x x.2 y y.2) }
    have hcyc : IsCyclic A := isCyclic_of_unique_involution (hP.to_subgroup A)
      fun x y hx2 hy2 => by
        rcases huniq x x.2 y y.2 (by simpa using congrArg Subtype.val hx2)
          (by simpa using congrArg Subtype.val hy2) with h | h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Or.inl (Subtype.ext h))
        · exact Or.inr (Or.inr (Subtype.ext h))
    obtain ⟨⟨a, haA⟩, ha⟩ := hcyc.exists_generator
    have hAa : A = zpowers a := by
      apply le_antisymm
      · intro x hx
        obtain ⟨k, hk⟩ := ha ⟨x, hx⟩
        have := congrArg Subtype.val hk
        simp only [SubgroupClass.coe_zpow] at this
        rw [← this]
        exact zpow_mem_zpowers a k
      · exact zpowers_le.mpr haA
    rw [hAa] at hAn hCA
    exact exists_normal_four_of_zpowers hP hAn hCA hE2 hE8

end CFSG.ComponentClassification.FooteLit
