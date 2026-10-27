module

public import CFSG.Holt.H78.Basic

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

section Involutions

private theorem conj_mul_eq_inv {a b : G} (ha : a * a = 1) (hb : b * b = 1) :
    a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb, ← mul_assoc,
    ha, one_mul]

theorem conj_pow_mul_eq_inv {a b : G} (ha : a * a = 1) (hb : b * b = 1) (n : ℕ) :
    a * (a * b) ^ n * a⁻¹ = ((a * b) ^ n)⁻¹ := by
  rw [← conj_pow, conj_mul_eq_inv ha hb, inv_pow]

theorem odd_period_mul_of_smul_eq_iff {a b : G} {α : Ω} (ha : a * a = 1) (hb : b * b = 1)
    (haα : ∀ ω, a • ω = ω ↔ ω = α) (hpos : 0 < period (a * b) α) :
    Odd (period (a * b) α) := by
  rw [← Nat.not_even_iff_odd]
  rintro ⟨m, hm⟩
  have hd2 : (a * b) ^ m • (a * b) ^ m • α = α := by
    rw [← mul_smul, ← pow_add, ← hm, pow_period_smul]
  have hfix : a • (a * b) ^ m • α = (a * b) ^ m • α := by
    calc a • (a * b) ^ m • α = (a * (a * b) ^ m * a⁻¹) • a • α := by
          simp only [mul_smul, inv_smul_smul]
      _ = ((a * b) ^ m)⁻¹ • α := by rw [conj_pow_mul_eq_inv ha hb, (haα α).mpr rfl]
      _ = (a * b) ^ m • α := by rw [inv_smul_eq_iff, hd2]
  exact pow_smul_ne_of_lt_period (by omega) (by omega) ((haα _).mp hfix)

theorem pow_period_div_two_smul_eq {a b : G} {α β : Ω} (ha : a * a = 1) (hb : b * b = 1)
    (haα : ∀ ω, a • ω = ω ↔ ω = α) (hbβ : ∀ ω, b • ω = ω ↔ ω = β)
    (hpos : 0 < period (a * b) α) : (a * b) ^ (period (a * b) α / 2) • α = β := by
  have hL := Nat.two_mul_div_two_add_one_of_odd (odd_period_mul_of_smul_eq_iff ha hb haα hpos)
  set j := period (a * b) α / 2
  have key : a • (a * b) ^ j • α = (a * b) ^ (j + 1) • α := by
    calc a • (a * b) ^ j • α = (a * (a * b) ^ j * a⁻¹) • a • α := by
          simp only [mul_smul, inv_smul_smul]
      _ = ((a * b) ^ j)⁻¹ • α := by rw [conj_pow_mul_eq_inv ha hb, (haα α).mpr rfl]
      _ = (a * b) ^ (j + 1) • α := by
          rw [inv_smul_eq_iff, ← mul_smul, ← pow_add,
            show j + (j + 1) = period (a * b) α by omega, pow_period_smul]
  refine (hbβ _).mp ?_
  calc b • (a * b) ^ j • α = a⁻¹ • (a * b) ^ (j + 1) • α := by
        rw [pow_succ', mul_smul, mul_smul, inv_smul_smul]
    _ = (a * b) ^ j • α := by rw [← key, inv_smul_smul]

theorem exists_mem_closure_conj_smul_eq {a b : G} {α β : Ω} (ha : a * a = 1) (hb : b * b = 1)
    (haα : ∀ ω, a • ω = ω ↔ ω = α) (hbβ : ∀ ω, b • ω = ω ↔ ω = β)
    (hpos : 0 < period (a * b) α) :
    ∃ x ∈ Subgroup.closure ({a, b} : Set G), (x * a * x⁻¹) • α = β := by
  have hL := Nat.two_mul_div_two_add_one_of_odd (odd_period_mul_of_smul_eq_iff ha hb haα hpos)
  have hj := pow_period_div_two_smul_eq ha hb haα hbβ hpos
  set j := period (a * b) α / 2
  set x := (a * b) ^ (j * (j + 1)) with hx
  have hxa : a * x⁻¹ * a⁻¹ = x := by rw [← conj_inv, hx, conj_pow_mul_eq_inv ha hb, inv_inv]
  have e : j * (j + 1) + j * (j + 1) = j + period (a * b) α * j := by
    rw [← hL]
    ring
  have hmem : a * b ∈ Subgroup.closure ({a, b} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert a {b}))
      (Subgroup.subset_closure (Set.mem_insert_of_mem a rfl))
  refine ⟨x, Subgroup.pow_mem _ hmem _, ?_⟩
  calc (x * a * x⁻¹) • α = (x * (a * x⁻¹ * a⁻¹)) • a • α := by
        simp only [mul_smul, inv_smul_smul]
    _ = β := by
        rw [hxa, (haα α).mpr rfl, hx, ← pow_add, e, pow_add, mul_smul,
          (pow_smul_eq_iff_period_dvd (n := period (a * b) α * j)).mpr (dvd_mul_right _ _), hj]

end Involutions

section LongInv

variable [Finite G]

theorem pow_period_div_two_mul_smul_eq {t u : G} {α β : Ω} (ht : t ∈ longInvAt G Ω α)
    (hu : u ∈ longInvAt G Ω β) : (t * u) ^ (period (t * u) α / 2) • α = β :=
  pow_period_div_two_smul_eq (mul_self_eq_one_of_mem_longInv ht.1)
    (mul_self_eq_one_of_mem_longInv hu.1) (smul_eq_iff_of_mem_longInvAt ht)
    (smul_eq_iff_of_mem_longInvAt hu) (period_pos_of_orderOf_pos (orderOf_pos _) _)

theorem exists_conj_mem_longInvSwap {t u : G} {α β : Ω} (ht : t ∈ longInvAt G Ω α)
    (hu : u ∈ longInvAt G Ω β) :
    ∃ x ∈ Subgroup.closure ({t, u} : Set G), x * t * x⁻¹ ∈ longInvSwap G Ω α β := by
  obtain ⟨x, hx, hxα⟩ := exists_mem_closure_conj_smul_eq (mul_self_eq_one_of_mem_longInv ht.1)
    (mul_self_eq_one_of_mem_longInv hu.1) (smul_eq_iff_of_mem_longInvAt ht)
    (smul_eq_iff_of_mem_longInvAt hu) (period_pos_of_orderOf_pos (orderOf_pos _) _)
  exact ⟨x, hx, conj_mem_longInv ht.1 x, hxα⟩

theorem longInvSwap_nonempty (hG : IsStarGroup G Ω) (α β : Ω) :
    (longInvSwap G Ω α β).Nonempty := by
  obtain ⟨t, ht⟩ := hG.longInvAt_nonempty α
  obtain ⟨u, hu⟩ := hG.longInvAt_nonempty β
  obtain ⟨x, -, hx⟩ := exists_conj_mem_longInvSwap ht hu
  exact ⟨_, hx⟩

theorem IsStarGroup.isPretransitive (hG : IsStarGroup G Ω) : IsPretransitive G Ω :=
  ⟨fun α β => let ⟨t, ht⟩ := longInvSwap_nonempty hG α β
    ⟨t, ht.2⟩⟩

theorem IsStarGroup.swap_mem_orbit (hG : IsStarGroup G Ω) (p : Ω × Ω) : p.swap ∈ orbit G p :=
  let ⟨t, ht⟩ := longInvSwap_nonempty hG p.1 p.2
  ⟨t, Prod.ext ht.2 (smul_eq_of_mem_longInvSwap ht)⟩

end LongInv

end CFSG.Holt.H78
