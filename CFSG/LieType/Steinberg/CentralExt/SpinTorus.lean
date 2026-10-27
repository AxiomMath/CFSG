module

public import CFSG.LieType.Steinberg.CentralExt.TorusLift
public import CFSG.LieType.Steinberg.Classical.SpinFrame.Basic

public section

open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SpinTorus

open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.SpinFrame

section Central

variable {E G : Type*} [Group E] [Group G] {π : E →* G}

theorem commute_commutatorElement_of_central (hcen : π.ker ≤ Subgroup.center E) {a b c : E}
    (ha : π c * π a = π a * π c) (hb : π c * π b = π b * π c) : c * ⁅a, b⁆ = ⁅a, b⁆ * c := by
  have hza : a⁻¹ * (c * a * c⁻¹) ∈ π.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv]
    rw [ha, mul_inv_cancel_right, inv_mul_cancel]
  have hzb : b⁻¹ * (c * b * c⁻¹) ∈ π.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv]
    rw [hb, mul_inv_cancel_right, inv_mul_cancel]
  have e : c * ⁅a, b⁆ * c⁻¹ = ⁅a, b⁆ := by
    rw [conjugate_commutatorElement]
    calc ⁅c * a * c⁻¹, c * b * c⁻¹⁆ = ⁅a * (a⁻¹ * (c * a * c⁻¹)), b * (b⁻¹ * (c * b * c⁻¹))⁆ := by
          rw [mul_inv_cancel_left, mul_inv_cancel_left]
      _ = ⁅a, b⁆ := by
          rw [TorusLift.commutatorElement_mul_central_left (hcen hza),
            TorusLift.commutatorElement_mul_central_right (hcen hzb)]
  calc c * ⁅a, b⁆ = c * ⁅a, b⁆ * c⁻¹ * c := by group
    _ = ⁅a, b⁆ * c := by rw [e]

end Central

section Dot

variable {n : ℕ}

theorem single_add_single_dotProduct {k l : Fin n} (x y : ℤ) (a : Fin n → ℤ) :
    (Pi.single k x + Pi.single l y) ⬝ᵥ a = x * a k + y * a l := by
  rw [add_dotProduct, single_dotProduct, single_dotProduct]

theorem dot_self_of_isLong {e : Fin n → ℤ} (he : IsLong e) : e ⬝ᵥ e = 2 := by
  obtain ⟨k, l, hkl, u, v, rfl⟩ := he
  rw [single_add_single_dotProduct, single_add_single_apply_left hkl,
    single_add_single_apply_right hkl, boolSign_mul_self, boolSign_mul_self]
  norm_num

theorem abs_dot_le_two {e a : Fin n → ℤ} (he : IsLong e) (ha : IsLong a) : |e ⬝ᵥ a| ≤ 2 := by
  obtain ⟨k, l, hkl, u, v, rfl⟩ := he
  rw [single_add_single_dotProduct]
  have h1 := ha.apply_mem k
  have h2 := ha.apply_mem l
  rcases boolSign_eq_one_or_eq_neg_one u with hu | hu <;>
    rcases boolSign_eq_one_or_eq_neg_one v with hv | hv <;> rw [hu, hv] <;>
    rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> rw [h1, h2] <;> norm_num

theorem eq_of_isLong_of_apply_ne_zero {e : Fin n → ℤ} (he : IsLong e) {i j : Fin n} (hij : i ≠ j)
    (hi : e i ≠ 0) (hj : e j ≠ 0) : e = Pi.single i (e i) + Pi.single j (e j) := by
  obtain ⟨k, l, hkl, u, v, rfl⟩ := he
  rcases eq_or_eq_of_single_add_single_apply_ne_zero hi with rfl | rfl <;>
    rcases eq_or_eq_of_single_add_single_apply_ne_zero hj with rfl | rfl
  · exact absurd rfl hij
  · rw [single_add_single_apply_left hkl, single_add_single_apply_right hkl]
  · rw [single_add_single_apply_left hkl, single_add_single_apply_right hkl]
    exact add_comm _ _
  · exact absurd rfl hij

theorem neg_single_add_single (i j : Fin n) (a b : ℤ) :
    -(Pi.single i a + Pi.single j b : Fin n → ℤ) = Pi.single i (-a) + Pi.single j (-b) := by
  rw [neg_add, Pi.single_neg, Pi.single_neg]

theorem exists_dot_sep {e e' : Fin n → ℤ} (he : IsLong e) (he' : IsLong e') (h1 : e' ≠ e)
    (h2 : e' ≠ -e) : ∃ a, IsLong a ∧ e ⬝ᵥ a = 0 ∧ e' ⬝ᵥ a ≠ 0 := by
  by_cases h0 : e ⬝ᵥ e' = 0
  · exact ⟨e', he', h0, by rw [dot_self_of_isLong he']; norm_num⟩
  obtain ⟨i, j, hij, s, t, rfl⟩ := he
  refine ⟨Pi.single i (boolSign s) + Pi.single j (boolSign (!t)),
    isLong_single_add_single hij _ _, ?_, fun h3 => ?_⟩
  · rw [single_add_single_dotProduct, single_add_single_apply_left hij,
      single_add_single_apply_right hij, boolSign_not, mul_neg, boolSign_mul_self,
      boolSign_mul_self]
    norm_num
  rw [dotProduct_comm, single_add_single_dotProduct, boolSign_not] at h3
  rw [single_add_single_dotProduct] at h0
  have hc : boolSign t * e' j = boolSign s * e' i := by linarith
  have hc0 : boolSign s * e' i ≠ 0 := fun h => h0 (by rw [hc, h, add_zero])
  have hei0 : e' i ≠ 0 := fun h => hc0 (by rw [h, mul_zero])
  have hej0 : e' j ≠ 0 := fun h => hc0 (by rw [← hc, h, mul_zero])
  have hc1 : boolSign s * e' i = 1 ∨ boolSign s * e' i = -1 := by
    rcases boolSign_eq_one_or_eq_neg_one s with hs | hs <;>
      rcases he'.apply_mem i with hi | hi | hi
    all_goals first | exact absurd hi hei0 | (rw [hs, hi]; norm_num)
  have hei : e' i = boolSign s * (boolSign s * e' i) := by
    rw [← mul_assoc, boolSign_mul_self, one_mul]
  have hej : e' j = boolSign t * (boolSign s * e' i) := by
    rw [← hc, ← mul_assoc, boolSign_mul_self, one_mul]
  have he'' := eq_of_isLong_of_apply_ne_zero he' hij hei0 hej0
  rw [hei, hej] at he''
  rcases hc1 with h | h <;> rw [h] at he''
  · exact h1 (by rw [he'', mul_one, mul_one])
  · exact h2 (by rw [he'', neg_single_add_single, mul_neg_one, mul_neg_one])

end Dot

theorem exists_unit_sq_ne_one {F : Type*} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
    ∃ u : Fˣ, u ^ 2 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  refine ⟨g, fun h => ?_⟩
  have := Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one h)
  omega

theorem two_eq_zero_iff_even_card {K : Type*} [Field K] [Finite K] :
    (2 : K) = 0 ↔ Even (Nat.card K) := by
  have : Fintype K := Fintype.ofFinite K
  have hp := CharP.char_is_prime K (ringChar K)
  rw [Nat.even_iff, Nat.card_eq_fintype_card, ← FiniteField.even_card_iff_char_two,
    show (2 : K) = ((2 : ℕ) : K) by norm_cast, ringChar.spec]
  exact ⟨fun h => (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h, fun h => h ▸ dvd_rfl⟩

end CFSG.LieType.Steinberg.CentralExt.SpinTorus
