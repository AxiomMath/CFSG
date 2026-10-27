module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.FanoLemmas

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

set_option maxRecDepth 100000 in
theorem Fano.a5_sq_of_pow_four : ∀ a : A5, a ^ 4 = 1 → a * a = 1 := by
  decide +revert

set_option maxRecDepth 100000 in
theorem Fano.a5_exists_three_cycle : ∀ x : A5, x * x = 1 → x ≠ 1 → ∀ y : A5, y * y = 1 → y ≠ 1 →
    x ≠ y → x * y = y * x →
    ∃ r : A5, r ^ 3 = 1 ∧ r * x * r⁻¹ = y ∧ r * y * r⁻¹ = x * y := by
  decide +revert

theorem exists_three_normalizing_of_a5 {D : Type*} [Group D] (e : D ≃* A5) (U : Subgroup D)
    (hU : Nat.card U = 4) :
    ∃ r ∈ normalizer (U : Set D), orderOf r = 3 ∧ ∃ x ∈ U, r * x * r⁻¹ ≠ x := by
  have hsq : ∀ g ∈ U, g * g = 1 := by
    intro g hg
    have h4 : g ^ 4 = 1 := by
      have := orderOf_dvd_natCard (⟨g, hg⟩ : U)
      rw [hU, Subgroup.orderOf_mk] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have h2 := Fano.a5_sq_of_pow_four (e g) (by rw [← map_pow, h4, map_one])
    exact e.injective (by rw [map_mul, h2, map_one])
  obtain ⟨x, hxU, hx1, -⟩ := Fano.exists_mem_ne_of_card_four hU 1 1
  obtain ⟨y, hyU, hy1, hyx⟩ := Fano.exists_mem_ne_of_card_four hU 1 x
  have hcomm : x * y = y * x :=
    Fano.mul_comm_of_mul_self_eq_one (hsq x hxU) (hsq y hyU) (hsq _ (mul_mem hxU hyU))
  obtain ⟨r', hr3', hr1', hr2'⟩ := Fano.a5_exists_three_cycle (e x)
    (by rw [← map_mul, hsq x hxU, map_one]) (fun h => hx1 (e.injective (h.trans (map_one e).symm)))
    (e y) (by rw [← map_mul, hsq y hyU, map_one])
    (fun h => hy1 (e.injective (h.trans (map_one e).symm)))
    (fun h => hyx (e.injective h).symm) (by rw [← map_mul, ← map_mul, hcomm])
  obtain ⟨r, hr⟩ : ∃ r : D, e r = r' := ⟨e.symm r', e.apply_symm_apply r'⟩
  have hr3 : r ^ 3 = 1 := e.injective (by rw [map_pow, hr, hr3', map_one])
  have hrx : r * x * r⁻¹ = y := e.injective (by simp only [map_mul, map_inv, hr]; exact hr1')
  have hry : r * y * r⁻¹ = x * y := e.injective (by simp only [map_mul, map_inv, hr]; exact hr2')
  have hxy1 : (1 : D) ≠ x * y := fun h => hyx (mul_left_cancel ((hsq x hxU).trans h)).symm
  have hxxy : x ≠ x * y := fun h => hy1 (mul_left_cancel (h.symm.trans (mul_one x).symm))
  have hyxy : y ≠ x * y := fun h => hx1 (mul_right_cancel (h.symm.trans (one_mul y).symm))
  have hU' : ∀ g ∈ U, g = 1 ∨ g = x ∨ g = y ∨ g = x * y :=
    Fano.eq_of_four_distinct hU (one_mem U) hxU hyU (mul_mem hxU hyU)
      hx1.symm hy1.symm hxy1 (Ne.symm hyx) hxxy hyxy
  have hmap : ∀ g ∈ U, r * g * r⁻¹ ∈ U := by
    intro g hg
    rcases hU' g hg with h | h | h | h
    · rw [h]; simp
    · rw [h, hrx]; exact hyU
    · rw [h, hry]; exact mul_mem hxU hyU
    · have h1 : r * (x * y) * r⁻¹ = (r * x * r⁻¹) * (r * y * r⁻¹) := by group
      have h2 : y * (x * y) = x := by
        calc y * (x * y) = (y * x) * y := by group
          _ = (x * y) * y := by rw [hcomm]
          _ = x * (y * y) := by group
          _ = x := by rw [hsq y hyU, mul_one]
      rw [h, h1, hrx, hry, h2]; exact hxU
  have hcube : ∀ n : D, r * (r * (r * n * r⁻¹) * r⁻¹) * r⁻¹ = n := by
    intro n
    have hg' : r * r * r = 1 := by rw [← pow_three']; exact hr3
    calc r * (r * (r * n * r⁻¹) * r⁻¹) * r⁻¹ = (r * r * r) * n * (r * r * r)⁻¹ := by group
      _ = n := by rw [hg']; simp
  have hnorm : r ∈ normalizer (U : Set D) := by
    refine Subgroup.mem_set_normalizer_iff.mpr fun n => ⟨hmap n, fun hn => ?_⟩
    have := hmap _ (hmap _ hn)
    rwa [hcube] at this
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, one_mul, inv_one, mul_one] at hrx
    exact hyx hrx.symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨r, hnorm, orderOf_eq_prime hr3 hr1, x, hxU, by rw [hrx]; exact hyx⟩

end CFSG.EvenSporadicStandard.RuStd.S2
