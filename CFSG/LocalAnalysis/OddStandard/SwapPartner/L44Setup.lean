module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {K : Type*} [Field K]

theorem scalars_four_eq_bot (hK : Nat.card K = 4) : scalars 4 K = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  rw [mem_scalars] at hA
  obtain ⟨c, hc, hAeq⟩ := hA
  have hcard : Nat.card Kˣ = 3 := by
    rw [Nat.card_units K, hK]
  have hc3 : c ^ 3 = 1 := by
    simpa [hcard] using pow_card_eq_one' (x := c)
  have hc1 : c = 1 := by
    have h4 : c ^ 4 = c ^ 3 * c := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ]
    have h : c ^ 3 * c = 1 := by rw [← h4]; exact hc
    rw [hc3, one_mul] at h
    exact h
  have hA1 : (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [hAeq, hc1]
    simp
  exact Subtype.ext hA1

theorem proj_four_injective (hK : Nat.card K = 4) : Function.Injective (proj 4 K) :=
  (MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_proj, scalars_four_eq_bot hK])

theorem center_projectiveSL_four (hK : Nat.card K = 4) (z : projectiveSL 4 K)
    (hz : ∀ x : projectiveSL 4 K, x * z = z * x) : z = 1 := by
  obtain ⟨g, rfl⟩ := proj_surjective (n := 4) (K := K) z
  have hg : g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply proj_four_injective hK
    rw [map_mul, map_mul]
    exact hz (proj 4 K h)
  have hg1 : g = 1 := by
    have hg' : g ∈ scalars 4 K := by
      rw [scalars_eq_center]
      exact hg
    simpa [scalars_four_eq_bot hK] using hg'
  rw [hg1, map_one]

theorem exists_lift_of_orderOf_seven (hK : Nat.card K = 4) {y : projectiveSL 4 K}
    (hy : orderOf y = 7) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 4) K, proj 4 K g = y ∧
      (g : Matrix (Fin 4) (Fin 4) K) ^ 7 = 1 ∧ (g : Matrix (Fin 4) (Fin 4) K) ≠ 1 := by
  obtain ⟨g, rfl⟩ := proj_surjective (n := 4) (K := K) y
  have hg7 : g ^ 7 = 1 := by
    apply proj_four_injective hK
    rw [map_pow, map_one, ← hy]
    exact pow_orderOf_eq_one (proj 4 K g)
  refine ⟨g, rfl, ?_, ?_⟩
  · rw [← Matrix.SpecialLinearGroup.coe_pow g 7, hg7, Matrix.SpecialLinearGroup.coe_one]
  · intro hmat
    have hg1 : g = 1 := by
      apply Subtype.ext
      rw [hmat, Matrix.SpecialLinearGroup.coe_one]
    have h1 : orderOf (proj 4 K g) = 1 := by rw [hg1, map_one, orderOf_one]
    omega

section Outer

variable {K : Type} [Field K]

theorem card_outer_projectiveSL_four_dvd (hK : Nat.card K = 4) :
    Nat.card (Outer (projectiveSL 4 K)) ∣ 4 := by
  have h := UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
    (k := K) (p := 2) (f := 2) (n := 4) (by norm_num) (by norm_num) (by norm_num)
    (by rw [hK]; norm_num)
  have h4 : 2 * 2 * Nat.gcd 4 (2 ^ 2 - 1) = 4 := by norm_num
  rwa [h4] at h

end Outer

end CFSG.OddStandard.AltStdSec.SwapPartner
