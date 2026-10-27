module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCalculus
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Unipotent

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.SignalizerFunctorTheorem.NonLocalExc

theorem pow_eight_of_mem_posUnipotent_g2
    {K : Type} [Field K] [CharP K 2] {y : ModGL .G2 K} (hy : y ∈ posUnipotent .G2 K) :
    y ^ 8 = 1 := by
  obtain ⟨A, B, C, D, E, F, rfl⟩ := exists_g2N_of_mem_posUnipotent hy
  have e2 : g2N A B C D E F ^ 2 = g2N 0 0 (A * B) (A ^ 2 * B) (A ^ 3 * B + A ^ 2 * C + A * D)
      (A * C ^ 2 + B * E + A * B * D + C * D + A ^ 2 * B * C) := by
    rw [sq]
    exact g2N_mul_self A B C D E F
  have e4 : g2N A B C D E F ^ 4 = g2N 0 0 0 0 0 (A * B * (A ^ 2 * B)) := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, e2, sq, g2N_mul_self]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  rw [show 8 = 4 * 2 from rfl, pow_mul, e4, sq, g2N_mul_self, ← g2N_zero]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem pow_eight_of_two_power_g2
    {K : Type} [Field K] [Finite K] [CharP K 2] {x : ModGL .G2 K} (hx : x ∈ adjointGroup .G2 K)
    {m : ℕ} (hxm : x ^ 2 ^ m = 1) : x ^ 8 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC : Subgroup.zpowers x ≤ adjointGroup .G2 K := (Subgroup.zpowers_le).2 hx
  have hPr : IsPGroup 2 (Subgroup.zpowers x) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hxm)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨g, -, hg⟩ := exists_conj_le_posUnipotent 2 hPC hPr
  have h8 := pow_eight_of_mem_posUnipotent_g2 (hg x (Subgroup.mem_zpowers x))
  have hconj : (g⁻¹ * x * g) ^ 8 = g⁻¹ * x ^ 8 * g := by
    simpa only [inv_inv] using conj_pow (a := g⁻¹) (b := x) (i := 8)
  rw [hconj] at h8
  have : x ^ 8 = g * (g⁻¹ * x ^ 8 * g) * g⁻¹ := by group
  rw [this, h8]
  group

end CFSG.EvenSporadicStandard.Induction
