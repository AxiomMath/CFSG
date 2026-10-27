module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.EvenSporadicStandard.HSStd.HOv

open Equiv Subgroup
open scoped Pointwise

theorem card_perm_seven_factorization_two :
    (Nat.card (Perm (Fin 7))).factorization 2 = 4 := by
  have h : Nat.card (Perm (Fin 7)) = 5040 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  rw [h, show (5040 : ℕ) = 2 ^ 4 * 315 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_sq_ne_one_of_card_sixteen_perm_seven (A : Subgroup (Perm (Fin 7)))
    (hcard : Nat.card A = 16) : ∃ x ∈ A, x ^ 2 ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let PA : Sylow 2 (Perm (Fin 7)) :=
    Sylow.ofCard A (by rw [hcard, card_perm_seven_factorization_two]; norm_num)
  have hPA : (PA : Subgroup (Perm (Fin 7))) = A := rfl
  set c : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 with hc
  have hc2 : ¬ c ^ 2 ^ 1 = 1 := by rw [hc]; decide
  have hc4 : c ^ 2 ^ (1 + 1) = 1 := by rw [hc]; decide
  have hord : orderOf c = 2 ^ (1 + 1) := orderOf_eq_prime_pow hc2 hc4
  have hP : IsPGroup 2 (zpowers c) :=
    IsPGroup.of_card (n := 1 + 1) (by rw [Nat.card_zpowers, hord])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 7)) Q PA
  have hmem : g * c * g⁻¹ ∈ A := by
    have h1 : c ∈ (Q : Subgroup (Perm (Fin 7))) := hQ (mem_zpowers c)
    have h2 : (MulAut.conj g) c ∈ MulAut.conj g • (Q : Subgroup (Perm (Fin 7))) :=
      Subgroup.smul_mem_pointwise_smul c (MulAut.conj g) _ h1
    have h3 : MulAut.conj g • (Q : Subgroup (Perm (Fin 7))) = A := by
      rw [← Sylow.coe_subgroup_smul, hg]
      exact hPA
    rw [h3] at h2
    simpa [MulAut.conj_apply] using h2
  refine ⟨g * c * g⁻¹, hmem, fun h => hc2 ?_⟩
  rw [conj_pow] at h
  simpa using h

theorem not_exists_sq_eq_one_sixteen_of_mulEquiv_perm_seven {D : Type*} [Group D]
    (e : D ≃* Perm (Fin 7)) :
    ¬ ∃ A : Subgroup D, (∀ x ∈ A, x ^ 2 = 1) ∧ Nat.card ↥A = 16 := by
  rintro ⟨A, hA, hcard⟩
  obtain ⟨x, hx, hx2⟩ := exists_sq_ne_one_of_card_sixteen_perm_seven (A.map e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.injective, hcard])
  obtain ⟨a, ha, rfl⟩ := hx
  exact hx2 (by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hA a ha, map_one])

end CFSG.EvenSporadicStandard.HSStd.HOv
