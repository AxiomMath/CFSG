module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.Induction.AutBound

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem mem_normalizer_of_map_le [Finite G] (T : Subgroup G) (π : G)
    (h : T.map (MulAut.conj π).toMonoidHom ≤ T) : π ∈ normalizer (T : Set G) := by
  have hcard : Nat.card (T.map (MulAut.conj π).toMonoidHom) = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj π).injective
  have heq : T.map (MulAut.conj π).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge h (le_of_eq hcard.symm)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨x', hx', hx'e⟩ := hx
    have : x' = x := (MulAut.conj π).injective hx'e
    rwa [← this]

theorem factorization_two_of_odd {a m : ℕ} (hm : Odd m) : (2 ^ a * m).factorization 2 = a := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by
      intro h
      exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h))]
  simp

theorem exists_conj_of_card_eq [Finite G] (P A B : Subgroup G) (hA : A ≤ P) (hB : B ≤ P) {a m : ℕ}
    (hm : Odd m) (hP : Nat.card P = 2 ^ a * m) (hAc : Nat.card A = 2 ^ a)
    (hBc : Nat.card B = 2 ^ a) :
    ∃ p ∈ P, ∀ x : G, x ∈ B ↔ p⁻¹ * x * p ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card P).factorization 2 = a := by rw [hP]; exact factorization_two_of_odd hm
  let A' : Subgroup P := A.subgroupOf P
  let B' : Subgroup P := B.subgroupOf P
  have hA' : Nat.card A' = 2 ^ (Nat.card P).factorization 2 := by
    rw [hfac, ← hAc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have hB' : Nat.card B' = 2 ^ (Nat.card P).factorization 2 := by
    rw [hfac, ← hBc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  let SA : Sylow 2 P := Sylow.ofCard A' hA'
  let SB : Sylow 2 P := Sylow.ofCard B' hB'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P SA SB
  refine ⟨(g : G), g.2, fun x => ?_⟩
  have hSB : (SB : Subgroup P) = B' := rfl
  have hSA : (SA : Subgroup P) = A' := rfl
  have key : ∀ y : P, y ∈ B' ↔ g⁻¹ * y * g ∈ A' := by
    intro y
    have h2 : (↑(g • SA) : Subgroup P) = MulAut.conj g • (SA : Subgroup P) :=
      Sylow.coe_subgroup_smul
    rw [hg, hSB, hSA] at h2
    rw [h2, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [mul_assoc]
  by_cases hx : x ∈ P
  · have := key ⟨x, hx⟩
    simpa [B', A', Subgroup.mem_subgroupOf, mul_assoc] using this
  · constructor
    · intro hxB
      exact absurd (hB hxB) hx
    · intro hxA
      exfalso
      have := hA hxA
      refine hx ?_
      have h3 : x = (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ := by group
      rw [h3]
      exact P.mul_mem (P.mul_mem g.2 this) (P.inv_mem g.2)

end CFSG.EvenSporadicStandard.Induction.AutBound
