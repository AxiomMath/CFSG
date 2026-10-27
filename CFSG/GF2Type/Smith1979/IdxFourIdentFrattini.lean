module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open scoped Pointwise

theorem frattini_of_normalizes {G : Type*} [Group G] [Finite G] (X E P A : Subgroup G)
    (hEX : E ≤ X) (hEn : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E) (hPE : P ≤ E)
    (hP : Nat.card P = 3 ^ ((Nat.card E).factorization 3))
    (hA : ∀ n ∈ X, (∀ p ∈ P, n * p * n⁻¹ ∈ P) → ∀ a ∈ A, n * a * n⁻¹ ∈ A) :
    ∀ x ∈ X, ∃ e ∈ E, ∃ n ∈ X, (∀ a ∈ A, n * a * n⁻¹ ∈ A) ∧ x = e * n := by
  intro x hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP1 : Nat.card (P.subgroupOf E) = 3 ^ ((Nat.card E).factorization 3) := by
    rw [← hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv
  let P1 : Sylow 3 E := Sylow.ofCard (P.subgroupOf E) hP1
  let φ : E →* E :=
    { toFun := fun e => ⟨x * e * x⁻¹, hEn x hx e e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hφ : Function.Injective φ := by
    intro a b hab
    have h : x * (a : G) * x⁻¹ = x * (b : G) * x⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  have hQ : Nat.card ((P.subgroupOf E).map φ) = 3 ^ ((Nat.card E).factorization 3) := by
    rw [← hP1]
    exact Subgroup.card_map_of_injective hφ
  let P2 : Sylow 3 E := Sylow.ofCard ((P.subgroupOf E).map φ) hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq E P1 P2
  have hgP : MulAut.conj g • (P.subgroupOf E) = (P.subgroupOf E).map φ := by
    exact congrArg (fun S : Sylow 3 E => (S : Subgroup E)) hg
  have hn : ∀ p ∈ P, ((g : G)⁻¹ * x) * p * ((g : G)⁻¹ * x)⁻¹ ∈ P := by
    intro p hp
    have h1 : φ ⟨p, hPE hp⟩ ∈ MulAut.conj g • (P.subgroupOf E) := by
      rw [hgP]
      exact ⟨⟨p, hPE hp⟩, hp, rfl⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have h2 := Subgroup.mem_subgroupOf.mp h1
    simpa [φ, mul_assoc] using h2
  refine ⟨g, g.2, (g : G)⁻¹ * x, mul_mem (inv_mem (hEX g.2)) hx,
    hA _ (mul_mem (inv_mem (hEX g.2)) hx) hn, by simp⟩

end CFSG.GF2Type.Smith1979.IdxFour
