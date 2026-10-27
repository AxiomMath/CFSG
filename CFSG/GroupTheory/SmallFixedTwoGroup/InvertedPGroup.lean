module

public import CFSG.GroupTheory.SmallFixedTwoGroup.InvertedOdd

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

variable {G : Type*} [Group G]

theorem inverted_of_card_inverted_ge [Finite G] {θ : MulAut G} (hθ : θ * θ = 1) {p : ℕ}
    [Fact p.Prime] (hp : 5 ≤ p) {R : Subgroup G} (hR : IsPGroup p R)
    (hRθ : ∀ r ∈ R, θ r ∈ R)
    (hcard : Nat.card R ≤ 4 * Nat.card {r : R // θ r = (r : G)⁻¹}) :
    ∀ r ∈ R, θ r = r⁻¹ := by
  have hpodd : Odd p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd' with h | h
    · omega
    · exact h
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR
  have hoddR : Odd (Nat.card R) := by
    rw [hn]
    exact hpodd.pow
  have hcount := card_inverted_mul_card_fixed_of_odd hθ hRθ hoddR
  haveI : Nonempty {r : R // θ r = (r : G)⁻¹} := ⟨⟨1, by simp⟩⟩
  have hSpos : 0 < Nat.card {r : R // θ r = (r : G)⁻¹} := Nat.card_pos
  have hC4 : Nat.card {r : R // θ r = (r : G)} ≤ 4 := by
    have h2 : Nat.card {r : R // θ r = (r : G)⁻¹} * Nat.card {r : R // θ r = (r : G)}
        ≤ Nat.card {r : R // θ r = (r : G)⁻¹} * 4 := by
      rw [hcount, mul_comm (Nat.card {r : R // θ r = (r : G)⁻¹}) 4]
      exact hcard
    exact Nat.le_of_mul_le_mul_left h2 hSpos
  let K : Subgroup R :=
    { carrier := {r | θ (r : G) = (r : G)}
      mul_mem' := by
        intro a b ha hb
        rw [Set.mem_setOf_eq] at ha hb
        rw [Set.mem_setOf_eq]
        simp only [Subgroup.coe_mul, map_mul, ha, hb]
      one_mem' := by
        simp
      inv_mem' := by
        intro a ha
        rw [Set.mem_setOf_eq] at ha
        rw [Set.mem_setOf_eq]
        simp only [Subgroup.coe_inv, map_inv, ha] }
  have hKcard : Nat.card K ≤ 4 := by
    have hEq : Nat.card K = Nat.card {r : R // θ (r : G) = (r : G)} := rfl
    rw [hEq]
    exact hC4
  have hKp : IsPGroup p K := hR.to_subgroup K
  have hKbot : K = ⊥ := by
    rcases hKp.card_eq_or_dvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hpos : 0 < Nat.card K := Nat.card_pos
      have hp_le : p ≤ Nat.card K := Nat.le_of_dvd hpos h1
      omega
  refine inverted_of_invariant_of_fixed_eq_one hθ hRθ ?_
  intro r hr hfix
  have hmem : (⟨r, hr⟩ : R) ∈ K := hfix
  have h1 : (⟨r, hr⟩ : R) = 1 := by
    have : (⟨r, hr⟩ : R) ∈ (⊥ : Subgroup R) := hKbot ▸ hmem
    simpa using this
  exact Subtype.ext_iff.mp h1

end CFSG.GroupTheory.SmallFixedTwoGroup
