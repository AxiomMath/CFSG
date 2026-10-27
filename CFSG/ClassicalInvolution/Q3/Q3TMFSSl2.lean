module

public import CFSG.ClassicalInvolution.SolvableCase.SL2Three

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T.MFS

open scoped MatrixGroups
open CFSG.ClassicalInvolution

private theorem sl2_prod_cube_one :
    ∀ x : SL(2, ZMod 3), ∃ a b c : SL(2, ZMod 3),
      a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ c ^ 3 = 1 ∧ x = a * b * c := by
  decide +kernel

private theorem sl2_conj_three :
    ∀ g h : SL(2, ZMod 3), (g ^ 3 = 1 ∧ g ≠ 1) → (h ^ 3 = 1 ∧ h ≠ 1) →
      ∃ c : SL(2, ZMod 3), c * g * c⁻¹ = h ∨ c * g * c⁻¹ = h⁻¹ := by
  decide +kernel

private theorem sl2_conj_four :
    ∀ g h : SL(2, ZMod 3), (g ^ 4 = 1 ∧ g ^ 2 ≠ 1) → (h ^ 4 = 1 ∧ h ^ 2 ≠ 1) →
      ∃ c : SL(2, ZMod 3), c * g * c⁻¹ = h := by
  decide +kernel

private theorem sl2_prod_four :
    ∀ x : SL(2, ZMod 3), x ^ 4 = 1 → ∃ a b : SL(2, ZMod 3),
      (a = 1 ∨ (a ^ 4 = 1 ∧ a ^ 2 ≠ 1)) ∧ (b = 1 ∨ (b ^ 4 = 1 ∧ b ^ 2 ≠ 1)) ∧ x = a * b := by
  decide +kernel

private theorem sl2_order_six :
    ∀ g : SL(2, ZMod 3), g ^ 3 = 1 ∨ g ^ 4 = 1 ∨ ((g ^ 4) ^ 3 = 1 ∧ g ^ 4 ≠ 1) := by
  decide +kernel

private theorem natCard_sq_one : Nat.card {g : SL(2, ZMod 3) // g ^ 2 = 1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem normal_sl2Three_index_cases (N : Subgroup SL(2, ZMod 3)) [hN : N.Normal] :
    N.index = 1 ∨ N.index = 3 ∨ N.index = 12 ∨ N.index = 24 := by
  have hconj : ∀ g ∈ N, ∀ c : SL(2, ZMod 3), c * g * c⁻¹ ∈ N := fun g hg c => hN.conj_mem g hg c
  by_cases hA : ∃ g ∈ N, g ^ 3 = 1 ∧ g ≠ 1
  ·
    obtain ⟨g, hgN, hg3, hg1⟩ := hA
    have hall : ∀ a : SL(2, ZMod 3), a ^ 3 = 1 → a ∈ N := by
      intro a ha
      by_cases ha1 : a = 1
      · rw [ha1]; exact N.one_mem
      · obtain ⟨c, hc | hc⟩ := sl2_conj_three g a ⟨hg3, hg1⟩ ⟨ha, ha1⟩
        · rw [← hc]; exact hconj g hgN c
        · have h1 : c * g * c⁻¹ ∈ N := hconj g hgN c
          have h2 : a⁻¹ ∈ N := by rw [← hc]; exact h1
          simpa using N.inv_mem h2
    have htop : N = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := sl2_prod_cube_one x
      exact N.mul_mem (N.mul_mem (hall a ha) (hall b hb)) (hall c hc)
    left
    rw [htop, Subgroup.index_top]
  · have hA' : ∀ g ∈ N, g ^ 3 = 1 → g = 1 := fun g hg h3 => by
      by_contra hne
      exact hA ⟨g, hg, h3, hne⟩
    have h4 : ∀ g ∈ N, g ^ 4 = 1 := by
      intro g hg
      rcases sl2_order_six g with h | h | ⟨h3, h1⟩
      · rw [hA' g hg h]; exact one_pow 4
      · exact h
      · exact absurd (hA' (g ^ 4) (N.pow_mem hg 4) h3) h1
    by_cases hC : ∃ g ∈ N, g ^ 2 ≠ 1
    · obtain ⟨g, hgN, hg2⟩ := hC
      have hg4 := h4 g hgN
      have hQN : sl2ThreeQ ≤ N := by
        intro x hx
        obtain ⟨a, b, ha, hb, rfl⟩ := sl2_prod_four x (mem_sl2ThreeQ_iff.mp hx)
        have hmem : ∀ c : SL(2, ZMod 3), (c = 1 ∨ (c ^ 4 = 1 ∧ c ^ 2 ≠ 1)) → c ∈ N := by
          intro c hc
          rcases hc with rfl | ⟨hc4, hc2⟩
          · exact N.one_mem
          · obtain ⟨u, hu⟩ := sl2_conj_four g c ⟨hg4, hg2⟩ ⟨hc4, hc2⟩
            rw [← hu]; exact hconj g hgN u
        exact N.mul_mem (hmem a ha) (hmem b hb)
      have hNQ : N ≤ sl2ThreeQ := fun g hg => mem_sl2ThreeQ_iff.mpr (h4 g hg)
      have hEq : N = sl2ThreeQ := le_antisymm hNQ hQN
      right; left
      rw [hEq]
      exact sl2ThreeQ_index
    · have hC' : ∀ g ∈ N, g ^ 2 = 1 := fun g hg => by
        by_contra hne
        exact hC ⟨g, hg, hne⟩
      have hcard : Nat.card N ≤ 2 := by
        have hle : Nat.card N ≤ Nat.card {g : SL(2, ZMod 3) // g ^ 2 = 1} := by
          apply Nat.card_le_card_of_injective
            (fun x : N => (⟨x.1, hC' x.1 x.2⟩ : {g : SL(2, ZMod 3) // g ^ 2 = 1}))
          intro x y hxy
          have := congrArg (fun z : {g : SL(2, ZMod 3) // g ^ 2 = 1} => z.1) hxy
          exact Subtype.ext this
        rwa [natCard_sq_one] at hle
      have hmul := Subgroup.card_mul_index N
      rw [natCard_sl2Three] at hmul
      have hpos : 0 < Nat.card N := Nat.card_pos
      have hcases : Nat.card N = 1 ∨ Nat.card N = 2 := by omega
      right; right
      rcases hcases with h | h
      · right
        rw [h] at hmul
        omega
      · left
        rw [h] at hmul
        omega

end CFSG.ClassicalInvolution.Q3.Q3T.MFS
