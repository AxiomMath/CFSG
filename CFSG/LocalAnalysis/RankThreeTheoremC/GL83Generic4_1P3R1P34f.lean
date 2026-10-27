module

import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem p34_zpowers_eq_of_mem [Finite G] {z y : G} (hz : orderOf z = 3) (hy : y ∈ zpowers z)
    (hy1 : y ≠ 1) : zpowers y = zpowers z := by
  have h1 : orderOf y ∣ 3 := hz ▸ orderOf_dvd_of_mem_zpowers hy
  have hyo : orderOf y = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  exact Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hy)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hz])

theorem p34_conj_eq_of_pow {x y : G} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) {m : ℕ}
    (hy : y ^ (3 ^ m) = 1) (h : y * x * y⁻¹ ∈ zpowers x) : y * x * y⁻¹ = x := by
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp h
  have hiter : ∀ n : ℕ, y ^ n * x * (y ^ n)⁻¹ = x ^ (j ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc y ^ (n + 1) * x * (y ^ (n + 1))⁻¹ = y * (y ^ n * x * (y ^ n)⁻¹) * y⁻¹ := by group
        _ = y * x ^ (j ^ n) * y⁻¹ := by rw [ih]
        _ = (y * x * y⁻¹) ^ (j ^ n) := by rw [conj_zpow]
        _ = (x ^ j) ^ (j ^ n) := by rw [← hj]
        _ = x ^ (j ^ (n + 1)) := by rw [← zpow_mul, pow_succ, mul_comm]
  have h1 : x ^ (j ^ (3 ^ m)) = x := by rw [← hiter, hy]; simp
  have h2 : x ^ (j ^ (3 ^ m) - 1) = 1 := by rw [zpow_sub_one, h1, mul_inv_cancel]
  have h3 : (3 : ℤ) ∣ j ^ (3 ^ m) - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rwa [hxo] at this
  have h4 : (j : ZMod 3) = 1 := by
    have h5 : ((j ^ (3 ^ m) - 1 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h3
    push_cast at h5
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [ZMod.pow_card_pow] at h5
    exact sub_eq_zero.mp h5
  have h6 : (3 : ℤ) ∣ j - 1 := by
    have h7 : ((j - 1 : ℤ) : ZMod 3) = 0 := by push_cast; rw [h4]; simp
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h7
  have h8 : x ^ (j - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rwa [hxo])
  rw [← hj]
  calc x ^ j = x ^ (j - 1) * x := by rw [← zpow_add_one]; congr 1; ring
    _ = x := by rw [h8, one_mul]

theorem p34_centralizer_zpowers (y : G) :
    centralizer ((zpowers y : Subgroup G) : Set G) = centralizer ({y} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem p34_false_of_three_lines [Finite G] {x : G} {Q : Subgroup G}
    (hL33 : ∀ D : Subgroup G, D ≤ Q → IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
      ¬ ∃ S : Finset (Subgroup G), S.card = 3 ∧ ∀ L ∈ S, L ≤ D ∧ Nat.card L = 3 ∧
        ∃ g : G, L = (zpowers x).map (MulAut.conj g).toMonoidHom)
    {D : Subgroup G} (hDQ : D ≤ Q) (hD : IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2)
    {y₁ y₂ y₃ : G} (h₁ : y₁ ∈ D) (h₂ : y₂ ∈ D) (h₃ : y₃ ∈ D) (n₁ : y₁ ≠ 1) (n₂ : y₂ ≠ 1)
    (n₃ : y₃ ≠ 1) (d₁₂ : zpowers y₁ ≠ zpowers y₂) (d₁₃ : zpowers y₁ ≠ zpowers y₃)
    (d₂₃ : zpowers y₂ ≠ zpowers y₃) (c₁ : ∃ g : G, g * x * g⁻¹ = y₁)
    (c₂ : ∃ g : G, g * x * g⁻¹ = y₂) (c₃ : ∃ g : G, g * x * g⁻¹ = y₃) : False := by
  classical
  refine hL33 D hDQ hD hDc ⟨{zpowers y₁, zpowers y₂, zpowers y₃}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [d₁₂, d₁₃]),
      Finset.card_insert_of_notMem (by simp [d₂₃]), Finset.card_singleton]
  · have key : ∀ y : G, y ∈ D → y ≠ 1 → (∃ g : G, g * x * g⁻¹ = y) →
        zpowers y ≤ D ∧ Nat.card (zpowers y) = 3 ∧
          ∃ g : G, zpowers y = (zpowers x).map (MulAut.conj g).toMonoidHom := by
      intro y hyD hy1 ⟨g, hg⟩
      refine ⟨zpowers_le.mpr hyD, ?_, g, ?_⟩
      · exact CFSG.LocalAnalysis.RankFourTheoremC.card_zpowers_of_isElemAbelian Nat.prime_three
          hD hyD hy1
      · rw [MonoidHom.map_zpowers, ← hg]
        rfl
    intro L hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · exact key y₁ h₁ n₁ c₁
    · exact key y₂ h₂ n₂ c₂
    · exact key y₃ h₃ n₃ c₃

end CFSG.LocalAnalysis.RankThreeTheoremC
