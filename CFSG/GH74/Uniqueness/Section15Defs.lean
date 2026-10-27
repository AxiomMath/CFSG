module

public import CFSG.GH74.Uniqueness.Section15HeringStmt

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

structure Facts15 (M : Subgroup X) (n : ℕ) (L D K J Mo V : Subgroup X) : Prop where
  two_le : 2 ≤ n
  D_le : D ≤ M
  card_M : Nat.card M = 2 ^ (3 * n) * Nat.card D
  oddGen : closure {y : X | y ∈ M ∧ Odd (orderOf y)} = M
  fusion : ∀ x ∈ M, IsPGroup 2 (zpowers x) → ∀ g : X, g⁻¹ * x * g ∈ M →
    ∃ m ∈ M, m⁻¹ * x * m = g⁻¹ * x * g
  conj_D : ∀ s ∈ M, orderOf s = 2 → s ∉ Mo → ∃ m ∈ M, m⁻¹ * s * m ∈ D
  Mo_le_M : Mo ≤ M
  Mo_le_L : Mo ≤ L
  Mo_normal : ∀ g ∈ M, ∀ x ∈ Mo, g * x * g⁻¹ ∈ Mo
  card_Mo : Nat.card Mo = 2 ^ n
  Mo_sq : ∀ x ∈ Mo, x * x = 1
  cent_Mo_le : centralizer (Mo : Set X) ≤ M
  K_eq : K = D ⊓ L
  card_K : Nat.card K = 2 ^ n - 1
  K_cyclic : IsCyclic K
  K_trans : ∀ a ∈ Mo, a ≠ 1 → ∀ b ∈ Mo, b ≠ 1 → ∃ k ∈ K, k * a * k⁻¹ = b
  K_fpf : ∀ k ∈ K, k ≠ 1 → ∀ x ∈ Mo, k * x = x * k → x = 1
  J_eq : J = centralizer (L : Set X)
  J_le_D : J ≤ D
  L_inf_J : L ⊓ J = ⊥
  exists_inv_J : ∃ u ∈ J, orderOf u = 2
  D_le_N : D ≤ normalizer (L : Set X)
  N_eq : ∀ g ∈ normalizer (L : Set X), ∃ l ∈ L, ∃ d ∈ D, g = l * d
  NM_eq : ∀ g ∈ M, g ∈ normalizer (L : Set X) → ∃ m ∈ Mo, ∃ d ∈ D, g = m * d
  NY_le : ∀ Y : Subgroup X, Y ≤ J → Y ≠ ⊥ → normalizer (Y : Set X) ≤ normalizer (L : Set X)
  cent_Mo_N : ∀ g ∈ normalizer (L : Set X), (∀ x ∈ Mo, g * x = x * g) →
    ∃ m ∈ Mo, ∃ j ∈ J, g = m * j
  cent_K_D : ∀ d ∈ D, (∀ k ∈ K, d * k = k * d) → ∃ k ∈ K, ∃ j ∈ J, d = k * j
  out_cyclic : ∃ g₀ ∈ D, ∀ d ∈ D, ∃ i : ℕ, d * (g₀ ^ i)⁻¹ ∈ K ⊔ J
  out_three : n = 3 → ∀ g ∈ normalizer (L : Set X), g * g ∈ L ⊔ J → g ∈ L ⊔ J
  rank_le : ∀ A : Subgroup X, A ≤ normalizer (L : Set X) → (∀ a ∈ A, a * a = 1) →
    Nat.card A ≤ 2 ^ n * Nat.card ↥(A ⊓ J)
  inv_comm : ∀ u ∈ D, orderOf u = 2 → ∀ x ∈ Mo, u * x = x * u
  inv_conj : ∀ u ∈ D, orderOf u = 2 → ∀ g : X, g * u * g⁻¹ ∈ D → g ∈ normalizer (L : Set X)
  J_prime : ∀ y ∈ J, (orderOf y).Prime → orderOf y ≠ 2 →
    orderOf y ∣ 2 ^ n - 1 ∨ orderOf y ∣ 2 ^ n + 1
  J_dihedral : ¬ IsPGroup 2 J →
    (∀ y ∈ J, (orderOf y).Prime → orderOf y ≠ 2 → ¬ orderOf y ∣ 2 ^ n - 1) →
    ∃ J' : Subgroup X, J' ≤ J ∧ (∀ j ∈ J, j ∈ J' ↔ Odd (orderOf j)) ∧
      Nat.card J = 2 * Nat.card J'
  J_frob : (∃ W : Subgroup X, W ≤ J ∧ W ≠ ⊥ ∧ IsPGroup 2 W ∧
      ∀ j ∈ J, ∀ w ∈ W, j * w * j⁻¹ ∈ W) →
    ∃ U Y : Subgroup X, U ≤ J ∧ Y ≤ J ∧ IsPGroup 2 U ∧
      (∀ j ∈ J, IsPGroup 2 (zpowers j) → j ∈ U) ∧ (∀ x ∈ U, x * x = 1) ∧
      Odd (Nat.card Y) ∧ Nat.card Y ∣ 2 ^ n - 1 ∧ (∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) ∧
      (∀ j ∈ J, ∃ x ∈ U, ∃ y ∈ Y, j = x * y) ∧
      (∀ y ∈ Y, y ≠ 1 → ∀ x ∈ U, y * x = x * y → x = 1)
  V_le : V ≤ M
  V_normal : ∀ g ∈ M, ∀ v ∈ V, g * v * g⁻¹ ∈ V
  V_pgroup : IsPGroup 2 V
  V_max : ∀ N : Subgroup X, N ≤ M → (∀ g ∈ M, ∀ x ∈ N, g * x * g⁻¹ ∈ N) → IsPGroup 2 N → N ≤ V
  V_comm : ∀ v ∈ V, ∀ x ∈ Mo, v * x = x * v

end CFSG.GH74.Uniqueness
