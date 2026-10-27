module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.QuotC
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Facts

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {C : Type} [Group C]

structure CCore (c : CInv C) : Prop where
  odd : ∀ M : Subgroup C, M.Normal → Odd (Nat.card ↥M) → M = ⊥
  two : ∀ Q : Subgroup C, Q.Normal → IsPGroup 2 ↥Q → Q ≤ zpowers c.z
  two_part : ¬ 2 ^ 22 ∣ Nat.card C

structure RData (c : CInv C) (R : Subgroup C) : Prop where
  z_mem : c.z ∈ R
  card : Nat.card ↥R = 2 ^ 13
  sq : ∀ x ∈ R, x ^ 2 ∈ zpowers c.z
  comm : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ zpowers c.z
  center : ∀ x ∈ R, (∀ y ∈ R, x * y = y * x) → x ∈ zpowers c.z
  self : ∀ g : C, (∀ r ∈ R, g * r * g⁻¹ * r⁻¹ ∈ zpowers c.z) → g ∈ R
  irr : ∀ U : Subgroup C, zpowers c.z ≤ U → U ≤ R →
    (∀ x ∈ normalizer (R : Set C), ∀ u ∈ U, x * u * x⁻¹ ∈ U) → U = zpowers c.z ∨ U = R

structure JData (c : CInv C) (t : C) (R J : Subgroup C) : Prop where
  t_sq : t ^ 2 = 1
  t_not : t ∉ zpowers c.z
  t_mem : t ∈ R
  R_le : R ≤ J
  mem_iff : ∀ g : C, g ∈ J ↔ g * t * g⁻¹ * t⁻¹ ∈ zpowers c.z
  R_normal : ∀ j ∈ J, ∀ r ∈ R, j * r * j⁻¹ ∈ R
  two : ∀ W : Subgroup C, W ≤ J → (∀ j ∈ J, ∀ w ∈ W, j * w * j⁻¹ ∈ W) → IsPGroup 2 ↥W → W ≤ R
  quot : ∃ (X : Type) (_ : Group X) (π : ↥J →* X), Function.Surjective π ∧
    π.ker = R.subgroupOf J ∧ IsU42Two X

structure KDataC (c : CInv C) (t : C) (R J K O Y : Subgroup C) : Prop where
  K_le_J : K ≤ J
  K_cent : ∀ k ∈ K, k * t = t * k
  O_eq : R ⊓ K = O
  O_card : Nat.card ↥O = 2 ^ 12
  V_le : closure {t, c.z} ≤ O
  V_card : Nat.card ↥(closure {t, c.z}) = 4
  Y_le : Y ≤ K
  Y_perfect : ⁅Y, Y⁆ = Y
  lattice : ∀ U : Subgroup C, closure {t, c.z} ≤ U → U ≤ O →
    (∀ y ∈ Y, ∀ u ∈ U, y * u * y⁻¹ ∈ U) →
    Nat.card ↥U = 2 ^ 2 ∨ Nat.card ↥U = 2 ^ 3 ∨ Nat.card ↥U = 2 ^ 11 ∨ Nat.card ↥U = 2 ^ 12
  quot : ∃ (X : Type) (_ : Group X) (π : ↥K →* X), Function.Surjective π ∧
    π.ker = O.subgroupOf K ∧ IsU42Two X

structure Y0Data (Y0 : Subgroup C) : Prop where
  perfect : ⁅Y0, Y0⁆ = Y0
  card : Nat.card ↥Y0 = 2 ^ 20 * 3 ^ 3 * 5

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
