module

public import CFSG.CGT.Hall82.ModelData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModels

public section

namespace CFSG.CGT.Hall82

open CFSG.ComponentClassification.AS81.Hexa CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.HeTri CFSG.Monster.B.Co2

noncomputable abbrev hexaL : Subgroup (Equiv.Perm (Fin 64)) := grpN 64 hallLGens

@[expose] def fixPts (B : Set (Equiv.Perm (Fin 64))) : Set (Fin 64) := {i | ∀ b ∈ B, b i = i}

noncomputable abbrev hallYP : Equiv.Perm (Fin 64) := permOfArr 64 hallY

noncomputable abbrev hallTP : Equiv.Perm (Fin 64) := permOfArr 64 hallT

structure ModelFacts : Prop where
  le : hexaL ≤ hexaM
  card_hexaM : Nat.card hexaM = 2160
  card : Nat.card hexaL = 1080
  conj_mem : ∀ m ∈ hexaM, ∀ x ∈ hexaL, m * x * m⁻¹ ∈ hexaL
  eq_of_card : ∀ N : Subgroup (Equiv.Perm (Fin 64)), N ≤ hexaM → Nat.card N = 1080 → N = hexaL
  zeta_mem : heZeta ∈ hexaL
  center : ∀ x ∈ hexaL, (∀ y ∈ hexaL, x * y = y * x) → x ∈ Subgroup.zpowers heZeta
  apply_zero : ∀ x ∈ hexaM, x 0 = 0
  eq_bot : ∀ X : Subgroup (Equiv.Perm (Fin 64)), X ≤ hexaM → IsPGroup 2 X →
    (∀ a ∈ hexaL, ∀ x ∈ X, a * x * a⁻¹ ∈ X) → X = ⊥
  le_32 : ∀ (v : Fin 64) (X : Subgroup (Equiv.Perm (Fin 64))), X ≤ hexaM → IsPGroup 2 X →
    (∀ x ∈ X, x v = v) → (∀ a ∈ hexaL, a v = v → ∀ x ∈ X, a * x * a⁻¹ ∈ X) →
    ∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ X → B ≠ ⊥ →
      Nat.card B * Nat.card (fixPts B) ≤ 32
  le_64 : ∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ hexaM → IsPGroup 2 B →
    Nat.card B * Nat.card (fixPts B) ≤ 64
  le_32_of_not_le : ∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ hexaM → IsPGroup 2 B →
    ¬ B ≤ hexaL → Nat.card B * Nat.card (fixPts B) ≤ 32
  of_fixPts_eq : ∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ hexaM → IsPGroup 2 B →
    4 ≤ Nat.card B → (∀ b ∈ B, b ≠ 1 → fixPts {b} = fixPts B) →
      B ≤ hexaL ∧ Nat.card B = 4 ∧ (∀ b ∈ B, b * b = 1) ∧ Nat.card (fixPts B) = 16
  fixPts_le_8 : ∀ x ∈ hexaM, x ∉ hexaL → x * x = 1 → Nat.card (fixPts {x}) ≤ 8
  y_mem : hallYP ∈ hexaL
  t_mem : hallTP ∈ hexaL
  t_mul_t : hallTP * hallTP = 1
  y_pow_four : hallYP ^ 4 = 1
  y_sq_ne_one : hallYP ^ 2 ≠ 1
  ty_mul_ty : (hallTP * hallYP) * (hallTP * hallYP) = 1
  card_closure : Nat.card (Subgroup.closure ({hallYP, hallTP} : Set (Equiv.Perm (Fin 64)))) = 8
  conj_t : ∀ x ∈ hexaL, x * x = 1 → x ≠ 1 → ∃ a ∈ hexaL, a * hallTP * a⁻¹ = x

end CFSG.CGT.Hall82
