module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaModel
public import CFSG.LargeExtraspecial.DW37Input

public section

namespace CFSG.ComponentClassification.AS81.HeTri

open Subgroup CFSG.Monster.B.Co2 CFSG.ComponentClassification.AS81.HeSylow
  CFSG.ComponentClassification.AS81.Hexa CFSG.LargeExtraspecial
open scoped MatrixGroups

noncomputable abbrev heZeta : Equiv.Perm (Fin 64) := permOfArr 64 heZetaArr

noncomputable abbrev heN0 : Subgroup (Equiv.Perm (Fin 64)) := hexaT ⊔ hexaM

noncomputable abbrev heP12 : Subgroup (Equiv.Perm (Fin 64)) :=
  heN0 ⊓ centralizer ({hexaT0P} : Set (Equiv.Perm (Fin 64)))

noncomputable abbrev heB0 : Subgroup (Equiv.Perm (Fin 64)) := grpN 64 heB0Gens

noncomputable abbrev heF0 : Subgroup (Equiv.Perm (Fin 64)) := grpN 64 heF0Gens

noncomputable abbrev heP23 : Subgroup (Equiv.Perm (Fin 64)) := grpN 64 heP23Gens

noncomputable abbrev hePC : Subgroup (Equiv.Perm (Fin 32)) := grpN 32 hePCGens

noncomputable abbrev heTC : Equiv.Perm (Fin 32) := permOfArr 32 heTCArr

noncomputable abbrev heBC : Subgroup (Equiv.Perm (Fin 32)) := grpN 32 heBCGens

noncomputable def heP12C (s : Bool) : Subgroup (Equiv.Perm (Fin 32)) :=
  grpN 32 (if s then heP13CGens else heP12CGens)

noncomputable def heEC (s : Bool) : Subgroup (Equiv.Perm (Fin 32)) :=
  grpN 32 (if s then heFCGens else heECGens)

structure HeModelFacts : Prop where
  T_inf_M : hexaT ⊓ hexaM = ⊥
  zeta_mem : heZeta ∈ hexaM
  zeta_pow : heZeta ^ 3 = 1
  zeta_ne : heZeta ≠ 1
  zeta_fix : ∀ t ∈ hexaT, heZeta * t * heZeta⁻¹ = t → t = 1
  zeta_normal : ∀ m ∈ hexaM, m * heZeta * m⁻¹ = heZeta ∨ m * heZeta * m⁻¹ = heZeta⁻¹
  orbit : ∀ t ∈ hexaT, t ≠ 1 → (∃ m ∈ hexaM, m * t * m⁻¹ = hexaT0P) ∨
    ∃ m ∈ hexaM, m * t = t * m ∧ orderOf m = 5
  card_P12 : Nat.card heP12 = 3072
  B0_le : heB0 ≤ heP12
  card_B0 : Nat.card heB0 = 1024
  T_le_B0 : hexaT ≤ heB0
  F0_le_B0 : heF0 ≤ heB0
  F0_sq : ∀ x ∈ heF0, x * x = 1
  card_F0 : Nat.card heF0 = 64
  F0_ne : heF0 ≠ hexaT
  normal_B0 : ∀ X : Subgroup (Equiv.Perm (Fin 64)), X ≤ heB0 →
    (∀ b ∈ heB0, ∀ x ∈ X, b * x * b⁻¹ ∈ X) → (∀ x ∈ X, x * x = 1) → Nat.card X = 64 →
      X = hexaT ∨ X = heF0
  P23_eq : heP23 = heN0 ⊓ normalizer (heF0 : Set (Equiv.Perm (Fin 64)))
  P23_gens : ∀ a ∈ heP23Gens, ∃ k : ℕ, permOfArr 64 a ^ (2 ^ k) = 1
  bridge : Nonempty (↥(centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} :
    Set (SL(5, ZMod 2)))) ≃* ↥hePC)
  card_PC : Nat.card hePC = 21504
  TC_mem : heTC ∈ hePC
  center_PC : ∀ x ∈ hePC, (∀ y ∈ hePC, x * y = y * x) → x = 1 ∨ x = heTC
  BC_le : heBC ≤ hePC
  card_BC : Nat.card heBC = 1024
  P12C_le : ∀ s, heBC ≤ heP12C s ∧ heP12C s ≤ hePC
  card_P12C : ∀ s, Nat.card (heP12C s) = 3072
  P12C_inf : heP12C false ⊓ heP12C true = heBC
  EC_le_BC : ∀ s, heEC s ≤ heBC
  normal_BC : ∀ X : Subgroup (Equiv.Perm (Fin 32)), X ≤ heBC →
    (∀ b ∈ heBC, ∀ x ∈ X, b * x * b⁻¹ ∈ X) → (∀ x ∈ X, x * x = 1) → Nat.card X = 64 →
      X = heEC false ∨ X = heEC true
  EC_le : ∀ s, heEC s ≤ heP12C s
  EC_sq : ∀ s, ∀ x ∈ heEC s, x * x = 1
  card_EC : ∀ s, Nat.card (heEC s) = 64
  normal_EC : ∀ s, ∀ X : Subgroup (Equiv.Perm (Fin 32)), X ≤ heP12C s →
    (∀ b ∈ heP12C s, ∀ x ∈ X, b * x * b⁻¹ ∈ X) → (∀ x ∈ X, x * x = 1) → Nat.card X = 64 →
      X = heEC s
  TC_mem_EC : ∀ s, heTC ∈ heEC s
  cent_EC : ∀ s, hePC ⊓ centralizer (heEC s : Set (Equiv.Perm (Fin 32))) ≤ heEC s
  norm_EC : ∀ s, hePC ⊓ normalizer (heEC s : Set (Equiv.Perm (Fin 32))) = heP12C s

end CFSG.ComponentClassification.AS81.HeTri
