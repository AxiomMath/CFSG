module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelFrame
public import Certificates.Data.ChengHeldPresProps

public section

namespace CFSG.OddStandard.ChengHeld.Model

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel Subgroup
open CFSG.OddStandard.ChengHeld.M1b (evalE)

section Defs

variable {H : Type} [Group H]

@[expose] def sD (x : Fin 7 → H) : Subgroup H := closure {x 0, x 1, x 2}
@[expose] def sR1 (x : Fin 7 → H) : Subgroup H := closure {x 0, x 1, x 2, x 3, x 4}
@[expose] def sR2 (x : Fin 7 → H) : Subgroup H := closure {x 0, x 1, x 2, x 5, x 6}
@[expose] def sV (x : Fin 7 → H) : Subgroup H := closure {x 0 ^ 2, x 1, x 0 * x 2}
@[expose] def sW (x : Fin 7 → H) : Subgroup H := centralizer (sV x : Set H)

@[expose] def twClass (σ : H →* H) (s : H) : Set H := {s' | ∃ y : H, s' = y⁻¹ * s * σ y}

@[expose] def TwSizes (σ : H →* H) (sizes : List ℕ) : Prop :=
  ∃ reps : List H, (reps.map fun s => (twClass σ s).ncard) = sizes ∧
    (∀ s ∈ reps, s * σ s = 1) ∧ reps.Pairwise (fun s₁ s₂ => s₂ ∉ twClass σ s₁) ∧
    ∀ s, s * σ s = 1 → ∃ s' ∈ reps, s ∈ twClass σ s'

structure Struct4Facts (α : ℕ) (H : Type) [Group H] (x : Fin 7 → H) : Prop where
  ord_t : orderOf (x 0) = 4
  center : center H = zpowers (x 0)
  commutator : ⁅(⊤ : Subgroup H), ⊤⁆ = sD x
  card_D : Nat.card (sD x) = 16
  card_R1 : Nat.card (sR1 x) = 64
  card_R2 : Nat.card (sR2 x) = 64
  inf_R : sR1 x ⊓ sR2 x = sD x
  center_R1 : sR1 x ⊓ centralizer (sR1 x : Set H) = zpowers (x 0)
  center_R2 : sR2 x ⊓ centralizer (sR2 x : Set H) = zpowers (x 0)
  involutions : {a : H | a ≠ 1 ∧ a * a = 1}.ncard = 55
  involutions_mem : ∀ a : H, a * a = 1 → a ∈ sR1 x ∨ a ∈ sR2 x
  R1_invol : {a : H | a ∈ sR1 x ∧ a ∉ zpowers (x 0) ∧ a * a = 1}.ncard = 30
  R1_ord4 : {a : H | a ∈ sR1 x ∧ a ∉ zpowers (x 0) ∧ orderOf a = 4}.ncard = 30
  R2_invol : {a : H | a ∈ sR2 x ∧ a ∉ zpowers (x 0) ∧ a * a = 1}.ncard = 30
  R2_ord4 : {a : H | a ∈ sR2 x ∧ a ∉ zpowers (x 0) ∧ orderOf a = 4}.ncard = 30
  no_root : ∀ s : H, s ^ 2 ≠ x 0 ∧ s ^ 2 ≠ (x 0)⁻¹
  elemAb_le : ∀ E : Subgroup H, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a * a = 1) →
    Nat.card E ≤ 8
  V_comm : ∀ a ∈ sV x, ∀ b ∈ sV x, a * b = b * a
  V_sq : ∀ a ∈ sV x, a * a = 1
  card_V : Nat.card (sV x) = 8
  card_W : Nat.card (sW x) = 64
  W_comm_iff : (∀ a ∈ sW x, ∀ b ∈ sW x, a * b = b * a) ↔ α = 0
  W_invol : ∀ a ∈ sW x, a * a = 1 → a ∈ sV x
  W_ord8 : ∀ a ∈ sW x, orderOf a ≠ 8
  W_center : α = 1 → sW x ⊓ centralizer (sW x : Set H) = closure {x 0, x 1, x 0 * x 2}
  W_commutator : α = 1 → ⁅sW x, sW x⁆ = zpowers (x 0 ^ 2)
  sq_mlxt : (x 3 * x 4 * x 6 * x 2) ^ 2 = x 1
  comm_mlx : (x 3 * x 4 * x 6)⁻¹ * (x 3 * x 5 * x 6)⁻¹ * (x 3 * x 4 * x 6) * (x 3 * x 5 * x 6) = 1 ↔
    α = 0

structure Struct2Facts (H : Type) [Group H] (x : Fin 7 → H) : Prop where
  ord_q : orderOf (x 0) = 2
  center : center H = sD x
  commutator : ⁅(⊤ : Subgroup H), ⊤⁆ = sD x
  card_D : Nat.card (sD x) = 8
  card_R1 : Nat.card (sR1 x) = 32
  card_R2 : Nat.card (sR2 x) = 32
  R1_comm : ∀ a ∈ sR1 x, ∀ b ∈ sR1 x, a * b = b * a
  R1_sq : ∀ a ∈ sR1 x, a * a = 1
  R2_comm : ∀ a ∈ sR2 x, ∀ b ∈ sR2 x, a * b = b * a
  R2_sq : ∀ a ∈ sR2 x, a * a = 1
  inf_R : sR1 x ⊓ sR2 x = sD x
  involutions : {a : H | a ≠ 1 ∧ a * a = 1}.ncard = 55
  involutions_mem : ∀ a : H, a * a = 1 → a ∈ sR1 x ∨ a ∈ sR2 x
  elemAb_le : ∀ E : Subgroup H, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a * a = 1) →
    Nat.card E ≤ 32
  elemAb_32 : ∀ E : Subgroup H, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a * a = 1) →
    Nat.card E = 32 → E = sR1 x ∨ E = sR2 x
  no_root_q : ∀ s : H, s ^ 2 ≠ x 0
  root_pi : ∃ s : H, s ^ 2 = x 1
  root_qpi : ∃ s : H, s ^ 2 = x 0 * x 1
  root_tau : ∃ s : H, s ^ 2 = x 2
  root_qtau : ∃ s : H, s ^ 2 = x 0 * x 2
  sq_mlx : (x 3 * x 4 * x 6) ^ 2 = x 1
  sq_mz : (x 3 * x 5) ^ 2 = x 0 * x 1

@[expose] def qOf (α : ℕ) (x : Fin 7 → H) : H := if α = 2 then x 0 else x 0 ^ 2

@[expose] def fixedSub (k : ℕ) (x : Fin 7 → H) : Subgroup H :=
  if k = 0 then closure {x 0, x 1, x 3 * x 4, x 6}
  else if k = 1 then closure {x 0, x 1, x 2}
  else closure {x 0, x 3 * x 4 * x 6 * x 2}

structure AutFacts (α k : ℕ) (σ : H →* H) (x : Fin 7 → H) : Prop where
  invol : ∀ h, σ (σ h) = h
  fixed_card : Nat.card {h : H // σ h = h} = (autData α k).1
  T_card : {s : H | s * σ s = 1}.ncard = (autData α k).2.1
  classes : TwSizes σ (autData α k).2.2.1
  flag : qOf α x ∈ twClass σ 1 ↔ (autData α k).2.2.2 = true
  fixed_le : α ≤ 1 → {h | σ h = h} ⊆ (fixedSub k x : Set H)
  fixed_eq : α = 2 → {h | σ h = h} = (fixedSub k x : Set H)
  graph_orbit : α = 2 → k = 1 →
    x 1 ∈ twClass σ 1 ∧ x 0 * x 2 ∈ twClass σ 1 ∧ x 0 * (x 1 * x 2) ∈ twClass σ 1

@[expose] def IsOrbitOf (Fs : List (H → H)) (a : H) (O : Set H) : Prop :=
  a ∈ O ∧ (∀ F ∈ Fs, ∀ y ∈ O, F y ∈ O) ∧
    ∀ P : Set H, a ∈ P → (∀ F ∈ Fs, ∀ y ∈ P, F y ∈ P) → O ⊆ P

@[expose] def gMaps (γ : H →* H) (x : Fin 7 → H) : List (H → H) :=
  (γ : H → H) :: (List.range 7).map fun j h => (natFam x j)⁻¹ * h * natFam x j

structure GFacts (α : ℕ) (γ : H →* H) (x : Fin 7 → H) : Prop where
  bij : Function.Bijective γ
  ord3 : (∀ h, γ (γ (γ h)) = h) ∧ ∃ h, γ h ≠ h
  fixed_free : ∀ y : H, y⁻¹ * γ y ∈ zpowers (x 0) → y ∈ zpowers (x 0)
  D_stable : ∀ y ∈ sD x, γ y ∈ sD x
  orbits2 : α = 2 → IsOrbitOf (gMaps γ x) (x 0) {x 0} ∧
    IsOrbitOf (gMaps γ x) (x 1) {x 1, x 0 * x 1 * x 2, x 0 * x 2} ∧
    IsOrbitOf (gMaps γ x) (x 2) {x 2, x 0 * x 1, x 1 * x 2} ∧
    [x 1, x 0 * x 1 * x 2, x 0 * x 2, x 2, x 0 * x 1, x 1 * x 2, x 0].Nodup
  V_stable : α ≤ 1 → ∀ y ∈ sV x, γ y ∈ sV x
  orbit4 : α ≤ 1 → IsOrbitOf (gMaps γ x) (x 1) ((sV x : Set H) \ {1, x 0 ^ 2})

end Defs

end CFSG.OddStandard.ChengHeld.Model
