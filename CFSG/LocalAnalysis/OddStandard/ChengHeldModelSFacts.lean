module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelFacts
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelLoop

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.ChengHeld.M1b (evalE)

section Generic

variable {G : Type} [Group G]

@[expose] def ClassSizes (S : Subgroup G) (y : G) (sizes : List ℕ) : Prop :=
  ∃ reps : List G, (∀ z ∈ reps, (∃ s ∈ S, z = s * y) ∧ z * z = 1) ∧
    (reps.map fun z => {z' : G | ∃ s ∈ S, z' = s⁻¹ * z * s}.ncard) = sizes ∧
    reps.Pairwise (fun z₁ z₂ => ¬ ∃ s ∈ S, z₂ = s⁻¹ * z₁ * s) ∧
    ∀ z : G, (∃ s ∈ S, z = s * y) → z * z = 1 → ∃ z' ∈ reps, ∃ s ∈ S, z = s⁻¹ * z' * s

@[expose] def qOfG (α : ℕ) (xG : Fin 7 → G) : G := if α = 2 then xG 0 else xG 0 ^ 2

@[expose] def fixedSubG (k : ℕ) (xG : Fin 7 → G) : Subgroup G :=
  if k = 0 then closure {xG 0, xG 1, xG 3 * xG 4, xG 6}
  else if k = 1 then closure {xG 0, xG 1, xG 2}
  else closure {xG 0, xG 3 * xG 4 * xG 6 * xG 2}

structure AutFactsG (S : Subgroup G) (xG : Fin 7 → G) (α k : ℕ) (y : G) : Prop where
  invol : ∀ s ∈ S, y⁻¹ * (y⁻¹ * s * y) * y = s
  fixed_card : {s : G | s ∈ S ∧ y⁻¹ * s * y = s}.ncard = (autData α k).1
  fixed_le : α ≤ 1 → ∀ s ∈ S, y⁻¹ * s * y = s → s ∈ fixedSubG k xG
  fixed_eq : α = 2 → ∀ s ∈ S, (y⁻¹ * s * y = s ↔ s ∈ fixedSubG k xG)
  coset_card : y * y = 1 →
    {z : G | (∃ s ∈ S, z = s * y) ∧ z * z = 1}.ncard = (autData α k).2.1
  coset_classes : y * y = 1 → ClassSizes S y (autData α k).2.2.1
  flag : y * y = 1 →
    ((∃ s ∈ S, s⁻¹ * y * s = qOfG α xG * y) ↔ (autData α k).2.2.2 = true)
  graph_orbit : y * y = 1 → α = 2 → k = 1 →
    (∃ s ∈ S, s⁻¹ * y * s = xG 1 * y) ∧ (∃ s ∈ S, s⁻¹ * y * s = xG 0 * xG 2 * y) ∧
      (∃ s ∈ S, s⁻¹ * y * s = xG 0 * (xG 1 * xG 2) * y)

@[expose] def gMapsG (g : G) (xG : Fin 7 → G) : List (G → G) :=
  (fun h => g⁻¹ * h * g) :: (List.range 7).map fun j h =>
    (xG (Fin.ofNat 7 j))⁻¹ * h * xG (Fin.ofNat 7 j)

structure GFactsG (S : Subgroup G) (xG : Fin 7 → G) (α : ℕ) (g : G) : Prop where
  cube : ∀ s ∈ S, g⁻¹ * (g⁻¹ * (g⁻¹ * s * g) * g) * g = s
  nontrivial : ∃ s ∈ S, g⁻¹ * s * g ≠ s
  fixed_free : ∀ s ∈ S, s⁻¹ * (g⁻¹ * s * g) ∈ zpowers (xG 0) → s ∈ zpowers (xG 0)
  D_stable : ∀ s ∈ closure ({xG 0, xG 1, xG 2} : Set G),
    g⁻¹ * s * g ∈ closure ({xG 0, xG 1, xG 2} : Set G)
  orbits2 : α = 2 → IsOrbitOf (gMapsG g xG) (xG 0) {xG 0} ∧
    IsOrbitOf (gMapsG g xG) (xG 1) {xG 1, xG 0 * xG 1 * xG 2, xG 0 * xG 2} ∧
    IsOrbitOf (gMapsG g xG) (xG 2) {xG 2, xG 0 * xG 1, xG 1 * xG 2} ∧
    [xG 1, xG 0 * xG 1 * xG 2, xG 0 * xG 2, xG 2, xG 0 * xG 1, xG 1 * xG 2, xG 0].Nodup
  V_stable : α ≤ 1 → ∀ s ∈ closure ({xG 0 ^ 2, xG 1, xG 0 * xG 2} : Set G),
    g⁻¹ * s * g ∈ closure ({xG 0 ^ 2, xG 1, xG 0 * xG 2} : Set G)
  orbit4 : α ≤ 1 → IsOrbitOf (gMapsG g xG) (xG 1)
    ((closure ({xG 0 ^ 2, xG 1, xG 0 * xG 2} : Set G) : Set G) \ {1, xG 0 ^ 2})

end Generic

section Charts

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}

@[expose] def Chart4.D {α : ℕ} (c : Chart4 d α) : Subgroup G := closure {c.t, c.pi, c.tau}
@[expose] def Chart4.R1 {α : ℕ} (c : Chart4 d α) : Subgroup G :=
  closure {c.t, c.pi, c.tau, c.mu, c.lam}
@[expose] def Chart4.R2 {α : ℕ} (c : Chart4 d α) : Subgroup G :=
  closure {c.t, c.pi, c.tau, c.ze, c.xi}
@[expose] def Chart2.D (c : Chart2 d) : Subgroup G := closure {d.q, c.pi, c.tau}
@[expose] def Chart2.R1 (c : Chart2 d) : Subgroup G := closure {d.q, c.pi, c.tau, c.mu, c.lam}
@[expose] def Chart2.R2 (c : Chart2 d) : Subgroup G := closure {d.q, c.pi, c.tau, c.ze, c.xi}

structure Chart4.SFacts {α : ℕ} (c : Chart4 d α) : Prop where
  card_S : Nat.card ↥d.S = 256
  ord_t : orderOf c.t = 4
  center : d.S ⊓ centralizer (d.S : Set G) = zpowers c.t
  derived : ⁅d.S, d.S⁆ = c.D
  card_D : Nat.card c.D = 16
  card_R1 : Nat.card c.R1 = 64
  card_R2 : Nat.card c.R2 = 64
  inf_R : c.R1 ⊓ c.R2 = c.D
  center_R1 : c.R1 ⊓ centralizer (c.R1 : Set G) = zpowers c.t
  center_R2 : c.R2 ⊓ centralizer (c.R2 : Set G) = zpowers c.t
  involutions : {s : G | s ∈ d.S ∧ s ≠ 1 ∧ s * s = 1}.ncard = 55
  involutions_mem : ∀ s ∈ d.S, s * s = 1 → s ∈ c.R1 ∨ s ∈ c.R2
  R1_invol : {s : G | s ∈ c.R1 ∧ s ∉ zpowers c.t ∧ s * s = 1}.ncard = 30
  R1_ord4 : {s : G | s ∈ c.R1 ∧ s ∉ zpowers c.t ∧ orderOf s = 4}.ncard = 30
  R2_invol : {s : G | s ∈ c.R2 ∧ s ∉ zpowers c.t ∧ s * s = 1}.ncard = 30
  R2_ord4 : {s : G | s ∈ c.R2 ∧ s ∉ zpowers c.t ∧ orderOf s = 4}.ncard = 30
  no_root : ∀ s ∈ d.S, s ^ 2 ≠ c.t ∧ s ^ 2 ≠ c.t⁻¹
  elemAb_le : ∀ E : Subgroup G, E ≤ d.S → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
    (∀ a ∈ E, a * a = 1) → Nat.card E ≤ 8
  V_comm : ∀ a ∈ c.V, ∀ b ∈ c.V, a * b = b * a
  V_sq : ∀ a ∈ c.V, a * a = 1
  card_V : Nat.card c.V = 8
  card_W : Nat.card c.W = 64
  W_comm_iff : (∀ a ∈ c.W, ∀ b ∈ c.W, a * b = b * a) ↔ α = 0
  W_invol : ∀ a ∈ c.W, a * a = 1 → a ∈ c.V
  W_ord8 : ∀ a ∈ c.W, orderOf a ≠ 8
  W_center : α = 1 → c.W ⊓ centralizer (c.W : Set G) = closure {c.t, c.pi, c.t * c.tau}
  W_derived : α = 1 → ⁅c.W, c.W⁆ = zpowers (c.t ^ 2)
  sq_mlxt : (c.mu * c.lam * c.xi * c.tau) ^ 2 = c.pi
  comm_mlx : cm (c.mu * c.lam * c.xi) (c.mu * c.ze * c.xi) = 1 ↔ α = 0

structure Chart2.SFacts (c : Chart2 d) : Prop where
  card_S : Nat.card ↥d.S = 128
  center : d.S ⊓ centralizer (d.S : Set G) = c.D
  derived : ⁅d.S, d.S⁆ = c.D
  card_D : Nat.card c.D = 8
  card_R1 : Nat.card c.R1 = 32
  card_R2 : Nat.card c.R2 = 32
  R1_comm : ∀ a ∈ c.R1, ∀ b ∈ c.R1, a * b = b * a
  R1_sq : ∀ a ∈ c.R1, a * a = 1
  R2_comm : ∀ a ∈ c.R2, ∀ b ∈ c.R2, a * b = b * a
  R2_sq : ∀ a ∈ c.R2, a * a = 1
  inf_R : c.R1 ⊓ c.R2 = c.D
  involutions : {s : G | s ∈ d.S ∧ s ≠ 1 ∧ s * s = 1}.ncard = 55
  involutions_mem : ∀ s ∈ d.S, s * s = 1 → s ∈ c.R1 ∨ s ∈ c.R2
  elemAb_le : ∀ E : Subgroup G, E ≤ d.S → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
    (∀ a ∈ E, a * a = 1) → Nat.card E ≤ 32
  elemAb_32 : ∀ E : Subgroup G, E ≤ d.S → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
    (∀ a ∈ E, a * a = 1) → Nat.card E = 32 → E = c.R1 ∨ E = c.R2
  no_root_q : ∀ s ∈ d.S, s ^ 2 ≠ d.q
  root_pi : ∃ s ∈ d.S, s ^ 2 = c.pi
  root_qpi : ∃ s ∈ d.S, s ^ 2 = d.q * c.pi
  root_tau : ∃ s ∈ d.S, s ^ 2 = c.tau
  root_qtau : ∃ s ∈ d.S, s ^ 2 = d.q * c.tau
  sq_mlx : (c.mu * c.lam * c.xi) ^ 2 = c.pi
  sq_mz : (c.mu * c.ze) ^ 2 = d.q * c.pi

end Charts

end CFSG.OddStandard.ChengHeld
