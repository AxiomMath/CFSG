module

public import CFSG.RankThree.OddKernel.OddLift
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X]

structure Z4IData (N Q Y V V' B K : Subgroup X) (ρ t τ l : X) : Prop where
  odd_N : Odd (Nat.card N)
  N_le_K : N ≤ K
  Q_comm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a
  card_Q : Nat.card Q = 64
  normal_Q : ∀ g x : X, x ∈ Q → g * x * g⁻¹ ∈ Q
  cent_Q : ∀ g : X, (∀ q ∈ Q, g * q = q * g) → g ∈ Q ⊔ N
  Q_le_K : Q ≤ K
  relIndex_K : (Q ⊔ N).relIndex K = 4
  Q_eq : Q = B ⊔ V'
  B_le_Q : B ≤ Q
  Y_le_Q : Y ≤ Q
  Y_eq : Y = V ⊔ V'
  V_inf_V' : V ⊓ V' = ⊥
  card_V : Nat.card V = 4
  card_V' : Nat.card V' = 4
  sq_mem_V : ∀ q ∈ Q, q ^ 2 ∈ V
  K_cent_Y : ∀ k ∈ K, ∀ y ∈ Y, k * y = y * k
  comm_KQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ V
  rho_pow_three : ρ ^ 3 = 1
  rho_norm_Q : ∀ x ∈ Q, ρ * x * ρ⁻¹ ∈ Q
  rho_norm_Y : ∀ x ∈ Y, ρ * x * ρ⁻¹ ∈ Y
  rho_norm_V : ∀ x ∈ V, ρ * x * ρ⁻¹ ∈ V
  rho_norm_V' : ∀ x ∈ V', ρ * x * ρ⁻¹ ∈ V'
  rho_norm_B : ∀ x ∈ B, ρ * x * ρ⁻¹ ∈ B
  rho_norm_K : ∀ x ∈ K, ρ * x * ρ⁻¹ ∈ K
  rho_fpf_Q : ∀ q ∈ Q, ρ * q * ρ⁻¹ = q → q = 1
  rho_fpf_KQ : ∀ k ∈ K, ρ * k * ρ⁻¹ * k⁻¹ ∈ Q ⊔ N → k ∈ Q ⊔ N
  card_B : Nat.card B = 16
  Y_sq : ∀ y ∈ Y, y * y = 1
  normal_Y : ∀ g x : X, x ∈ Y → g * x * g⁻¹ ∈ Y
  normal_V : ∀ g x : X, x ∈ V → g * x * g⁻¹ ∈ V
  t_ne_one : t ≠ 1
  t_ne_tau : t ≠ τ
  t_sq : t * t = 1
  tau_sq : τ * τ = 1
  l_sq : l * l = 1
  t_tau : t * τ = τ * t
  t_l : t * l = l * t
  tau_l : τ * l = l * τ
  t_rho : t * ρ = ρ * t
  tau_rho : τ * ρ = ρ * τ
  l_rho : l * ρ * l⁻¹ = ρ⁻¹
  t_norm_K : ∀ k ∈ K, t * k * t⁻¹ ∈ K
  tau_norm_K : ∀ k ∈ K, τ * k * τ⁻¹ ∈ K
  l_norm_K : ∀ k ∈ K, l * k * l⁻¹ ∈ K
  comm_t_K : ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ Q ⊔ N
  tau_inv : ∀ q ∈ Q, τ * q * τ⁻¹ = q⁻¹
  tau_not_mem_Q : τ ∉ Q ⊔ N
  B_cent_t : ∀ b ∈ B, t * b = b * t
  cent_t_Q : ∀ q ∈ Q, t * q = q * t → q ∈ B
  V_cent_t : ∀ v ∈ V, t * v = v * t
  Y_cent_t : ∀ y ∈ Y, t * y = y * t → y ∈ V
  bound : ∀ R : Subgroup X, IsPGroup 2 R → R ≤ centralizer ({t} : Set X) → Nat.card R ≤ 128
  not_conj : ∀ g : X, g * t * g⁻¹ ≠ t * τ

section quotient

variable (N : Subgroup X) [N.Normal]

@[expose] abbrev z4iπ : X →* X ⧸ N := QuotientGroup.mk' N

theorem z4iπ_surjective : Function.Surjective (z4iπ N) :=
  QuotientGroup.mk'_surjective N

theorem z4iπ_ker : (z4iπ N).ker = N :=
  QuotientGroup.ker_mk' N

theorem z4iπ_eq_iff {a b : X} : z4iπ N a = z4iπ N b ↔ a⁻¹ * b ∈ N := by
  change (a : X ⧸ N) = (b : X ⧸ N) ↔ a⁻¹ * b ∈ N
  exact QuotientGroup.eq

theorem z4i_comap_map_sup (A : Subgroup X) : (A.map (z4iπ N)).comap (z4iπ N) = A ⊔ N := by
  rw [Subgroup.comap_map_eq (f := z4iπ N), z4iπ_ker]

theorem z4iπ_mem_map_iff {A : Subgroup X} {x : X} :
    z4iπ N x ∈ A.map (z4iπ N) ↔ x ∈ A ⊔ N := by
  rw [← Subgroup.mem_comap, z4i_comap_map_sup]

theorem z4i_map_sup_N (A : Subgroup X) : (A ⊔ N).map (z4iπ N) = A.map (z4iπ N) := by
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]

theorem z4i_inf_N_eq_bot (hN : Odd (Nat.card N)) [Finite X] {P : Subgroup X}
    (hP : IsPGroup 2 P) : P ⊓ N = ⊥ :=
  CFSG.RankThree.OddKernel.inf_eq_bot_of_odd hP hN

theorem z4iπ_injOn (hN : Odd (Nat.card N)) [Finite X] {P : Subgroup X} (hP : IsPGroup 2 P)
    {a b : X} (ha : a ∈ P) (hb : b ∈ P) (h : z4iπ N a = z4iπ N b) : a = b := by
  have hmemN : a⁻¹ * b ∈ N := (z4iπ_eq_iff N).1 h
  have hmemP : a⁻¹ * b ∈ P := P.mul_mem (P.inv_mem ha) hb
  have hbot : a⁻¹ * b ∈ (⊥ : Subgroup X) := by
    rw [← z4i_inf_N_eq_bot N hN hP]
    exact ⟨hmemP, hmemN⟩
  exact inv_mul_eq_one.1 (Subgroup.mem_bot.1 hbot)

theorem z4i_card_map (hN : Odd (Nat.card N)) [Finite X] {P : Subgroup X} (hP : IsPGroup 2 P) :
    Nat.card (P.map (z4iπ N)) = Nat.card P := by
  have hker : Odd (Nat.card (z4iπ N).ker) := by rw [z4iπ_ker]; exact hN
  have hinj : Function.Injective ((z4iπ N).comp P.subtype) :=
    CFSG.RankThree.OddKernel.injective_restrict_of_odd (z4iπ N) hker hP
  have hmap : (⊤ : Subgroup P).map ((z4iπ N).comp P.subtype) = P.map (z4iπ N) := by
    rw [← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
  rw [← hmap, Subgroup.card_map_of_injective (K := (⊤ : Subgroup P)) hinj]
  exact Nat.card_congr (Subgroup.topEquiv (G := P)).toEquiv

theorem z4i_map_inf (hN : Odd (Nat.card N)) [Finite X] {P A B : Subgroup X} (hP : IsPGroup 2 P)
    (hA : A ≤ P) (hB : B ≤ P) :
    (A ⊓ B).map (z4iπ N) = A.map (z4iπ N) ⊓ B.map (z4iπ N) := by
  refine le_antisymm (Subgroup.map_inf_le A B (z4iπ N)) ?_
  rintro y ⟨⟨a, ha, rfl⟩, ⟨b, hb, hbe⟩⟩
  have hb' : b = a := z4iπ_injOn N hN hP (hB hb) (hA ha) hbe
  exact ⟨a, ⟨ha, hb' ▸ hb⟩, rfl⟩

theorem z4i_commute_of_map {Q : Subgroup X} (hQN : Q ⊓ N = ⊥) {a q : X}
    (ha : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q) (hq : q ∈ Q) (h : z4iπ N a * z4iπ N q = z4iπ N q * z4iπ N a) :
    a * q = q * a := by
  have hcQ : a * q * a⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (ha q hq) (Q.inv_mem hq)
  have hc1 : z4iπ N (a * q * a⁻¹ * q⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [h]
    group
  have hcN : a * q * a⁻¹ * q⁻¹ ∈ N := by
    rw [← z4iπ_ker N]
    exact MonoidHom.mem_ker.2 hc1
  have hbot : a * q * a⁻¹ * q⁻¹ = 1 := by
    have hmem : a * q * a⁻¹ * q⁻¹ ∈ (⊥ : Subgroup X) := by
      rw [← hQN]
      exact ⟨hcQ, hcN⟩
    exact Subgroup.mem_bot.1 hmem
  have haq : a * q * a⁻¹ = q := by
    calc a * q * a⁻¹ = (a * q * a⁻¹ * q⁻¹) * q := by group
      _ = 1 * q := by rw [hbot]
      _ = q := one_mul q
  calc a * q = (a * q * a⁻¹) * a := by group
    _ = q * a := by rw [haq]

end quotient

namespace Z4IData

variable {N Q Y V V' B K : Subgroup X} {ρ t τ l : X}

theorem isPGroup_Q (h : Z4IData N Q Y V V' B K ρ t τ l) : IsPGroup 2 Q :=
  IsPGroup.of_card (n := 6) (by rw [h.card_Q]; norm_num)

theorem V_le_Q (h : Z4IData N Q Y V V' B K ρ t τ l) : V ≤ Q := by
  calc V ≤ V ⊔ V' := le_sup_left
    _ = Y := h.Y_eq.symm
    _ ≤ Q := h.Y_le_Q

theorem V'_le_Q (h : Z4IData N Q Y V V' B K ρ t τ l) : V' ≤ Q := by
  calc V' ≤ V ⊔ V' := le_sup_right
    _ = Y := h.Y_eq.symm
    _ ≤ Q := h.Y_le_Q

theorem Q_inf_N [Finite X] [N.Normal] (h : Z4IData N Q Y V V' B K ρ t τ l) : Q ⊓ N = ⊥ :=
  z4i_inf_N_eq_bot N h.odd_N h.isPGroup_Q

end Z4IData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
