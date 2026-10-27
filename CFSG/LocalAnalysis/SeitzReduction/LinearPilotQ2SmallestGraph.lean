module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

section Generic

variable {H : Type*} [Group H]

theorem exists_commute_lift_of_odd {N : Subgroup H} (hN : Odd (Nat.card N)) [Finite N]
    {t : H} (ht : t * t = 1) {x : H} (hx : x⁻¹ * t * x * t ∈ N) :
    ∃ z ∈ N, x * z * t = t * (x * z) := by
  set m := x⁻¹ * t * x * t with hm
  have hmo : Odd (orderOf m) := by
    have h1 : orderOf (⟨m, hx⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hN h1
  obtain ⟨k, hk⟩ := hmo
  refine ⟨m ^ (k + 1), pow_mem hx _, ?_⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htx : t * x = x * m * t := by
    rw [hm]
    calc t * x = x * (x⁻¹ * t * x) * (t * t) := by rw [ht]; group
      _ = x * (x⁻¹ * t * x * t) * t := by group
  have hconj : t * m * t = m⁻¹ := by
    rw [hm]
    calc t * (x⁻¹ * t * x * t) * t = t * x⁻¹ * t * x * (t * t) := by group
      _ = t * x⁻¹ * t * x := by rw [ht, mul_one]
      _ = (x⁻¹ * t⁻¹ * x * t⁻¹)⁻¹ := by group
      _ = (x⁻¹ * t * x * t)⁻¹ := by rw [htinv]
  have hconjk : ∀ j : ℕ, t * m ^ j * t = m⁻¹ ^ j := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, mul_one, ht]
    | succ j ih =>
      calc t * m ^ (j + 1) * t = (t * m ^ j * t) * (t * m * t) := by
            rw [pow_succ]
            calc t * (m ^ j * m) * t = t * m ^ j * (t * t) * m * t := by rw [ht]; group
              _ = (t * m ^ j * t) * (t * m * t) := by group
        _ = m⁻¹ ^ (j + 1) := by rw [ih, hconj, pow_succ]
  have hmk : m * m⁻¹ ^ (k + 1) = m ^ (k + 1) := by
    have h1 : m ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one m
    rw [inv_pow, mul_inv_eq_iff_eq_mul, ← pow_add]
    calc m = m ^ (2 * k + 1) * m := by rw [h1, one_mul]
      _ = m ^ (k + 1 + (k + 1)) := by rw [← pow_succ]; ring_nf
  calc x * m ^ (k + 1) * t = x * (m * m⁻¹ ^ (k + 1)) * t := by rw [hmk]
    _ = x * m * (t * m ^ (k + 1) * t) * t := by rw [hconjk]; group
    _ = (x * m * t) * m ^ (k + 1) * (t * t) := by group
    _ = t * (x * m ^ (k + 1)) := by rw [ht, mul_one, ← htx]; group

end Generic

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem mem_oddCore_centralizer_of_le_centralizer_odd {X : Subgroup G} (hXC : X ≤ centralizer (X : Set G))
    (hodd : Odd (Nat.card X)) {x : G} (hx : x ∈ X) :
    (⟨x, hXC hx⟩ : centralizer (X : Set G)) ∈ CFSG.oddCore (centralizer (X : Set G)) := by
  have hn : (X.subgroupOf (centralizer (X : Set G))).Normal := by
    constructor
    intro y hy h
    rw [mem_subgroupOf] at hy ⊢
    have h1 : (h : G) * (y : G) = (y : G) * (h : G) := (mem_centralizer_iff.1 h.2 (y : G) hy).symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1, mul_inv_cancel_right]
    exact hy
  have hcard : Nat.card (X.subgroupOf (centralizer (X : Set G))) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv
  have hle : X.subgroupOf (centralizer (X : Set G)) ≤ CFSG.oddCore (centralizer (X : Set G)) :=
    le_sSup ⟨hn, hcard ▸ hodd⟩
  exact hle (mem_subgroupOf.2 hx)

end Setting

end CFSG.SeitzReduction.LinearPilot
