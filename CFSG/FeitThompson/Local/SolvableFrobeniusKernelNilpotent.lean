module

public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Local.SolvableKernelFixedFreePrimeNilpotent

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

variable {G : Type*} [Group G]

theorem inf_centralizer_zpowers_eq_bot {H : Subgroup G} {e : G}
    (h : H ⊓ centralizer ({e} : Set G) = ⊥) :
    H ⊓ centralizer ((zpowers e : Subgroup G) : Set G) = ⊥ := by
  rwa [zpowers_eq_closure, centralizer_closure]

theorem isNilpotent_of_isSolvable_of_inf_centralizer_eq_bot [Finite G] {H E : Subgroup G}
    [H.Normal] [Group.IsSolvable ↥H] (hinf : H ⊓ E = ⊥) (hE : E ≠ ⊥)
    (hC : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥) : Group.IsNilpotent ↥H := by
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥E)
    fun h => hE (Subgroup.eq_bot_of_card_eq E h)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) p hpdvd
  have hmem : (x : G) ∈ E := x.2
  have horder : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hx]
  have hne : (x : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at horder
    exact hp.one_lt.ne horder
  set R : Subgroup G := zpowers (x : G) with hR
  have hHR : H ⊓ R = ⊥ :=
    le_antisymm (hinf.le.trans' (inf_le_inf_left H (zpowers_le.2 hmem))) bot_le
  have hCR : H ⊓ centralizer (R : Set G) = ⊥ := inf_centralizer_zpowers_eq_bot (hC _ hmem hne)
  have hcardR : Nat.card (R.subgroupOf (H ⊔ R)) = p := by
    rw [Nat.card_eq_of_bijective _ (subgroupOfEquivOfLe (le_sup_right (a := H) (b := R))).bijective,
      hR, Nat.card_zpowers, horder]
  have hsol : Group.IsSolvable ↥(H.subgroupOf (H ⊔ R)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (le_sup_left (a := H) (b := R))).toMonoidHom)
      (by simpa using (subgroupOfEquivOfLe (le_sup_left (a := H) (b := R))).injective)
  have hnil := isNilpotent_of_isSolvable_of_natCard_eq_prime
    (H := H.subgroupOf (H ⊔ R)) (R := R.subgroupOf (H ⊔ R))
    coe_subgroupOf_mul_coe_subgroupOf_eq_univ
    (subgroupOf_inf_subgroupOf_eq_bot (H := H) (L := H) (R := R) hHR le_rfl) hp hcardR
    (subgroupOf_inf_centralizer_eq_bot (H := H) (L := H) (R := R) hCR le_rfl)
  exact Group.nilpotent_of_mulEquiv (_h := hnil) (subgroupOfEquivOfLe (le_sup_left (a := H)))

theorem isNilpotent_of_isSolvable_of_forall_inf_centralizer_eq_bot [Finite G] {H E : Subgroup G}
    [H.Normal] [Group.IsSolvable ↥H] (_hprod : (H : Set G) * (E : Set G) = Set.univ)
    (hinf : H ⊓ E = ⊥) (_hH : H ≠ ⊥) (hE : E ≠ ⊥)
    (hC : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥) : Group.IsNilpotent ↥H :=
  isNilpotent_of_isSolvable_of_inf_centralizer_eq_bot hinf hE hC

theorem exists_central_series_of_isSolvable_of_inf_centralizer_eq_bot [Finite G] {H E : Subgroup G}
    [H.Normal] [Group.IsSolvable ↥H] (hprod : (H : Set G) * (E : Set G) = Set.univ)
    (hinf : H ⊓ E = ⊥) (hH : H ≠ ⊥) (hE : E ≠ ⊥)
    (hC : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥) :
    ∃ (n : ℕ) (X : ℕ → Subgroup ↥H), X 0 = ⊥ ∧ X n = ⊤ ∧ Monotone X ∧ (∀ i, (X i).Normal) ∧
      ∀ i, ⁅(⊤ : Subgroup ↥H), X (i + 1)⁆ ≤ X i := by
  have : Group.IsNilpotent ↥H :=
    isNilpotent_of_isSolvable_of_forall_inf_centralizer_eq_bot hprod hinf hH hE hC
  obtain ⟨n, hn⟩ := Group.IsNilpotent.nilpotent ↥H
  refine ⟨n, Subgroup.upperCentralSeries ↥H, Subgroup.upperCentralSeries_zero ↥H, hn,
    Subgroup.upperCentralSeries_mono ↥H, fun i => inferInstance, fun i => ?_⟩
  rw [commutator_comm]
  exact Subgroup.commutator_upperCentralSeries_top_le ↥H i

end CFSG.FeitThompson
