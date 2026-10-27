module

public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaQ

open Subgroup

variable {G : Type*} [Group G]

theorem normal_subgroupOf_of_le_normalizer {N X : Subgroup G}
    (h : X ≤ normalizer (N : Set G)) : (N.subgroupOf X).Normal :=
  ⟨fun n hn x => by
    rw [mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.mp (h x.2) n).mp hn⟩

theorem card_sup_mul_card_inf_of_normalizes {X N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) = Nat.card X * Nat.card N := by
  have : (N.subgroupOf (X ⊔ N)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le hXN le_normalizer)
  have : (N.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem card_le_card_mul_card_cent [Finite G] (R : Subgroup G) (t : G) (S : Set G)
    (hS : ∀ r ∈ R, r * t * r⁻¹ ∈ S) :
    Nat.card R ≤ Nat.card S * Nat.card (R ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  classical
  set C : Subgroup R := (R ⊓ centralizer ({t} : Set G)).subgroupOf R with hC
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup C
  have hCc : Nat.card C = Nat.card (R ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    rw [hC, ← Subgroup.card_map_of_injective R.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm, ← inf_assoc, inf_idem]
  have key : ∀ a b : R, a⁻¹ * b ∈ C ↔
      (a : G) * t * (a : G)⁻¹ = (b : G) * t * (b : G)⁻¹ := by
    intro a b
    rw [hC, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · rintro ⟨-, hab⟩
      have hc : ((a : G)⁻¹ * b) * t * ((a : G)⁻¹ * b)⁻¹ = t := by
        rw [hab]; group
      calc (a : G) * t * (a : G)⁻¹
          = (a : G) * (((a : G)⁻¹ * b) * t * ((a : G)⁻¹ * b)⁻¹) * (a : G)⁻¹ := by rw [hc]
        _ = (b : G) * t * (b : G)⁻¹ := by group
    · intro hab
      refine ⟨R.mul_mem (R.inv_mem a.2) b.2, ?_⟩
      calc (a : G)⁻¹ * b * t = (a : G)⁻¹ * ((b : G) * t * (b : G)⁻¹) * b := by group
        _ = (a : G)⁻¹ * ((a : G) * t * (a : G)⁻¹) * b := by rw [hab]
        _ = t * ((a : G)⁻¹ * b) := by group
  let f : R ⧸ C → S := fun q => Quotient.liftOn' q (fun r => ⟨(r : G) * t * (r : G)⁻¹, hS r r.2⟩)
    (fun a b hab => Subtype.ext ((key a b).mp (QuotientGroup.leftRel_apply.mp hab)))
  have hf : Function.Injective f := by
    intro q₁ q₂ hq
    induction q₁ using Quotient.inductionOn' with
    | h a =>
      induction q₂ using Quotient.inductionOn' with
      | h b =>
        apply Quotient.sound'
        exact QuotientGroup.leftRel_apply.mpr ((key a b).mpr (congrArg Subtype.val hq))
  have h1 : Nat.card (R ⧸ C) ≤ Nat.card S := Nat.card_le_card_of_injective f hf
  rw [hcard, hCc]
  exact Nat.mul_le_mul_right _ h1

theorem two_mul_card_le_card_sup [Finite G] {B : Subgroup G} {s : G} (hs : s ∉ B) :
    2 * Nat.card B ≤ Nat.card (B ⊔ zpowers s : Subgroup G) := by
  have hle : B ≤ B ⊔ zpowers s := le_sup_left
  have hdvd := Subgroup.card_dvd_of_le hle
  have hne : Nat.card B ≠ Nat.card (B ⊔ zpowers s : Subgroup G) := by
    intro he
    exact hs ((Subgroup.eq_of_le_of_card_ge hle he.ge) ▸ mem_sup_right (mem_zpowers s))
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < Nat.card B := Nat.card_pos
  rcases k with _ | _ | k
  · simp at hk; exact absurd hk Nat.card_pos.ne'
  · simp at hk; exact absurd hk.symm hne
  · rw [hk]; nlinarith

end CFSG.EvenSmallLie.UnitarySix.YamadaQ
