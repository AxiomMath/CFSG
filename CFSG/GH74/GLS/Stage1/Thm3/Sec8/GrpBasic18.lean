module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

section MulConj

theorem exists_mulConjHom_of_comm {G : Type*} [Group G] {E : Subgroup G} {d : G}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hdN : ∀ e ∈ E, d * e * d⁻¹ ∈ E) :
    ∃ φ : ↥E →* ↥E, ∀ e : ↥E, ((φ e : ↥E) : G) = (e : G) * (d * (e : G) * d⁻¹) := by
  refine ⟨{ toFun := fun e => ⟨(e : G) * (d * (e : G) * d⁻¹), E.mul_mem e.2 (hdN _ e.2)⟩
            map_one' := Subtype.ext (by simp)
            map_mul' := fun a b => Subtype.ext ?_ }, fun e => rfl⟩
  have hx : d * (a : G) * d⁻¹ ∈ E := hdN _ a.2
  have hcomm : (b : G) * (d * (a : G) * d⁻¹) = (d * (a : G) * d⁻¹) * b := hEc _ b.2 _ hx
  show ((a : G) * b) * (d * ((a : G) * b) * d⁻¹) =
    ((a : G) * (d * (a : G) * d⁻¹)) * ((b : G) * (d * (b : G) * d⁻¹))
  calc ((a : G) * b) * (d * ((a : G) * b) * d⁻¹)
      = (a : G) * b * ((d * a * d⁻¹) * (d * b * d⁻¹)) := by group
    _ = (a : G) * (b * (d * a * d⁻¹)) * (d * b * d⁻¹) := by simp only [mul_assoc]
    _ = (a : G) * ((d * a * d⁻¹) * b) * (d * b * d⁻¹) := by rw [hcomm]
    _ = ((a : G) * (d * (a : G) * d⁻¹)) * ((b : G) * (d * (b : G) * d⁻¹)) := by
      simp only [mul_assoc]

theorem exists_mul_conj_eq {G : Type*} [Group G] [Finite G] {E K : Subgroup G} {d k : G}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEs : ∀ a ∈ E, a * a = 1)
    (hdN : ∀ e ∈ E, d * e * d⁻¹ ∈ E) (hd2 : d * d = 1)
    (hK : ∀ e ∈ E, d * e = e * d ↔ e ∈ K) (hKE : K ≤ E)
    (hE : Nat.card ↥E = 16) (hKc : Nat.card ↥K = 4) (hkK : k ∈ K) :
    ∃ e ∈ E, e * (d * e * d⁻¹) = k := by
  obtain ⟨φ, hφ⟩ := exists_mulConjHom_of_comm hEc hdN
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hKcard : Nat.card ↥(K.subgroupOf E) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv).trans hKc
  have hker : φ.ker = K.subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hK e e.2, Subtype.ext_iff, hφ,
      Subgroup.coe_one, mul_eq_one_iff_inv_eq, inv_eq_of_mul_eq_one_right (hEs e e.2), eq_comm,
      ← mul_inv_eq_iff_eq_mul]
  have hrange : φ.range ≤ K.subgroupOf E := by
    rintro _ ⟨e, rfl⟩
    rw [Subgroup.mem_subgroupOf, hφ]
    refine (hK _ (E.mul_mem e.2 (hdN _ e.2))).1 ?_
    have hx : d * (e : G) * d⁻¹ ∈ E := hdN _ e.2
    have hcomm : (e : G) * (d * (e : G) * d⁻¹) = (d * (e : G) * d⁻¹) * e := hEc _ e.2 _ hx
    calc d * ((e : G) * (d * e * d⁻¹)) = d * ((d * e * d⁻¹) * e) := by rw [hcomm]
      _ = ((d * d) * e * d⁻¹) * e := by simp only [mul_assoc]
      _ = e * d⁻¹ * e := by rw [hd2, one_mul]
      _ = e * d * e := by rw [hdinv]
      _ = ((e : G) * (d * e * d⁻¹)) * d := by group
  have hmul : Nat.card φ.ker * Nat.card φ.range = 16 := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at h1
    rw [h1, hE]
  have hker4 : Nat.card φ.ker = 4 := by rw [hker]; exact hKcard
  have hrange4 : Nat.card φ.range = 4 := by
    rw [hker4] at hmul
    omega
  have hrangeEq : φ.range = K.subgroupOf E :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hrange4, hKcard])
  have hkmem : (⟨k, hKE hkK⟩ : ↥E) ∈ K.subgroupOf E := by
    rw [Subgroup.mem_subgroupOf]
    exact hkK
  rw [← hrangeEq] at hkmem
  obtain ⟨e, he⟩ := hkmem
  refine ⟨e, e.2, ?_⟩
  have h1 := congrArg Subtype.val he
  rwa [hφ] at h1

end MulConj

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
