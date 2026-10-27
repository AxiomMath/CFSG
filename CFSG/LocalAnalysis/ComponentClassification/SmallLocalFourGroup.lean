module

public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import Mathlib.GroupTheory.FixedPointFree
public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.SmallLocal

open Subgroup

variable {H : Type*} [Group H]

theorem odd_card_oddCore [Finite H] : Odd (Nat.card (oddCore H)) := by
  have h := LocalCores.piCore_isPiSubgroup (G := H) {q : Nat.Primes | q.val ≠ 2}
  rw [← oddCore_eq_piCore] at h
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  exact fun h2 => h ⟨2, Nat.prime_two⟩ h2 rfl

theorem le_oddCore_of_normal_odd {N : Subgroup H} (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N ≤ oddCore H :=
  le_sSup ⟨hN, hodd⟩

theorem eq_one_of_mem_oddCore_of_conj_eq [Finite H] {c : H}
    (hc : oddCore (centralizer ({c} : Set H)) = ⊥) {r : H} (hr : r ∈ oddCore H)
    (hrc : c * r * c⁻¹ = r) : r = 1 := by
  set C := centralizer ({c} : Set H)
  have hrC : r ∈ C := by
    rw [mem_centralizer_singleton_iff]
    calc r * c = c * r * c⁻¹ * c := by rw [hrc]
      _ = c * r := by group
  have hdvd : Nat.card ((oddCore H).subgroupOf C) ∣ Nat.card (oddCore H) := by
    rw [← card_map_of_injective C.subtype_injective, subgroupOf_map_subtype]
    exact card_dvd_of_le inf_le_left
  have hle : (oddCore H).subgroupOf C ≤ oddCore C :=
    le_oddCore_of_normal_odd (Normal.subgroupOf inferInstance C) (odd_card_oddCore.of_dvd_nat hdvd)
  have hmem : (⟨r, hrC⟩ : C) ∈ oddCore C := hle (mem_subgroupOf.mpr hr)
  rw [hc, mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem conj_eq_inv_of_oddCore_centralizer_eq_bot [Finite H] {c : H} (hc2 : c ^ 2 = 1)
    (hc : oddCore (centralizer ({c} : Set H)) = ⊥) {r : H} (hr : r ∈ oddCore H) :
    c * r * c⁻¹ = r⁻¹ := by
  let φ : oddCore H →* oddCore H := (MulAut.conjNormal c).toMonoidHom
  have hφ : ∀ x : oddCore H, (φ x : H) = c * x * c⁻¹ := fun x => MulAut.conjNormal_apply c x
  have hfree : MonoidHom.FixedPointFree φ := fun x hx => by
    apply Subtype.ext
    exact eq_one_of_mem_oddCore_of_conj_eq hc x.2 (by rw [← hφ, hx])
  have hcc : c * c = 1 := by rw [← pow_two]; exact hc2
  have hinv : Function.Involutive φ := fun x => by
    apply Subtype.ext
    rw [hφ, hφ]
    calc c * (c * (x : H) * c⁻¹) * c⁻¹ = c * c * x * (c⁻¹ * c⁻¹) := by simp only [mul_assoc]
      _ = x := by rw [hcc, ← mul_inv_rev, hcc, inv_one, one_mul, mul_one]
  have := congrArg (fun f => ((f ⟨r, hr⟩ : oddCore H) : H)) (hfree.coe_eq_inv_of_involutive hinv)
  simpa [hφ] using this

theorem oddCore_eq_bot_of_involution_pair [Finite H] {a b : H} (ha2 : a ^ 2 = 1)
    (hb2 : b ^ 2 = 1) (ha : oddCore (centralizer ({a} : Set H)) = ⊥)
    (hb : oddCore (centralizer ({b} : Set H)) = ⊥)
    (hab : oddCore (centralizer ({a * b} : Set H)) = ⊥) : oddCore H = ⊥ := by
  refine (eq_bot_iff_forall _).mpr fun r hr => eq_one_of_mem_oddCore_of_conj_eq hab hr ?_
  have hbr : b * r * b⁻¹ = r⁻¹ := conj_eq_inv_of_oddCore_centralizer_eq_bot hb2 hb hr
  have har : a * r⁻¹ * a⁻¹ = r :=
    (conj_eq_inv_of_oddCore_centralizer_eq_bot ha2 ha (inv_mem hr)).trans (inv_inv r)
  calc a * b * r * (a * b)⁻¹ = a * (b * r * b⁻¹) * a⁻¹ := by group
    _ = r := by rw [hbr, har]

theorem four_group_local_centralizer_odd_core_vanishing [Finite H] (A : Subgroup H)
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4)
    (hcore : ∀ a ∈ A, a ≠ 1 → oddCore (centralizer ({a} : Set H)) = ⊥) :
    oddCore H = ⊥ := by
  classical
  have hsq : ∀ x ∈ A, x ^ 2 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have : Fintype A := Fintype.ofFinite A
  have hcard : (Finset.univ : Finset A).card = 4 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hA]
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1} : Finset A)) (t := Finset.univ) (by rw [hcard, Finset.card_singleton]; omega)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, a} : Finset A)) (t := Finset.univ)
    (by have := Finset.card_insert_le (1 : A) {a}; rw [hcard]; simp at this ⊢; omega)
  simp only [Finset.mem_singleton] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  have ha1 : (a : H) ≠ 1 := fun h => ha (Subtype.ext h)
  have hb1 : (b : H) ≠ 1 := fun h => hb.1 (Subtype.ext h)
  have hab1 : (a : H) * b ≠ 1 := by
    intro h
    have hinv : (b : H) = (a : H)⁻¹ := eq_inv_of_mul_eq_one_right h
    have ha' : (a : H)⁻¹ = a := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two]
      exact hsq a a.2
    exact hb.2 (Subtype.ext (hinv.trans ha'))
  exact oddCore_eq_bot_of_involution_pair (hsq a a.2) (hsq b b.2) (hcore a a.2 ha1)
    (hcore b b.2 hb1) (hcore _ (mul_mem a.2 b.2) hab1)

end CFSG.ComponentClassification.SmallLocal
