module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup
open scoped commutatorElement

theorem commutatorElement_mul_of_commute {A : Type*} [Group A] {x y z : A} (hzy : z * y = y * z) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  simp only [commutatorElement_def]
  calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [hzy]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutatorElement_of_commute_mul {A : Type*} [Group A] {x y z : A} (hxz : x * z = z * x) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  simp only [commutatorElement_def]
  have h2 : z * x⁻¹ = x⁻¹ * z := by
    calc z * x⁻¹ = x⁻¹ * (x * z) * x⁻¹ := by group
      _ = x⁻¹ * (z * x) * x⁻¹ := by rw [hxz]
      _ = x⁻¹ * z := by group
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [h2]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutatorElement_mul_mul {A : Type*} [Group A] {P Q : Subgroup A}
    (hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) {p p' q q' : A} (hp : p ∈ P) (hp' : p' ∈ P)
    (hq : q ∈ Q) (hq' : q' ∈ Q) : ⁅p * q, p' * q'⁆ = ⁅p, p'⁆ * ⁅q, q'⁆ := by
  have e1 : q * p' = p' * q := (hPQ p' hp' q hq).symm
  have e2 : (q * q' * q⁻¹) * p⁻¹ = p⁻¹ * (q * q' * q⁻¹) :=
    (hPQ p⁻¹ (P.inv_mem hp) _ (Q.mul_mem (Q.mul_mem hq hq') (Q.inv_mem hq))).symm
  have e3 : (q * q' * q⁻¹ * q'⁻¹) * p'⁻¹ = p'⁻¹ * (q * q' * q⁻¹ * q'⁻¹) :=
    (hPQ p'⁻¹ (P.inv_mem hp') _
      (Q.mul_mem (Q.mul_mem (Q.mul_mem hq hq') (Q.inv_mem hq)) (Q.inv_mem hq'))).symm
  simp only [commutatorElement_def]
  calc p * q * (p' * q') * (p * q)⁻¹ * (p' * q')⁻¹
      = p * (q * p') * q' * q⁻¹ * p⁻¹ * q'⁻¹ * p'⁻¹ := by group
    _ = p * (p' * q) * q' * q⁻¹ * p⁻¹ * q'⁻¹ * p'⁻¹ := by rw [e1]
    _ = p * p' * ((q * q' * q⁻¹) * p⁻¹) * q'⁻¹ * p'⁻¹ := by group
    _ = p * p' * (p⁻¹ * (q * q' * q⁻¹)) * q'⁻¹ * p'⁻¹ := by rw [e2]
    _ = p * p' * p⁻¹ * ((q * q' * q⁻¹ * q'⁻¹) * p'⁻¹) := by group
    _ = p * p' * p⁻¹ * (p'⁻¹ * (q * q' * q⁻¹ * q'⁻¹)) := by rw [e3]
    _ = p * p' * p⁻¹ * p'⁻¹ * (q * q' * q⁻¹ * q'⁻¹) := by group

theorem commutator_self_le {A : Type*} [Group A] (S : Subgroup A) : ⁅S, S⁆ ≤ S := by
  refine commutator_le.2 fun a ha b hb => ?_
  simp only [commutatorElement_def]
  exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)

theorem normal_commutator_subgroupOf {A : Type*} [Group A] (S : Subgroup A) :
    (⁅S, S⁆.subgroupOf S).Normal := by
  have h : (⁅S, S⁆.subgroupOf S) = _root_.commutator ↥S := by
    apply Subgroup.map_injective S.subtype_injective
    rw [map_subgroupOf_eq_of_le (commutator_self_le S), map_subtype_commutator]
  rw [h]
  infer_instance

section CentralCover

variable {A B : Type*} [Group A] [Group B] (f : A →* B)

@[expose] def ccLift (Q : Subgroup B) : Subgroup A := ⁅Q.comap f, Q.comap f⁆

theorem ccLift_le_comap (Q : Subgroup B) : ccLift f Q ≤ Q.comap f :=
  commutator_self_le _

theorem map_ccLift {Q : Subgroup B} (hQ : ⁅Q, Q⁆ = Q) (hQr : Q ≤ f.range) :
    (ccLift f Q).map f = Q := by
  unfold ccLift
  rw [map_commutator, map_comap_eq, inf_eq_right.2 hQr, hQ]

variable {f}

theorem exists_mul_ker_of_mem_comap {Q : Subgroup B} (hQ : ⁅Q, Q⁆ = Q) (hQr : Q ≤ f.range)
    {x : A} (hx : x ∈ Q.comap f) : ∃ l ∈ ccLift f Q, ∃ z ∈ f.ker, x = l * z := by
  have hmem : f x ∈ (ccLift f Q).map f := by rw [map_ccLift f hQ hQr]; exact hx
  obtain ⟨l, hl, hlx⟩ := hmem
  refine ⟨l, hl, l⁻¹ * x, ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hlx, inv_mul_cancel]

theorem commutator_ccLift_eq (hker : f.ker ≤ center A) {Q : Subgroup B} (hQ : ⁅Q, Q⁆ = Q)
    (hQr : Q ≤ f.range) : ⁅ccLift f Q, ccLift f Q⁆ = ccLift f Q := by
  refine le_antisymm (commutator_self_le _) ?_
  refine commutator_le.2 fun a ha b hb => ?_
  obtain ⟨l, hl, z, hz, rfl⟩ := exists_mul_ker_of_mem_comap hQ hQr ha
  obtain ⟨l', hl', z', hz', rfl⟩ := exists_mul_ker_of_mem_comap hQ hQr hb
  rw [commutatorElement_mul_of_commute (mem_center_iff.1 (hker hz) _).symm,
    commutatorElement_of_commute_mul (mem_center_iff.1 (hker hz') _)]
  exact commutator_mem_commutator hl hl'

theorem le_of_map_le_of_perfect (hker : f.ker ≤ center A) {P P' : Subgroup A} (hP : ⁅P, P⁆ = P)
    (hP' : ⁅P', P'⁆ = P') (h : P.map f ≤ P'.map f) : P ≤ P' := by
  have key : ∀ a ∈ P, ∃ a' ∈ P', ∃ z ∈ f.ker, a = a' * z := by
    intro a ha
    obtain ⟨a', ha', haa⟩ := h ⟨a, ha, rfl⟩
    refine ⟨a', ha', a'⁻¹ * a, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, haa, inv_mul_cancel]
  refine le_trans (le_of_eq hP.symm) (commutator_le.2 fun a ha b hb => ?_)
  obtain ⟨a', ha', z, hz, rfl⟩ := key a ha
  obtain ⟨b', hb', w, hw, rfl⟩ := key b hb
  rw [commutatorElement_mul_of_commute (mem_center_iff.1 (hker hz) _).symm,
    commutatorElement_of_commute_mul (mem_center_iff.1 (hker hw) _)]
  have := commutator_mem_commutator ha' hb'
  rwa [hP'] at this

end CentralCover

end CFSG.EvenSporadicStandard.Induction.Junction
