module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeLin
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeMat
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
import all CFSG.Fischer.F4
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.Fischer
open scoped IsMulCommutative

section General

variable {X : Type*} [Group X] {E : Type*} [AddCommGroup E]

theorem addMonoidEnd_apply_inv_apply (ρ : X →* AddMonoid.End E) (x : X) (e : E) :
    ρ x (ρ x⁻¹ e) = e := by
  rw [← addMonoidEnd_mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem addMonoidEnd_inv_apply_apply (ρ : X →* AddMonoid.End E) (x : X) (e : E) :
    ρ x⁻¹ (ρ x e) = e := by
  rw [← addMonoidEnd_mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem card_fixed_eq_of_mul_eq (ρ : X →* AddMonoid.End E) {P x y : X} (h : P * x = y * P) :
    Nat.card {e : E // ρ y e = e} = Nat.card {e : E // ρ x e = e} := by
  have hxy : x = P⁻¹ * y * P := by rw [mul_assoc, ← h]; group
  refine Nat.card_congr
    { toFun := fun e => ⟨ρ P⁻¹ e, ?_⟩
      invFun := fun e => ⟨ρ P e, ?_⟩
      left_inv := fun e => Subtype.ext (addMonoidEnd_apply_inv_apply ρ P e)
      right_inv := fun e => Subtype.ext (addMonoidEnd_inv_apply_apply ρ P e) }
  · rw [hxy, map_mul, map_mul, addMonoidEnd_mul_apply, addMonoidEnd_mul_apply,
      addMonoidEnd_apply_inv_apply, e.2]
  · rw [← addMonoidEnd_mul_apply, ← map_mul, ← h, map_mul, addMonoidEnd_mul_apply, e.2]

theorem eq_zero_of_mul_eq (ρ : X →* AddMonoid.End E) {P x y : X} (h : P * x = y * P)
    (hx : ∀ e, ρ x e = e → e = 0) (e : E) (he : ρ y e = e) : e = 0 := by
  have h1 : ρ x (ρ P⁻¹ e) = ρ P⁻¹ e := by
    have hxy : x = P⁻¹ * y * P := by rw [mul_assoc, ← h]; group
    rw [hxy, map_mul, map_mul, addMonoidEnd_mul_apply, addMonoidEnd_mul_apply,
      addMonoidEnd_apply_inv_apply, he]
  have h2 := hx _ h1
  rw [← addMonoidEnd_apply_inv_apply ρ P e, h2, map_zero]

theorem card_fixed_inv (ρ : X →* AddMonoid.End E) (x : X) :
    Nat.card {e : E // ρ x⁻¹ e = e} = Nat.card {e : E // ρ x e = e} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun e => ?_)
  constructor
  · intro h
    calc ρ x e = ρ x (ρ x⁻¹ e) := by rw [h]
      _ = e := addMonoidEnd_apply_inv_apply ρ x e
  · intro h
    calc ρ x⁻¹ e = ρ x⁻¹ (ρ x e) := by rw [h]
      _ = e := addMonoidEnd_inv_apply_apply ρ x e

theorem injective_sub_one_of_fixed (f : AddMonoid.End E) (hf : ∀ e, f e = e → e = 0) :
    Function.Injective ⇑(f - 1 : AddMonoid.End E) := by
  intro a b hab
  rw [addMonoidEnd_sub_one_apply, addMonoidEnd_sub_one_apply] at hab
  have h : f (a - b) = a - b := by
    rw [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.1 hab
  exact sub_eq_zero.1 (hf _ h)

theorem apply_eq_of_isPerfect_of_card_le_four (ρ : X →* AddMonoid.End E) {Q : Subgroup X}
    (hQ : ⁅Q, Q⁆ = Q) (A : AddSubgroup E) [Finite A] (hA : Nat.card A ≤ 4)
    (hQA : ∀ q ∈ Q, ∀ a ∈ A, ρ q a ∈ A) : ∀ q ∈ Q, ∀ a ∈ A, ρ q a = a := by
  let φ : Q →* Equiv.Perm A :=
    { toFun := fun q =>
        { toFun := fun a => ⟨ρ q a, hQA _ q.2 _ a.2⟩
          invFun := fun a => ⟨ρ (q : X)⁻¹ a, hQA _ (Q.inv_mem q.2) _ a.2⟩
          left_inv := fun a => Subtype.ext (addMonoidEnd_inv_apply_apply ρ q a)
          right_inv := fun a => Subtype.ext (addMonoidEnd_apply_inv_apply ρ q a) }
      map_one' := by
        ext a
        simp only [OneMemClass.coe_one, map_one, Equiv.coe_fn_mk, Equiv.Perm.coe_one, id_eq]
        rfl
      map_mul' := fun q r => by
        ext a
        simp only [Subgroup.coe_mul, map_mul, Equiv.coe_fn_mk, Equiv.Perm.coe_mul,
          Function.comp_apply]
        rfl }
  have htop : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = (⊤ : Subgroup Q) := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hQ]
  set H := φ.range with hHdef
  have hH : ⁅H, H⁆ = H := by
    rw [hHdef, MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  obtain ⟨n, hn⟩ := (Equiv.Perm.isSolvable (α := A) hA).solvable
  have hle : ∀ k, H ≤ derivedSeries (Equiv.Perm A) k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      rw [derivedSeries_succ, ← hH]
      exact Subgroup.commutator_mono ih ih
  have hbot : H = ⊥ := eq_bot_iff.2 (hn ▸ hle n)
  intro q hq a ha
  have h1 : φ ⟨q, hq⟩ = 1 := by
    have h : φ ⟨q, hq⟩ ∈ H := ⟨⟨q, hq⟩, rfl⟩
    rw [hbot] at h
    exact h
  have h2 := congrArg (fun p : Equiv.Perm A => ((p ⟨a, ha⟩ : A) : E)) h1
  exact h2

@[expose] def fixAddSubgroup (f : AddMonoid.End E) : AddSubgroup E where
  carrier := {e | f e = e}
  add_mem' := fun {a b} ha hb => by
    have ha' : f a = a := ha
    have hb' : f b = b := hb
    change f (a + b) = a + b
    rw [map_add, ha', hb']
  zero_mem' := map_zero f
  neg_mem' := fun {a} ha => by
    have ha' : f a = a := ha
    change f (-a) = -a
    rw [map_neg, ha']

end General

section OmegaRing

variable {R : Type*} [Ring R]

theorem omega_ring_identities {a b : R} (hab : a * b = b * a) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hZ : a * b * (a * b) + a * b + 1 = 0) (h2 : (2 : R) = 0) :
    (1 + a * a + b * (1 + a + a * a)) * (1 + a * a + b * (1 + a + a * a)) +
        (1 + a * a + b * (1 + a + a * a)) + 1 = 0 ∧
      1 + a * a + b * (1 + a + a * a) = 1 + b * b + a * (1 + b + b * b) ∧
      1 + a * a * (a * a) + b * b * (1 + a * a + a * a * (a * a)) =
        (1 + a * a + b * (1 + a + a * a)) * (1 + a * a + b * (1 + a + a * a)) ∧
      a * (1 + a + a * a) = 1 + a + a * a ∧ b * (1 + b + b * b) = 1 + b + b * b := by
  obtain ⟨S, hS, haS, hbS⟩ := exists_isMulCommutative_subring_pair hab
  let a' : S := ⟨a, haS⟩
  let b' : S := ⟨b, hbS⟩
  have ha' : a' ^ 3 = 1 := Subtype.ext (by simp [a', ha])
  have hb' : b' ^ 3 = 1 := Subtype.ext (by simp [b', hb])
  have hZ' : a' * b' * (a' * b') + a' * b' + 1 = 0 := Subtype.ext (by simp [a', b', hZ])
  have h2' : (2 : S) = 0 := Subtype.ext (by push_cast; exact h2)
  have hN : (1 + a' + a' * a') * (1 + b' + b' * b') = 0 := by
    linear_combination (1 + b' + b' * b') * hZ' + (-a' ^ 2 * b' - a' ^ 2 - a') * hb'
  have e1 : (1 + a' * a' + b' * (1 + a' + a' * a')) * (1 + a' * a' + b' * (1 + a' + a' * a')) +
      (1 + a' * a' + b' * (1 + a' + a' * a')) + 1 = 0 := by
    linear_combination (a' * b' ^ 2 + a') * ha' + hN +
      (a' ^ 4 * b' + a' ^ 3 * b' ^ 2 + a' ^ 3 * b' + a' ^ 2 * b' ^ 2 + 2 * a' ^ 2 * b' + a' ^ 2 +
        a' * b' ^ 2 + a' * b' + b' + 1) * h2'
  have e2 : 1 + a' * a' + b' * (1 + a' + a' * a') = 1 + b' * b' + a' * (1 + b' + b' * b') := by
    linear_combination hN - hZ' + (-a' * b' ^ 2 - a' - b' ^ 2) * h2'
  have e3 : 1 + a' * a' * (a' * a') + b' * b' * (1 + a' * a' + a' * a' * (a' * a')) =
      (1 + a' * a' + b' * (1 + a' + a' * a')) * (1 + a' * a' + b' * (1 + a' + a' * a')) := by
    linear_combination (-a' ^ 4 * b' - a' ^ 3 * b' ^ 2 - a' ^ 3 * b' - a' ^ 2 * b' ^ 2 -
      2 * a' ^ 2 * b' - a' ^ 2 - a' * b' ^ 2 - a' * b' - b') * h2'
  have e4 : a' * (1 + a' + a' * a') = 1 + a' + a' * a' := by linear_combination ha'
  have e5 : b' * (1 + b' + b' * b') = 1 + b' + b' * b' := by linear_combination hb'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [a', b'] using congrArg Subtype.val e1
  · simpa [a', b'] using congrArg Subtype.val e2
  · simpa [a', b'] using congrArg Subtype.val e3
  · simpa [a', b'] using congrArg Subtype.val e4
  · simpa [a', b'] using congrArg Subtype.val e5

end OmegaRing

section Blocks

@[expose] def veeFrobHom : F4 →+* F4 where
  toFun x := x * x
  map_one' := by decide
  map_mul' := by decide
  map_zero' := by decide
  map_add' := by decide

@[expose] def veeFrob : SpecialLinearGroup (Fin 4) F4 →* SpecialLinearGroup (Fin 4) F4 :=
  SpecialLinearGroup.map veeFrobHom

theorem veeFrob_veeH1 : veeFrob veeH1 = veeH1 * veeH1 := Subtype.ext (by decide +kernel)

theorem veeFrob_veeH2 : veeFrob veeH2 = veeH2 * veeH2 := Subtype.ext (by decide +kernel)

theorem transvection_mul_veeMatH1 : ∀ i j : Fin 4, ∀ a : F4, i ≠ 3 → j ≠ 3 →
    (1 + single i j a) * veeMatH1 = veeMatH1 * (1 + single i j a) := by
  decide +kernel

theorem transvection_mul_veeMatH2 : ∀ i j : Fin 4, ∀ a : F4, i ≠ 0 → j ≠ 0 →
    (1 + single i j a) * veeMatH2 = veeMatH2 * (1 + single i j a) := by
  decide +kernel

@[expose] def veeBlock (c : Fin 4) : Subgroup (SpecialLinearGroup (Fin 4) F4) :=
  Subgroup.closure {g | ∃ (i j : Fin 4) (hij : i ≠ j) (a : F4), i ≠ c ∧ j ≠ c ∧
    g = SpecialLinearGroup.transvection hij a}

theorem transvection_mem_veeBlock {c i j : Fin 4} (hij : i ≠ j) (a : F4) (hi : i ≠ c)
    (hj : j ≠ c) : SpecialLinearGroup.transvection hij a ∈ veeBlock c :=
  Subgroup.subset_closure ⟨i, j, hij, a, hi, hj, rfl⟩

theorem veeBlock_perfect (c : Fin 4) : ⁅veeBlock c, veeBlock c⁆ = veeBlock c := by
  refine le_antisymm (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂) (Subgroup.inv_mem _ h₁))
      (Subgroup.inv_mem _ h₂)) ?_
  rw [veeBlock, Subgroup.closure_le]
  rintro g ⟨i, j, hij, a, hi, hj, rfl⟩
  obtain ⟨k, hki, hkj, hkc⟩ : ∃ k : Fin 4, k ≠ i ∧ k ≠ j ∧ k ≠ c := by
    revert hi hj hij
    revert i j c
    decide
  have h := SpecialLinearGroup.commutatorElement_transvection hki.symm hkj hij a 1
  rw [mul_one] at h
  rw [← h]
  exact Subgroup.commutator_mem_commutator (transvection_mem_veeBlock _ a hi hkc)
    (transvection_mem_veeBlock _ 1 hkc hj)

theorem veeBlock_three_le : ∀ q ∈ veeBlock 3, q * veeH1 = veeH1 * q := by
  intro q hq
  have hle : veeBlock 3 ≤ Subgroup.centralizer ({veeH1} : Set _) := by
    rw [veeBlock, Subgroup.closure_le]
    rintro g ⟨i, j, hij, a, hi, hj, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (transvection_mul_veeMatH1 i j a hi hj)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hq)

theorem veeBlock_zero_le : ∀ q ∈ veeBlock 0, q * veeH2 = veeH2 * q := by
  intro q hq
  have hle : veeBlock 0 ≤ Subgroup.centralizer ({veeH2} : Set _) := by
    rw [veeBlock, Subgroup.closure_le]
    rintro g ⟨i, j, hij, a, hi, hj, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (transvection_mul_veeMatH2 i j a hi hj)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hq)

theorem diag2n_mul_veeH {i j : Fin 4} (hij : i ≠ j) {c : F4} (hc : c ≠ 0) :
    SpecialLinearGroup.diag2n hij c hc * veeH1 = veeH1 * SpecialLinearGroup.diag2n hij c hc ∧
      SpecialLinearGroup.diag2n hij c hc * veeH2 = veeH2 * SpecialLinearGroup.diag2n hij c hc := by
  have hd : ∀ (g : SpecialLinearGroup (Fin 4) F4) (d : Fin 4 → F4),
      (g : Matrix (Fin 4) (Fin 4) F4) = diagonal d →
        SpecialLinearGroup.diag2n hij c hc * g = g * SpecialLinearGroup.diag2n hij c hc := by
    intro g d hgd
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.diag2n_coe, hgd, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _
  exact ⟨hd _ _ rfl, hd _ _ rfl⟩

end Blocks

end CFSG.SeitzReduction.LinearPilot
