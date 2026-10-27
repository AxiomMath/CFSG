module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.CharP.CharAndCard
public import CFSG.FeitThompson.Foundations.FiniteHomImageOrder
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.Positivity.Finset

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Matrix

section Det

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

theorem range_toGL_eq_ker_det :
    (Matrix.SpecialLinearGroup.toGL (n := n) (R := R)).range =
      (Matrix.GeneralLinearGroup.det (n := n) (R := R)).ker := by
  ext x
  rw [MonoidHom.mem_range, MonoidHom.mem_ker, ← Units.val_inj,
    Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  refine ⟨?_, fun hx => ⟨⟨(x : Matrix n n R), hx⟩, ?_⟩⟩
  · rintro ⟨g, rfl⟩
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact g.2
  · exact Matrix.GeneralLinearGroup.ext fun _ _ => rfl

theorem mem_ker_det_iff {x : GL n R} :
    x ∈ (Matrix.GeneralLinearGroup.det (n := n) (R := R)).ker ↔ (x : Matrix n n R).det = 1 := by
  rw [MonoidHom.mem_ker, ← Units.val_inj, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]

theorem mem_range_toGL_iff {x : GL n R} :
    x ∈ (Matrix.SpecialLinearGroup.toGL (n := n) (R := R)).range ↔
      (x : Matrix n n R).det = 1 := by
  rw [range_toGL_eq_ker_det, mem_ker_det_iff]

end Det

section FiniteField

variable {k : Type*} [Field k] {p f : ℕ}

theorem char_dvd_natCard [CharP k p] : p ∣ Nat.card k := by
  have h : addOrderOf (1 : k) = p := CharP.eq k (CharP.addOrderOf_one k) ‹CharP k p›
  rw [← h]
  exact addOrderOf_dvd_natCard _

theorem not_dvd_natCard_units [Finite k] (hp : p.Prime) [CharP k p] : ¬ p ∣ Nat.card kˣ := by
  rw [Nat.card_units]
  intro h
  have h1 : p ∣ 1 := by
    have := Nat.dvd_sub (char_dvd_natCard (k := k) (p := p)) h
    rwa [Nat.sub_sub_self Nat.card_pos] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem charP_of_natCard_eq_prime_pow [Finite k] (hp : p.Prime) (hq : Nat.card k = p ^ f) :
    CharP k p := by
  have := Fintype.ofFinite k
  have : Fact p.Prime := ⟨hp⟩
  exact charP_of_card_eq_prime_pow (p := p) (f := f) (by rwa [← Nat.card_eq_fintype_card])

end FiniteField

section Main

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k] {p : ℕ}
  {G : Subgroup (GL n k)}

theorem injective_det_comp_subtype
    (hG : G ⊓ (Matrix.SpecialLinearGroup.toGL (n := n) (R := k)).range = ⊥) :
    Function.Injective ((Matrix.GeneralLinearGroup.det (n := n) (R := k)).comp G.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot, ← Subtype.coe_inj]
  have hmem : (x : GL n k) ∈ G ⊓ (Matrix.SpecialLinearGroup.toGL (n := n) (R := k)).range :=
    ⟨x.2, by rw [range_toGL_eq_ker_det]; exact hx⟩
  rw [hG, Subgroup.mem_bot] at hmem
  exact hmem

theorem isMulCommutative_of_inf_specialLinear_eq_bot
    (hG : G ⊓ (Matrix.SpecialLinearGroup.toGL (n := n) (R := k)).range = ⊥) :
    IsMulCommutative G :=
  .of_comm fun a b => injective_det_comp_subtype hG (by simp [mul_comm])

theorem natCard_dvd_natCard_units_of_inf_specialLinear_eq_bot [Finite k]
    (hG : G ⊓ (Matrix.SpecialLinearGroup.toGL (n := n) (R := k)).range = ⊥) :
    Nat.card G ∣ Nat.card kˣ := by
  set φ := (Matrix.GeneralLinearGroup.det (n := n) (R := k)).comp G.subtype
  have h : Nat.card φ.range = Nat.card G :=
    Nat.card_congr (Equiv.ofInjective φ (injective_det_comp_subtype hG)).symm
  rw [← h]
  exact natCard_range_dvd_natCard_codomain φ

theorem not_dvd_natCard_of_inf_specialLinear_eq_bot [Finite k] (hp : p.Prime) [CharP k p]
    (hG : G ⊓ (Matrix.SpecialLinearGroup.toGL (n := n) (R := k)).range = ⊥) :
    ¬ p ∣ Nat.card G :=
  fun h => not_dvd_natCard_units (k := k) hp
    (h.trans (natCard_dvd_natCard_units_of_inf_specialLinear_eq_bot hG))

theorem isMulCommutative_and_not_dvd_of_inf_specialLinear_eq_bot_two [Finite k] {f : ℕ}
    (hp : p.Prime) (_hf : 1 ≤ f) (hq : Nat.card k = p ^ f) {G : Subgroup (GL (Fin 2) k)}
    (hG : G ⊓ (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range = ⊥) :
    IsMulCommutative G ∧ ¬ p ∣ Nat.card G :=
  have : CharP k p := charP_of_natCard_eq_prime_pow hp hq
  ⟨isMulCommutative_of_inf_specialLinear_eq_bot hG,
    not_dvd_natCard_of_inf_specialLinear_eq_bot hp hG⟩

end Main

end

end CFSG.FeitThompson
