module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Weights16Core
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.OddStandard.Seitz77

namespace Nat16

open Matrix MatrixGroups

variable {F : Type*} [Field F]

@[expose] def uE (c : F) : SL(2, F) := ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lE (c : F) : SL(2, F) := ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def tE (a : F) (ha : a ≠ 0) : SL(2, F) :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, ha]⟩

@[expose] def wE [CharP F 2] : SL(2, F) :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

theorem sl_eq {A B : SL(2, F)} (h : (A : Matrix (Fin 2) (Fin 2) F) = B) : A = B := Subtype.ext h

theorem sl_coe_mul (A B : SL(2, F)) :
    ((A * B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = A * B := rfl

theorem uE_zero : (uE 0 : SL(2, F)) = 1 := by
  apply sl_eq
  show (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) = 1
  exact Matrix.one_fin_two.symm

theorem uE_add (c c' : F) : uE (c + c') = uE c * uE c' := by
  apply sl_eq
  rw [sl_coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uE, Matrix.mul_apply, add_comm]

theorem tE_mul_uE (a : F) (ha : a ≠ 0) (c : F) :
    tE a ha * uE c = uE (a * a * c) * tE a ha := by
  apply sl_eq
  rw [sl_coe_mul, sl_coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tE, uE, Matrix.mul_apply]
  field_simp

theorem tE_mul (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    tE a ha * tE b hb = tE (a * b) (mul_ne_zero ha hb) := by
  apply sl_eq
  rw [sl_coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tE, Matrix.mul_apply, mul_comm]

theorem tE_one : tE (1 : F) one_ne_zero = 1 := by
  apply sl_eq
  show (!![1, 0; 0, 1⁻¹] : Matrix (Fin 2) (Fin 2) F) = 1
  rw [inv_one]
  exact Matrix.one_fin_two.symm

theorem tE_congr {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (h : a = b) : tE a ha = tE b hb := by
  subst h
  rfl

theorem tE_pow (a : F) (ha : a ≠ 0) (n : ℕ) :
    tE a ha ^ n = tE (a ^ n) (pow_ne_zero n ha) := by
  induction n with
  | zero => simp [tE_one]
  | succ n ih => rw [pow_succ, ih, tE_mul]; exact tE_congr _ _ (pow_succ a n).symm

theorem wE_mul_wE [CharP F 2] : (wE : SL(2, F)) * wE = 1 := by
  apply sl_eq
  rw [sl_coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wE, Matrix.mul_apply]

theorem wE_mul_tE [CharP F 2] (a : F) (ha : a ≠ 0) :
    (wE : SL(2, F)) * tE a ha = tE a⁻¹ (inv_ne_zero ha) * wE := by
  apply sl_eq
  rw [sl_coe_mul, sl_coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wE, tE, Matrix.mul_apply]

theorem wE_mul_uE_mul_wE [CharP F 2] (c : F) : (wE : SL(2, F)) * uE c * wE = lE c := by
  apply sl_eq
  rw [sl_coe_mul, sl_coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wE, uE, lE, Matrix.mul_apply]

theorem uE_mul_lE_mul_uE [CharP F 2] : uE (1 : F) * lE 1 * uE 1 = wE := by
  apply sl_eq
  rw [sl_coe_mul, sl_coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wE, uE, lE, Matrix.mul_apply] <;>
    exact CharTwo.add_self_eq_zero 1


theorem uE_ne_one {c : F} (hc : c ≠ 0) : uE c ≠ 1 := by
  intro h
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [uE] at this
  exact hc this

theorem uE_injective : Function.Injective (uE : F → SL(2, F)) := by
  intro c c' h
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [uE] using this

theorem det_entries (g : SL(2, F)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have := g.2
  rwa [Matrix.det_fin_two] at this

theorem eq_uE_mul_lE_mul_uE (g : SL(2, F)) (hc : g 1 0 ≠ 0) :
    g = uE ((g 0 0 - 1) / g 1 0) * lE (g 1 0) * uE ((g 1 1 - 1) / g 1 0) := by
  have hdet := det_entries g
  apply sl_eq
  rw [sl_coe_mul, sl_coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uE, lE, Matrix.mul_apply]
  · field_simp
    ring
  · field_simp
    linear_combination (-1 : F) * hdet
  · field_simp
    ring

theorem closure_uE_wE [CharP F 2] :
    Subgroup.closure (Set.range (uE : F → SL(2, F)) ∪ {wE}) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  set S := Subgroup.closure (Set.range (uE : F → SL(2, F)) ∪ {wE}) with hS
  have hu : ∀ c : F, uE c ∈ S := fun c => Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
  have hw : (wE : SL(2, F)) ∈ S := Subgroup.subset_closure (Or.inr rfl)
  have hl : ∀ c : F, lE c ∈ S := fun c => by
    rw [← wE_mul_uE_mul_wE]
    exact S.mul_mem (S.mul_mem hw (hu c)) hw
  have key : ∀ g : SL(2, F), g 1 0 ≠ 0 → g ∈ S := by
    intro g hc
    rw [eq_uE_mul_lE_mul_uE g hc]
    exact S.mul_mem (S.mul_mem (hu _) (hl _)) (hu _)
  by_cases hc : g 1 0 = 0
  · have hdet := det_entries g
    rw [hc, mul_zero, sub_zero] at hdet
    have hg11 : g 1 1 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hdet
      exact zero_ne_one hdet
    have h1 : g * lE 1 ∈ S := by
      apply key
      rw [sl_coe_mul]
      simpa [lE, Matrix.mul_apply, hc] using hg11
    have : g = (g * lE 1) * (lE 1)⁻¹ := by group
    rw [this]
    exact S.mul_mem h1 (S.inv_mem (hl 1))
  · exact key g hc


@[expose] def natAct (g : SL(2, F)) : AddMonoid.End (F × F) :=
  AddMonoidHom.mk' (fun v => (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 * v.2))
    (fun v w => by ext <;> simp <;> ring)

theorem natAct_apply (g : SL(2, F)) (v : F × F) :
    natAct g v = (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 * v.2) := rfl

@[expose] def natHom : SL(2, F) →* AddMonoid.End (F × F) where
  toFun := natAct
  map_one' := by
    ext v <;> simp [natAct_apply]
  map_mul' g g' := by
    ext v <;> simp [natAct_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem natHom_apply (g : SL(2, F)) (v : F × F) :
    natHom g v = (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 * v.2) := rfl

@[simp] theorem natHom_uE (c : F) (v : F × F) : natHom (uE c) v = (v.1 + c * v.2, v.2) := by
  rw [natHom_apply]
  simp [uE]

@[simp] theorem natHom_tE (a : F) (ha : a ≠ 0) (v : F × F) :
    natHom (tE a ha) v = (a * v.1, a⁻¹ * v.2) := by
  rw [natHom_apply]
  simp [tE]

@[simp] theorem natHom_wE [CharP F 2] (v : F × F) : natHom (wE : SL(2, F)) v = (v.2, v.1) := by
  rw [natHom_apply]
  simp [wE]


end Nat16

end CFSG.OddStandard.Seitz77
