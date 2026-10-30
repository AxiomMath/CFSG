module

public import CFSG.Open.StatedDefs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.GH74.QTGen4.Leaves.F112

open Matrix

variable {F : Type} [Field F]

theorem exists_omega (hF : Nat.card F = 4) : ∃ ω : F, ω ^ 2 = ω + 1 ∧ (2 : F) = 0 := by
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = 2 ^ 2 := by rw [← Nat.card_eq_fintype_card, hF]; norm_num
  have hp : CharP F 2 := charP_of_card_eq_prime_pow hc
  have h2 : (2 : F) = 0 := by
    have := hp.cast_eq_zero
    exact_mod_cast this
  have hu : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, hF]
  obtain ⟨g, hg⟩ := (IsCyclic.exists_generator : ∃ g : Fˣ, ∀ x, x ∈ Subgroup.zpowers g)
  have hord : orderOf g = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hu]
  have hg3 : g ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h; rw [h, orderOf_one] at hord; omega
  refine ⟨(g : F), ?_, h2⟩
  have e1 : ((g : F)) ^ 3 = 1 := by simpa using congrArg Units.val hg3
  have e2 : (g : F) ≠ 1 := fun h => hg1 (Units.ext h)
  have e3 : ((g : F) - 1) * ((g : F) ^ 2 + (g : F) + 1) = 0 := by linear_combination e1
  have e4 : (g : F) - 1 ≠ 0 := sub_ne_zero.mpr e2
  have e5 : (g : F) ^ 2 + (g : F) + 1 = 0 := by
    rcases mul_eq_zero.mp e3 with h | h
    · exact absurd h e4
    · exact h
  linear_combination e5 - ((g : F) + 1) * h2

section Mats

variable (ω : F)

def mS : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
def mD : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]
def mP : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
def mF : Matrix (Fin 3) (Fin 3) F := !![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω]
def mG : Matrix (Fin 3) (Fin 3) F := !![1, ω ^ 2, ω ^ 2; ω, ω, ω ^ 2; ω, ω ^ 2, ω]

variable {ω}

section Rel

variable (hω : ω ^ 2 = ω + 1) (h2 : (2 : F) = 0)

include hω h2 in
theorem mat_F_S : mF ω * mS = mD ω * mF ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mF, mS, mD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω h2 in
theorem mat_F_D : mF ω * mD ω = (mS * mS) * mF ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mF, mS, mD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem mat_P_S : (mP : Matrix (Fin 3) (Fin 3) F) * mS = (mS * mS) * mP := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mP, mS, Matrix.mul_apply, Fin.sum_univ_three]

include hω h2 in
theorem mat_P_D : mP * mD ω = (mD ω * mD ω) * mP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mP, mD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω h2 in
theorem mat_S_D : mS * mD ω = (ω ^ 2) • (mD ω * mS) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mS, mD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω h2 in
theorem mat_G_S : mG ω * mS = (ω ^ 2) • ((mS * mS * (mD ω * mD ω)) * mG ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mG, mS, mD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include hω h2 in
theorem mat_G_D : mG ω * mD ω = ω • ((mS * mS * mD ω) * mG ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mG, mS, mD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem det_S : (mS : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [mS, Matrix.det_fin_three]
include hω h2 in
theorem det_P : (mP : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [mP, Matrix.det_fin_three]; grind
include hω h2 in
theorem det_D : (mD ω).det = 1 := by
  simp [mD, Matrix.det_fin_three]; grind
include hω h2 in
theorem det_F : (mF ω).det = 1 := by
  simp [mF, Matrix.det_fin_three]; grind
include hω h2 in
theorem det_G : (mG ω).det = 1 := by
  simp [mG, Matrix.det_fin_three]; grind

theorem unit_S : (((mS : Matrix (Fin 3) (Fin 3) F)).map (· ^ 2))ᵀ * mS = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mS, Matrix.mul_apply, Fin.sum_univ_three]
theorem unit_P : (((mP : Matrix (Fin 3) (Fin 3) F)).map (· ^ 2))ᵀ * mP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mP, Matrix.mul_apply, Fin.sum_univ_three]
include hω h2 in
theorem unit_D : ((mD ω).map (· ^ 2))ᵀ * mD ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
include hω h2 in
theorem unit_F : ((mF ω).map (· ^ 2))ᵀ * mF ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mF, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
include hω h2 in
theorem unit_G : ((mG ω).map (· ^ 2))ᵀ * mG ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mG, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem S_cube : (mS : Matrix (Fin 3) (Fin 3) F) * mS * mS = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mS, Matrix.mul_apply, Fin.sum_univ_three]
include hω h2 in
theorem D_cube : mD ω * mD ω * mD ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

end Rel

end Mats

section NS

variable {ω : F}

theorem not_scalar (hω : ω ^ 2 = ω + 1) (h2 : (2 : F) = 0) (m n : ℕ) (hm : m < 3) (hn : n < 3)
    (hmn : m ≠ 0 ∨ n ≠ 0) (c : F) : (mS : Matrix (Fin 3) (Fin 3) F) ^ m * mD ω ^ n ≠
      Matrix.scalar (Fin 3) c := by
  intro h
  have e : ∀ i j, ((mS : Matrix (Fin 3) (Fin 3) F) ^ m * mD ω ^ n) i j =
      (Matrix.scalar (Fin 3) c) i j := fun i j => by rw [h]
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  interval_cases m <;> interval_cases n <;> simp at hmn <;>
    simp [pow_succ, mS, mD, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply,
      Matrix.diagonal_apply] at e00 e01 e02 e10 e11 e12 e20 e21 e22 <;> grind

end NS

section Grp

open CFSG.Open

variable (F)

abbrev SUg : Type := ↥(StatedSU 3 2 F)

abbrev Ug : Type := StatedProj (StatedSU 3 2 F)

variable {F}

@[expose] noncomputable def suMk (M : Matrix (Fin 3) (Fin 3) F) (h1 : M.det = 1)
    (h2 : (M.map (· ^ 2))ᵀ * M = 1) : SUg F :=
  ⟨Matrix.GeneralLinearGroup.mk'' M (h1 ▸ isUnit_one), by
    apply Subgroup.subset_closure
    exact ⟨by simpa using h1, by simpa using h2⟩⟩

@[expose] def mat (x : SUg F) : Matrix (Fin 3) (Fin 3) F := ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

@[simp] theorem mat_suMk (M h1 h2) : mat (suMk M h1 h2 : SUg F) = M := rfl

@[simp] theorem val_suMk (M h1 h2) :
    (((suMk M h1 h2 : SUg F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = M := rfl

theorem mat_mul (x y : SUg F) : mat (x * y) = mat x * mat y := rfl

theorem mat_one : mat (1 : SUg F) = 1 := rfl

theorem su_ext {x y : SUg F} (h : mat x = mat y) : x = y := Subtype.ext (Units.ext h)

theorem mat_pow (x : SUg F) (n : ℕ) : mat (x ^ n) = mat x ^ n := by
  induction n with
  | zero => simp [mat_one]
  | succ n ih => rw [pow_succ, mat_mul, ih, pow_succ]

end Grp


section Quot

open CFSG.Open

theorem unit_scalar (c : F) (hc : c ^ 3 = 1) :
    (((Matrix.scalar (Fin 3) c : Matrix (Fin 3) (Fin 3) F)).map (· ^ 2))ᵀ *
      Matrix.scalar (Fin 3) c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal_apply] <;> grind

theorem det_scalar' (c : F) (hc : c ^ 3 = 1) :
    (Matrix.scalar (Fin 3) c : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [Matrix.det_smul, hc]

@[expose] noncomputable def zS (c : F) (hc : c ^ 3 = 1) : SUg F :=
  suMk (Matrix.scalar (Fin 3) c) (det_scalar' c hc) (unit_scalar c hc)

@[expose] noncomputable def piU : SUg F →* Ug F := QuotientGroup.mk' _

theorem piU_zS (c : F) (hc3 : c ^ 3 = 1) : piU (zS c hc3) = 1 := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h] at hc3; norm_num at hc3
  rw [piU, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  simp [zS, Matrix.GeneralLinearGroup.coe_scalar]

theorem piU_eq_of_smul (x y : SUg F) (c : F) (hc3 : c ^ 3 = 1) (h : mat x = c • mat y) :
    piU x = piU y := by
  have hxz : x = zS c hc3 * y := by
    apply su_ext
    rw [mat_mul]
    simp only [zS, mat_suMk, h]
    rw [Matrix.smul_eq_diagonal_mul, Matrix.scalar_apply]
  rw [hxz, map_mul, piU_zS, one_mul]

end Quot


structure OmegaData (F : Type) [Field F] : Type where
  ω : F
  hω : ω ^ 2 = ω + 1
  h2 : (2 : F) = 0

namespace OmegaData

open CFSG.Open

variable (o : OmegaData F)

theorem cube : o.ω ^ 3 = 1 := by have := o.hω; have := o.h2; grind

theorem cube_sq : (o.ω ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, o.cube, one_pow]

@[expose] noncomputable def sS (_o : OmegaData F) : SUg F := suMk mS det_S unit_S
@[expose] noncomputable def sD : SUg F := suMk (mD o.ω) (det_D o.hω o.h2) (unit_D o.hω o.h2)
@[expose] noncomputable def sP : SUg F := suMk mP (det_P o.hω o.h2) unit_P
@[expose] noncomputable def sF : SUg F := suMk (mF o.ω) (det_F o.hω o.h2) (unit_F o.hω o.h2)
@[expose] noncomputable def sG : SUg F := suMk (mG o.ω) (det_G o.hω o.h2) (unit_G o.hω o.h2)

@[expose] noncomputable def ua : Ug F := piU (sS o)
@[expose] noncomputable def ub : Ug F := piU (sD o)
@[expose] noncomputable def up : Ug F := piU (sP o)
@[expose] noncomputable def uf : Ug F := piU (sF o)
@[expose] noncomputable def ug : Ug F := piU (sG o)

theorem sS_cube : sS o ^ 3 = 1 := by
  apply su_ext
  rw [mat_pow, mat_one, pow_three']
  exact S_cube

theorem sD_cube : sD o ^ 3 = 1 := by
  apply su_ext
  rw [mat_pow, mat_one, pow_three']
  exact D_cube o.hω o.h2

theorem ua_cube : ua o ^ 3 = 1 := by
  rw [ua, ← map_pow, sS_cube, map_one]

theorem ub_cube : ub o ^ 3 = 1 := by
  rw [ub, ← map_pow, sD_cube, map_one]

theorem ua_comm : ua o * ub o = ub o * ua o := by
  rw [ua, ub, ← map_mul, ← map_mul]
  apply piU_eq_of_smul _ _ (o.ω ^ 2) o.cube_sq
  exact mat_S_D o.hω o.h2

theorem conj_p_a : up o * ua o * (up o)⁻¹ = ua o ^ 2 := by
  rw [mul_inv_eq_iff_eq_mul, up, ua, ← map_pow, ← map_mul, ← map_mul]
  congr 1
  apply su_ext
  rw [mat_mul, mat_mul, pow_two, mat_mul]
  exact mat_P_S

theorem conj_p_b : up o * ub o * (up o)⁻¹ = ub o ^ 2 := by
  rw [mul_inv_eq_iff_eq_mul, up, ub, ← map_pow, ← map_mul, ← map_mul]
  congr 1
  apply su_ext
  rw [mat_mul, mat_mul, pow_two, mat_mul]
  exact mat_P_D o.hω o.h2

theorem conj_f_a : uf o * ua o * (uf o)⁻¹ = ub o := by
  rw [mul_inv_eq_iff_eq_mul, uf, ua, ub, ← map_mul, ← map_mul]
  congr 1
  apply su_ext
  rw [mat_mul, mat_mul]
  exact mat_F_S o.hω o.h2

theorem conj_f_b : uf o * ub o * (uf o)⁻¹ = ua o ^ 2 := by
  rw [mul_inv_eq_iff_eq_mul, uf, ub, ua, ← map_pow, ← map_mul, ← map_mul]
  congr 1
  apply su_ext
  rw [mat_mul, mat_mul, pow_two, mat_mul]
  exact mat_F_D o.hω o.h2

theorem conj_g_a : ug o * ua o * (ug o)⁻¹ = ua o ^ 2 * ub o ^ 2 := by
  rw [mul_inv_eq_iff_eq_mul, ug, ua, ub, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_mul]
  apply piU_eq_of_smul _ _ (o.ω ^ 2) o.cube_sq
  simp only [mat_mul, mat_pow]
  rw [pow_two (mat (sS o)), pow_two (mat (sD o))]
  exact mat_G_S o.hω o.h2

theorem conj_g_b : ug o * ub o * (ug o)⁻¹ = ua o ^ 2 * ub o := by
  rw [mul_inv_eq_iff_eq_mul, ug, ua, ub, ← map_pow, ← map_mul, ← map_mul, ← map_mul]
  apply piU_eq_of_smul _ _ o.ω o.cube
  simp only [mat_mul, mat_pow]
  rw [pow_two (mat (sS o))]
  exact mat_G_D o.hω o.h2


theorem ua_commute : Commute (ua o) (ub o) := ua_comm o

@[expose] noncomputable def th (x : Multiplicative (ZMod 3 × ZMod 3)) : Ug F :=
  ua o ^ (Multiplicative.toAdd x).1.val * ub o ^ (Multiplicative.toAdd x).2.val

theorem th_mul (x y : Multiplicative (ZMod 3 × ZMod 3)) : th o (x * y) = th o x * th o y := by
  obtain ⟨⟨i, j⟩, rfl⟩ := Multiplicative.ofAdd.surjective x
  obtain ⟨⟨i', j'⟩, rfl⟩ := Multiplicative.ofAdd.surjective y
  rw [← ofAdd_add]
  simp only [th, toAdd_ofAdd, Prod.mk_add_mk, ZMod.val_add]
  have ha : ∀ n : ℕ, ua o ^ (n % 3) = ua o ^ n := fun n => (pow_eq_pow_mod n (ua_cube o)).symm
  have hb : ∀ n : ℕ, ub o ^ (n % 3) = ub o ^ n := fun n => (pow_eq_pow_mod n (ub_cube o)).symm
  rw [ha, hb, pow_add, pow_add]
  have hc : ub o ^ (j.val) * ua o ^ (i'.val) = ua o ^ (i'.val) * ub o ^ (j.val) :=
    ((ua_commute o).pow_pow i'.val j.val).eq.symm
  calc ua o ^ i.val * ua o ^ i'.val * (ub o ^ j.val * ub o ^ j'.val)
      = ua o ^ i.val * (ua o ^ i'.val * ub o ^ j.val) * ub o ^ j'.val := by
        simp only [mul_assoc]
    _ = ua o ^ i.val * (ub o ^ j.val * ua o ^ i'.val) * ub o ^ j'.val := by rw [hc]
    _ = ua o ^ i.val * ub o ^ j.val * (ua o ^ i'.val * ub o ^ j'.val) := by
        simp only [mul_assoc]

@[expose] noncomputable def theta : Multiplicative (ZMod 3 × ZMod 3) →* Ug F :=
  MonoidHom.mk' (th o) (th_mul o)

theorem theta_apply (x : Multiplicative (ZMod 3 × ZMod 3)) :
    theta o x = ua o ^ (Multiplicative.toAdd x).1.val * ub o ^ (Multiplicative.toAdd x).2.val :=
  rfl


theorem theta_injective : Function.Injective (theta o) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨⟨i, j⟩, rfl⟩ := Multiplicative.ofAdd.surjective x
  rw [theta_apply] at hx
  simp only [toAdd_ofAdd] at hx
  by_contra hne
  have hij : i.val ≠ 0 ∨ j.val ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    have hi : i = 0 := (ZMod.val_eq_zero i).mp h.1
    have hj : j = 0 := (ZMod.val_eq_zero j).mp h.2
    subst hi; subst hj
    rfl
  have h1 : piU (sS o ^ i.val * sD o ^ j.val) = 1 := by
    rw [map_mul, map_pow, map_pow]; exact hx
  rw [piU, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  obtain ⟨u, hu⟩ := h1
  have hmat : Matrix.scalar (Fin 3) (u : F) = (mS : Matrix (Fin 3) (Fin 3) F) ^ i.val * mD o.ω ^ j.val := by
    have h3 : mat (sS o ^ i.val * sD o ^ j.val) =
        ((Matrix.GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [hu]; rfl
    rw [mat_mul, mat_pow, mat_pow] at h3
    rw [← Matrix.GeneralLinearGroup.coe_scalar]
    exact h3.symm
  exact not_scalar o.hω o.h2 i.val j.val (ZMod.val_lt i) (ZMod.val_lt j) hij u hmat.symm

theorem val_zero3 : (0 : ZMod 3).val = 0 := rfl
theorem val_one3 : (1 : ZMod 3).val = 1 := rfl
theorem val_two3 : (2 : ZMod 3).val = 2 := rfl

theorem pow_four_a : ua o ^ 4 = ua o := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, ua_cube, one_mul, pow_one]
theorem pow_four_b : ub o ^ 4 = ub o := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, ub_cube, one_mul, pow_one]

theorem conj_to_a (x : Multiplicative (ZMod 3 × ZMod 3)) (hx : x ≠ 1) :
    ∃ h : Ug F, h * ua o * h⁻¹ = theta o x := by
  obtain ⟨⟨i, j⟩, rfl⟩ := Multiplicative.ofAdd.surjective x
  rw [theta_apply]
  simp only [toAdd_ofAdd]
  have hz : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  have hi := hz i
  have hj := hz j
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    simp only [val_zero3, val_one3, val_two3, pow_zero, pow_one, one_mul, mul_one]
  · exact absurd rfl hx
  ·
    exact ⟨uf o, conj_f_a o⟩
  ·
    refine ⟨up o * uf o, ?_⟩
    calc up o * uf o * ua o * (up o * uf o)⁻¹ = up o * (uf o * ua o * (uf o)⁻¹) * (up o)⁻¹ := by
          group
      _ = ub o ^ 2 := by rw [conj_f_a, conj_p_b]
  ·
    exact ⟨1, by simp⟩
  ·
    refine ⟨up o * ug o, ?_⟩
    calc up o * ug o * ua o * (up o * ug o)⁻¹ = up o * (ug o * ua o * (ug o)⁻¹) * (up o)⁻¹ := by
          group
      _ = up o * (ua o ^ 2 * ub o ^ 2) * (up o)⁻¹ := by rw [conj_g_a]
      _ = (up o * ua o * (up o)⁻¹) ^ 2 * (up o * ub o * (up o)⁻¹) ^ 2 := by
          simp only [pow_two]; group
      _ = (ua o ^ 2) ^ 2 * (ub o ^ 2) ^ 2 := by rw [conj_p_a, conj_p_b]
      _ = ua o * ub o := by
        rw [← pow_mul, ← pow_mul, pow_four_a, pow_four_b]
  ·
    refine ⟨up o * ug o * uf o, ?_⟩
    calc up o * ug o * uf o * ua o * (up o * ug o * uf o)⁻¹
        = up o * (ug o * (uf o * ua o * (uf o)⁻¹) * (ug o)⁻¹) * (up o)⁻¹ := by group
      _ = up o * (ua o ^ 2 * ub o) * (up o)⁻¹ := by rw [conj_f_a, conj_g_b]
      _ = (up o * ua o * (up o)⁻¹) ^ 2 * (up o * ub o * (up o)⁻¹) := by
          simp only [pow_two]; group
      _ = (ua o ^ 2) ^ 2 * ub o ^ 2 := by rw [conj_p_a, conj_p_b]
      _ = ua o * ub o ^ 2 := by rw [← pow_mul, pow_four_a]
  ·
    exact ⟨up o, conj_p_a o⟩
  ·
    refine ⟨ug o * uf o, ?_⟩
    calc ug o * uf o * ua o * (ug o * uf o)⁻¹ = ug o * (uf o * ua o * (uf o)⁻¹) * (ug o)⁻¹ := by
          group
      _ = ua o ^ 2 * ub o := by rw [conj_f_a, conj_g_b]
  ·
    exact ⟨ug o, conj_g_a o⟩

theorem theta_conj (x y : Multiplicative (ZMod 3 × ZMod 3)) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ h : Ug F, h * theta o x * h⁻¹ = theta o y := by
  obtain ⟨h1, e1⟩ := conj_to_a o x hx
  obtain ⟨h2, e2⟩ := conj_to_a o y hy
  refine ⟨h2 * h1⁻¹, ?_⟩
  calc h2 * h1⁻¹ * theta o x * (h2 * h1⁻¹)⁻¹ = h2 * (h1⁻¹ * theta o x * h1) * h2⁻¹ := by group
    _ = h2 * ua o * h2⁻¹ := by rw [← e1]; group
    _ = theta o y := e2

end OmegaData



end CFSG.GH74.QTGen4.Leaves.F112
