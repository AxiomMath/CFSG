module

public import CFSG.ClassicalInvolution.Q3.Q3T6AutConj

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open Matrix
open scoped MatrixGroups

structure M2 where
  a : ZMod 3
  b : ZMod 3
  c : ZMod 3
  d : ZMod 3
deriving DecidableEq

namespace M2

def mul (x y : M2) : M2 :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d, x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩

def one : M2 := ⟨1, 0, 0, 1⟩

def neg (x : M2) : M2 := ⟨-x.a, -x.b, -x.c, -x.d⟩

def det (x : M2) : ZMod 3 := x.a * x.d - x.b * x.c

def adj (x : M2) : M2 := ⟨x.d, -x.b, -x.c, x.a⟩

def smul (s : ZMod 3) (x : M2) : M2 := ⟨s * x.a, s * x.b, s * x.c, s * x.d⟩

def inv (x : M2) : M2 := smul x.det (adj x)

def sq (x : M2) : M2 := mul x x

def cube (x : M2) : M2 := mul x (mul x x)

def comm (x y : M2) : M2 := mul (mul (mul x y) (inv x)) (inv y)

def pm (x y : M2) : Prop := x = y ∨ x = neg y

instance (x y : M2) : Decidable (pm x y) := inferInstanceAs (Decidable (x = y ∨ x = neg y))

def zs : List (ZMod 3) := [0, 1, 2]

def all : List M2 :=
  (zs.flatMap fun a => zs.flatMap fun b => zs.flatMap fun c => zs.map fun d =>
    (⟨a, b, c, d⟩ : M2)).filter (fun x => decide (x.det ≠ 0))

theorem mem_all_of_det_ne_zero (x : M2) (h : x.det ≠ 0) : x ∈ all := by
  obtain ⟨a, b, c, d⟩ := x
  revert h
  revert a b c d
  decide +kernel

theorem mul_inv_self : ∀ x ∈ all, mul x (inv x) = one := by decide +kernel

theorem eq_inv_of_mul_eq_one : ∀ x ∈ all, ∀ y ∈ all, mul x y = one → y = inv x := by
  decide +kernel

theorem pm_iff : ∀ x ∈ all, ∀ y ∈ all,
    (mul (inv x) y = one ∨ mul (inv x) y = neg one) ↔ (y = x ∨ y = neg x) := by decide +kernel

end M2

def toM2 (g : GL (Fin 2) (ZMod 3)) : M2 :=
  ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0, (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1,
    (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0, (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1⟩

theorem toM2_mul (g h : GL (Fin 2) (ZMod 3)) : toM2 (g * h) = (toM2 g).mul (toM2 h) := by
  simp [toM2, M2.mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem toM2_one : toM2 1 = M2.one := by
  simp [toM2, M2.one]

theorem toM2_neg_one : toM2 (-1) = M2.neg M2.one := by
  simp [toM2, M2.neg, M2.one]

theorem toM2_injective : Function.Injective toM2 := by
  intro g h hgh
  apply Units.ext
  ext i j
  have h1 := congrArg M2.a hgh
  have h2 := congrArg M2.b hgh
  have h3 := congrArg M2.c hgh
  have h4 := congrArg M2.d hgh
  fin_cases i <;> fin_cases j <;> assumption

theorem toM2_det_ne_zero (g : GL (Fin 2) (ZMod 3)) : (toM2 g).det ≠ 0 := by
  have h := (Matrix.isUnit_iff_isUnit_det (g : Matrix (Fin 2) (Fin 2) (ZMod 3))).mp g.isUnit
  have h2 := h.ne_zero
  rw [Matrix.det_fin_two] at h2
  simpa [toM2, M2.det] using h2

theorem toM2_mem_all (g : GL (Fin 2) (ZMod 3)) : toM2 g ∈ M2.all :=
  M2.mem_all_of_det_ne_zero _ (toM2_det_ne_zero g)

theorem toM2_inv (g : GL (Fin 2) (ZMod 3)) : toM2 g⁻¹ = (toM2 g).inv := by
  have h1 : (toM2 g).mul (toM2 g⁻¹) = M2.one := by
    rw [← toM2_mul, mul_inv_cancel, toM2_one]
  exact M2.eq_inv_of_mul_eq_one _ (toM2_mem_all g) _ (toM2_mem_all g⁻¹) h1

theorem toM2_sq (g : GL (Fin 2) (ZMod 3)) : toM2 (g * g) = (toM2 g).sq := by
  rw [toM2_mul]
  rfl

theorem toM2_cube (g : GL (Fin 2) (ZMod 3)) : toM2 (g ^ 3) = (toM2 g).cube := by
  rw [pow_three, toM2_mul, toM2_mul]
  rfl

theorem conjAut_eq_one_iff (g : GL (Fin 2) (ZMod 3)) :
    Q3T6.conjAut g = 1 ↔ M2.pm (toM2 g) M2.one := by
  rw [← MonoidHom.mem_ker, Q3T6.conjAut3_ker, Q3T6.Aut.mem_center_gl3_iff]
  constructor
  · rintro (h | h)
    · left
      rw [h, toM2_one]
    · right
      rw [h, toM2_neg_one]
  · rintro (h | h)
    · left
      exact toM2_injective (h.trans toM2_one.symm)
    · right
      exact toM2_injective (h.trans toM2_neg_one.symm)

theorem conjAut_eq_iff (x y : GL (Fin 2) (ZMod 3)) :
    Q3T6.conjAut x = Q3T6.conjAut y ↔ M2.pm (toM2 y) (toM2 x) := by
  have h : Q3T6.conjAut x = Q3T6.conjAut y ↔ Q3T6.conjAut (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
  rw [h, conjAut_eq_one_iff, toM2_mul, toM2_inv]
  exact M2.pm_iff _ (toM2_mem_all x) _ (toM2_mem_all y)

theorem pow_three_eq_one_of_odd {ξ : MulAut SL(2, ZMod 3)} (h : Odd (orderOf ξ)) :
    ξ ^ 3 = 1 := by
  have h1 : orderOf ξ ∣ 3 * 2 ^ 3 := by
    have := orderOf_dvd_natCard ξ
    rw [Q3T6.sl2Three_card_mulAut] at this
    exact this
  have h2 : ¬ 2 ∣ orderOf ξ := by
    obtain ⟨j, hj⟩ := h
    omega
  have h3 : Nat.Coprime (orderOf ξ) (2 ^ 3) :=
    Nat.Coprime.pow_right 3
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))
  exact orderOf_dvd_iff_pow_eq_one.mp (Nat.Coprime.dvd_of_dvd_mul_right h3 h1)

open M2 in
theorem s4a_core : ∀ a ∈ M2.all, ∀ b ∈ M2.all,
    ¬ pm (sq a) one → pm (sq (sq a)) one → pm (sq b) one → ¬ pm b one →
    ¬ pm (mul (sq a) b) one → pm (mul (sq a) b) (mul b (sq a)) →
    pm (cube (comm b a)) one → False := by
  decide +kernel

theorem aut_s4a {A B ζ ξ : MulAut SL(2, ZMod 3)} (hA : A * A = ζ) (hζ : ζ ≠ 1)
    (hζ2 : ζ * ζ = 1) (hB2 : B * B = 1) (hB1 : B ≠ 1) (hBζ : ζ * B ≠ 1)
    (hcomm : B * ζ = ζ * B) (hconj : B * A * B⁻¹ = ξ * A) (hξ : Odd (orderOf ξ)) : False := by
  have hξ3 : ξ ^ 3 = 1 := pow_three_eq_one_of_odd hξ
  have hξe : ξ = B * A * B⁻¹ * A⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hconj.symm
  subst hA
  obtain ⟨a, rfl⟩ := Q3T6.conjAut3_surjective A
  obtain ⟨b, rfl⟩ := Q3T6.conjAut3_surjective B
  have e1 : (Q3T6.conjAut a * Q3T6.conjAut a) = Q3T6.conjAut (a * a) := (map_mul _ _ _).symm
  have hxe : ξ = Q3T6.conjAut (b * a * b⁻¹ * a⁻¹) := by
    rw [hξe]
    simp only [map_mul, map_inv]
  rw [e1] at hζ hζ2 hcomm hBζ
  have h1 : ¬ M2.pm (M2.sq (toM2 a)) M2.one := by
    intro h
    apply hζ
    rw [conjAut_eq_one_iff]
    simpa only [toM2_mul, M2.sq] using h
  have h2 : M2.pm (M2.sq (M2.sq (toM2 a))) M2.one := by
    rw [← map_mul, conjAut_eq_one_iff] at hζ2
    simpa only [toM2_mul, M2.sq] using hζ2
  have h3 : M2.pm (M2.sq (toM2 b)) M2.one := by
    rw [← map_mul, conjAut_eq_one_iff] at hB2
    simpa only [toM2_mul, M2.sq] using hB2
  have h4 : ¬ M2.pm (toM2 b) M2.one := fun h => hB1 ((conjAut_eq_one_iff b).mpr h)
  have h5 : ¬ M2.pm (M2.mul (M2.sq (toM2 a)) (toM2 b)) M2.one := by
    intro h
    apply hBζ
    rw [← map_mul, conjAut_eq_one_iff]
    simpa only [toM2_mul, M2.sq] using h
  have h6 : M2.pm (M2.mul (M2.sq (toM2 a)) (toM2 b)) (M2.mul (toM2 b) (M2.sq (toM2 a))) := by
    rw [← map_mul, ← map_mul, conjAut_eq_iff] at hcomm
    simpa only [toM2_mul, M2.sq] using hcomm
  have h7 : M2.pm (M2.cube (M2.comm (toM2 b) (toM2 a))) M2.one := by
    rw [hxe, ← map_pow, conjAut_eq_one_iff, toM2_cube] at hξ3
    simpa only [M2.comm, toM2_mul, toM2_inv] using hξ3
  exact s4a_core _ (toM2_mem_all a) _ (toM2_mem_all b) h1 h2 h3 h4 h5 h6 h7

end CFSG.ClassicalInvolution.Q3.Q3AM
