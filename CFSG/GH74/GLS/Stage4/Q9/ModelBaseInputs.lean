module

public import Mathlib
public meta import Mathlib

public section

namespace CFSG.GH74.GLS.Stage4.Q9

@[ext]
structure F9 where
  re : ZMod 3
  im : ZMod 3

namespace F9

@[expose] def equivProd : F9 ≃ ZMod 3 × ZMod 3 where
  toFun a := (a.re, a.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : DecidableEq F9 := fun a b =>
  decidable_of_iff (a.re = b.re ∧ a.im = b.im) (by
    rcases a with ⟨_, _⟩; rcases b with ⟨_, _⟩; simp)

instance : Fintype F9 := Fintype.ofEquiv _ equivProd.symm

section Algebra

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

instance : Zero F9 := ⟨⟨0, 0⟩⟩
instance : One F9 := ⟨⟨1, 0⟩⟩
instance : Add F9 := ⟨fun a b => ⟨a.re + b.re, a.im + b.im⟩⟩
instance : Neg F9 := ⟨fun a => ⟨-a.re, -a.im⟩⟩
instance : Sub F9 := ⟨fun a b => ⟨a.re - b.re, a.im - b.im⟩⟩
instance : Mul F9 := ⟨fun a b => ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩⟩
instance : NatCast F9 := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast F9 := ⟨fun z => ⟨z, 0⟩⟩

@[simp] theorem zero_re : (0 : F9).re = 0 := rfl
@[simp] theorem zero_im : (0 : F9).im = 0 := rfl
@[simp] theorem one_re : (1 : F9).re = 1 := rfl
@[simp] theorem one_im : (1 : F9).im = 0 := rfl
@[simp] theorem add_re (a b : F9) : (a + b).re = a.re + b.re := rfl
@[simp] theorem add_im (a b : F9) : (a + b).im = a.im + b.im := rfl
@[simp] theorem neg_re (a : F9) : (-a).re = -a.re := rfl
@[simp] theorem neg_im (a : F9) : (-a).im = -a.im := rfl
@[simp] theorem sub_re (a b : F9) : (a - b).re = a.re - b.re := rfl
@[simp] theorem sub_im (a b : F9) : (a - b).im = a.im - b.im := rfl
@[simp] theorem mul_re (a b : F9) : (a * b).re = a.re * b.re - a.im * b.im := rfl
@[simp] theorem mul_im (a b : F9) : (a * b).im = a.re * b.im + a.im * b.re := rfl
@[simp] theorem natCast_re (n : ℕ) : (n : F9).re = n := rfl
@[simp] theorem natCast_im (n : ℕ) : (n : F9).im = 0 := rfl
@[simp] theorem intCast_re (z : ℤ) : (z : F9).re = z := rfl
@[simp] theorem intCast_im (z : ℤ) : (z : F9).im = 0 := rfl

instance : CommRing F9 where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp <;> ring
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  mul_comm a b := by ext <;> simp <;> ring
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp
  intCast_ofNat n := by ext <;> simp
  intCast_negSucc n := by ext <;> simp

instance : Inv F9 :=
  ⟨fun a => ⟨a.re * (a.re * a.re + a.im * a.im), -(a.im * (a.re * a.re + a.im * a.im))⟩⟩

instance : Field F9 where
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := by decide
  inv_zero := by decide
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end Algebra

end F9

@[expose] def nu : F9 := ⟨1, 1⟩

theorem nu_ne_zero : nu ≠ 0 := by decide

@[expose] abbrev SL2 : Type := Matrix.SpecialLinearGroup (Fin 2) F9

@[expose] def A0 : Matrix.GeneralLinearGroup (Fin 2) F9 where
  val := !![0, nu; 1, 0]
  inv := !![0, 1; nu⁻¹, 0]
  val_inv := by decide
  inv_val := by decide

local notation "𝕄" => Matrix (Fin 2) (Fin 2) F9
local notation "𝐀" => ((A0 : Matrix.GeneralLinearGroup (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9)
local notation "𝐁" => ((A0⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F9) : Matrix (Fin 2) (Fin 2) F9)

theorem A0_mul_self : (A0 : Matrix (Fin 2) (Fin 2) F9) * A0 = nu • 1 := by decide

theorem A0_inv_mul_self : 𝐁 * 𝐁 = nu⁻¹ • 1 := by decide

@[expose] def sigmaFun (g : SL2) : SL2 :=
  ⟨!![(g : 𝕄) 1 1, nu * (g : 𝕄) 1 0; nu⁻¹ * (g : 𝕄) 0 1, (g : 𝕄) 0 0], by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    have hinv : nu * nu⁻¹ = 1 := mul_inv_cancel₀ nu_ne_zero
    linear_combination h - ((g : 𝕄) 1 0 * (g : 𝕄) 0 1) * hinv⟩

theorem sigmaFun_val (g : SL2) : ((sigmaFun g : SL2) : 𝕄) = 𝐀 * (g : 𝕄) * 𝐁 := by
  have hν : nu ≠ 0 := nu_ne_zero
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [sigmaFun, A0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;>
    field_simp

theorem sigmaFun_mul (g h : SL2) : sigmaFun (g * h) = sigmaFun g * sigmaFun h := by
  apply Subtype.ext
  have hBA : 𝐁 * 𝐀 = 1 := Units.inv_mul A0
  show ((sigmaFun (g * h) : SL2) : 𝕄) = (sigmaFun g : 𝕄) * (sigmaFun h : 𝕄)
  rw [sigmaFun_val, sigmaFun_val, sigmaFun_val, Matrix.SpecialLinearGroup.coe_mul]
  calc 𝐀 * ((g : 𝕄) * (h : 𝕄)) * 𝐁 = 𝐀 * (g : 𝕄) * (𝐁 * 𝐀) * (h : 𝕄) * 𝐁 := by
        rw [hBA, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (𝐀 * (g : 𝕄) * 𝐁) * (𝐀 * (h : 𝕄) * 𝐁) := by simp only [Matrix.mul_assoc]

theorem sigmaFun_sigmaFun (g : SL2) : sigmaFun (sigmaFun g) = g := by
  apply Subtype.ext
  show ((sigmaFun (sigmaFun g) : SL2) : 𝕄) = (g : 𝕄)
  rw [sigmaFun_val, sigmaFun_val]
  calc 𝐀 * (𝐀 * (g : 𝕄) * 𝐁) * 𝐁 = (𝐀 * 𝐀) * (g : 𝕄) * (𝐁 * 𝐁) := by
        simp only [Matrix.mul_assoc]
    _ = g := by
        rw [A0_mul_self, A0_inv_mul_self]
        simp [smul_smul, inv_mul_cancel₀ nu_ne_zero]

@[expose] def sigmaAut : MulAut SL2 where
  toFun := sigmaFun
  invFun := sigmaFun
  left_inv := sigmaFun_sigmaFun
  right_inv := sigmaFun_sigmaFun
  map_mul' := sigmaFun_mul

theorem sigmaAut_sq (g : SL2) : sigmaAut (sigmaAut g) = g := sigmaFun_sigmaFun g

theorem sigmaAut_mul_self : sigmaAut * sigmaAut = 1 := by
  apply MulEquiv.ext
  intro g
  exact sigmaAut_sq g

theorem sigmaAut_pow_two : sigmaAut ^ 2 = 1 := by
  rw [pow_two]; exact sigmaAut_mul_self

@[expose] def sigmaHom : Multiplicative (ZMod 2) →* MulAut SL2 where
  toFun a := sigmaAut ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ sigmaAut_pow_two]

@[expose] abbrev Lg : Type := SL2 ⋊[sigmaHom] Multiplicative (ZMod 2)

instance : Fintype Lg := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

instance : DecidableEq Lg := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) (by
    constructor
    · rintro ⟨h1, h2⟩; exact SemidirectProduct.ext h1 h2
    · rintro rfl; exact ⟨rfl, rfl⟩)

@[expose] def parityL : Lg →* Multiplicative (ZMod 2) := SemidirectProduct.rightHom

@[expose] def innerL : SL2 →* Lg := SemidirectProduct.inl

@[expose] def minusOne : SL2 := ⟨-1, by rw [Matrix.det_fin_two]; decide⟩

@[expose] def normSL (g : SL2) : SL2 :=
  ⟨!![(g : 𝕄) 0 0, (g : 𝕄) 0 1; (g : 𝕄) 1 0, (g : 𝕄) 1 1], by
    rw [← Matrix.eta_fin_two]; exact g.2⟩

@[expose] def normL (x : Lg) : Lg := ⟨normSL x.left, x.right⟩

@[expose] def ordLAux (l : Lg) : ℕ → Lg → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, p, n => if p = 1 then n else ordLAux l k (normL (p * l)) (n + 1)

@[expose] def ordL (l : Lg) : ℕ := ordLAux l 16 (normL l) 1

end CFSG.GH74.GLS.Stage4.Q9
