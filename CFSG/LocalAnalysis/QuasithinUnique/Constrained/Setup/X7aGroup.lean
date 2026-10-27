module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

variable {F : Type*} [Field F]

@[expose] def u3Mat (x y z : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; x, 1, 0; y, z, 1]

theorem det_u3Mat (x y z : F) : (u3Mat x y z).det = 1 := by
  simp [u3Mat, Matrix.det_fin_three]

@[expose] def u3 (x y z : F) : SL(3, F) := ⟨u3Mat x y z, det_u3Mat x y z⟩

theorem u3_coe (x y z : F) : (u3 x y z : Matrix (Fin 3) (Fin 3) F) = u3Mat x y z := rfl

theorem u3Mat_mul (x y z X Y Z : F) :
    u3Mat x y z * u3Mat X Y Z = u3Mat (x + X) (y + Y + z * X) (z + Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u3Mat, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

theorem u3_mul (x y z X Y Z : F) :
    u3 x y z * u3 X Y Z = u3 (x + X) (y + Y + z * X) (z + Z) :=
  Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul, u3_coe, u3_coe, u3_coe, u3Mat_mul])

theorem u3_zero : u3 (0 : F) 0 0 = 1 :=
  Subtype.ext (by
    rw [u3_coe, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u3Mat])

theorem u3_inj {x y z X Y Z : F} (h : u3 x y z = u3 X Y Z) : x = X ∧ y = Y ∧ z = Z := by
  have h' : u3Mat x y z = u3Mat X Y Z := by
    rw [← u3_coe, ← u3_coe, h]
  have h1 := congrFun (congrFun h' 1) 0
  have h2 := congrFun (congrFun h' 2) 0
  have h3 := congrFun (congrFun h' 2) 1
  simp [u3Mat] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem u3_inv [CharP F 2] (x y z : F) : (u3 x y z)⁻¹ = u3 x (y + x * z) z := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [u3_mul]
  have h2 : ∀ a : F, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  have : y + (y + x * z) + z * x = 0 := by
    linear_combination (h2 y) + (h2 (x * z))
  rw [h2 x, this, h2 z, u3_zero]

@[expose] def upMat (x y z : F) : Matrix (Fin 3) (Fin 3) F := !![1, z, y; 0, 1, x; 0, 0, 1]

theorem det_upMat (x y z : F) : (upMat x y z).det = 1 := by
  simp [upMat, Matrix.det_fin_three]

@[expose] def up3 (x y z : F) : SL(3, F) := ⟨upMat x y z, det_upMat x y z⟩

theorem up3_coe (x y z : F) : (up3 x y z : Matrix (Fin 3) (Fin 3) F) = upMat x y z := rfl

theorem upMat_mul (x y z X Y Z : F) :
    upMat x y z * upMat X Y Z = upMat (x + X) (y + Y + z * X) (z + Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upMat, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

theorem up3_mul (x y z X Y Z : F) :
    up3 x y z * up3 X Y Z = up3 (x + X) (y + Y + z * X) (z + Z) :=
  Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul, up3_coe, up3_coe, up3_coe, upMat_mul])

theorem up3_zero : up3 (0 : F) 0 0 = 1 :=
  Subtype.ext (by
    rw [up3_coe, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upMat])

theorem up3_inj {x y z X Y Z : F} (h : up3 x y z = up3 X Y Z) : x = X ∧ y = Y ∧ z = Z := by
  have h' : upMat x y z = upMat X Y Z := by
    rw [← up3_coe, ← up3_coe, h]
  have h1 := congrFun (congrFun h' 1) 2
  have h2 := congrFun (congrFun h' 0) 2
  have h3 := congrFun (congrFun h' 0) 1
  simp [upMat] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem up3_inv [CharP F 2] (x y z : F) : (up3 x y z)⁻¹ = up3 x (y + z * x) z := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [up3_mul]
  have h2 : ∀ a : F, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  have : y + (y + z * x) + z * x = 0 := by
    linear_combination (h2 y) + (h2 (z * x))
  rw [h2 x, this, h2 z, up3_zero]

@[expose] def wJMat : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem det_wJMat [CharP F 2] : (wJMat : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [wJMat, Matrix.det_fin_three]
  exact (CharTwo.neg_eq (1 : F))

@[expose] def wJ [CharP F 2] : SL(3, F) := ⟨wJMat, det_wJMat⟩

theorem wJ_coe [CharP F 2] : (wJ : SL(3, F)).1 = (wJMat : Matrix (Fin 3) (Fin 3) F) := rfl

theorem wJ_mul_self [CharP F 2] : (wJ : SL(3, F)) * wJ = 1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, wJ_coe, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [wJMat, Matrix.mul_apply, Fin.sum_univ_three])

theorem wJ_inv [CharP F 2] : (wJ : SL(3, F))⁻¹ = wJ :=
  inv_eq_of_mul_eq_one_right wJ_mul_self

theorem wJ_u3_wJ [CharP F 2] (x y z : F) : (wJ : SL(3, F)) * u3 x y z * wJ = up3 x y z :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, wJ_coe, u3_coe, up3_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [wJMat, u3Mat, upMat, Matrix.mul_apply, Fin.sum_univ_three])


@[expose] def lowerUni (F : Type*) [Field F] [CharP F 2] : Subgroup SL(3, F) where
  carrier := Set.range fun p : F × F × F => u3 p.1 p.2.1 p.2.2
  one_mem' := ⟨(0, 0, 0), u3_zero⟩
  mul_mem' := by
    rintro _ _ ⟨⟨x, y, z⟩, rfl⟩ ⟨⟨X, Y, Z⟩, rfl⟩
    exact ⟨(x + X, y + Y + z * X, z + Z), (u3_mul x y z X Y Z).symm⟩
  inv_mem' := by
    rintro _ ⟨⟨x, y, z⟩, rfl⟩
    exact ⟨(x, y + x * z, z), (u3_inv x y z).symm⟩

@[expose] def upperUni (F : Type*) [Field F] [CharP F 2] : Subgroup SL(3, F) where
  carrier := Set.range fun p : F × F × F => up3 p.1 p.2.1 p.2.2
  one_mem' := ⟨(0, 0, 0), up3_zero⟩
  mul_mem' := by
    rintro _ _ ⟨⟨x, y, z⟩, rfl⟩ ⟨⟨X, Y, Z⟩, rfl⟩
    exact ⟨(x + X, y + Y + z * X, z + Z), (up3_mul x y z X Y Z).symm⟩
  inv_mem' := by
    rintro _ ⟨⟨x, y, z⟩, rfl⟩
    exact ⟨(x, y + z * x, z), (up3_inv x y z).symm⟩

theorem mem_lowerUni [CharP F 2] {g : SL(3, F)} : g ∈ lowerUni F ↔ ∃ x y z, g = u3 x y z :=
  ⟨fun ⟨p, hp⟩ => ⟨p.1, p.2.1, p.2.2, hp.symm⟩, fun ⟨x, y, z, h⟩ => ⟨(x, y, z), h.symm⟩⟩

theorem mem_upperUni [CharP F 2] {g : SL(3, F)} : g ∈ upperUni F ↔ ∃ x y z, g = up3 x y z :=
  ⟨fun ⟨p, hp⟩ => ⟨p.1, p.2.1, p.2.2, hp.symm⟩, fun ⟨x, y, z, h⟩ => ⟨(x, y, z), h.symm⟩⟩

theorem wJ_conj_lowerUni [CharP F 2] {u : SL(3, F)} (hu : u ∈ lowerUni F) :
    (wJ : SL(3, F)) * u * (wJ : SL(3, F))⁻¹ ∈ upperUni F := by
  obtain ⟨x, y, z, rfl⟩ := mem_lowerUni.mp hu
  rw [wJ_inv, wJ_u3_wJ]
  exact mem_upperUni.mpr ⟨x, y, z, rfl⟩

theorem card_lowerUni [CharP F 2] : Nat.card (lowerUni F) = Nat.card F ^ 3 := by
  have e : (F × F × F) ≃ lowerUni F := Equiv.ofBijective
    (fun p => ⟨u3 p.1 p.2.1 p.2.2, ⟨p, rfl⟩⟩)
    ⟨fun p q h => by
      have := u3_inj (congrArg Subtype.val h)
      exact Prod.ext this.1 (Prod.ext this.2.1 this.2.2),
      fun ⟨g, ⟨p, hp⟩⟩ => ⟨p, Subtype.ext hp⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  ring

theorem card_upperUni [CharP F 2] : Nat.card (upperUni F) = Nat.card F ^ 3 := by
  have e : (F × F × F) ≃ upperUni F := Equiv.ofBijective
    (fun p => ⟨up3 p.1 p.2.1 p.2.2, ⟨p, rfl⟩⟩)
    ⟨fun p q h => by
      have := up3_inj (congrArg Subtype.val h)
      exact Prod.ext this.1 (Prod.ext this.2.1 this.2.2),
      fun ⟨g, ⟨p, hp⟩⟩ => ⟨p, Subtype.ext hp⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  ring

theorem isPGroup_lowerUni [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f) :
    IsPGroup 2 (lowerUni F) :=
  IsPGroup.of_card (n := 3 * f) (by rw [card_lowerUni, hF, ← pow_mul, mul_comm])

theorem isPGroup_upperUni [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f) :
    IsPGroup 2 (upperUni F) :=
  IsPGroup.of_card (n := 3 * f) (by rw [card_upperUni, hF, ← pow_mul, mul_comm])

@[expose] def dTMat (r t : Fˣ) : Matrix (Fin 3) (Fin 3) F :=
  !![(r : F), 0, 0; 0, (t : F), 0; 0, 0, (((r * t)⁻¹ : Fˣ) : F)]

theorem det_dTMat (r t : Fˣ) : (dTMat r t : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  have hr : (r : F) ≠ 0 := r.ne_zero
  have ht : (t : F) ≠ 0 := t.ne_zero
  simp [dTMat, Matrix.det_fin_three]
  field_simp

@[expose] def dT (r t : Fˣ) : SL(3, F) := ⟨dTMat r t, det_dTMat r t⟩

theorem dT_coe (r t : Fˣ) : (dT r t : Matrix (Fin 3) (Fin 3) F) = dTMat r t := rfl

@[expose] noncomputable def lowerUniEquiv (F : Type*) [Field F] [CharP F 2] : F × F × F ≃ lowerUni F :=
  Equiv.ofBijective (fun p => ⟨u3 p.1 p.2.1 p.2.2, ⟨p, rfl⟩⟩)
    ⟨fun p q h => by
      have := u3_inj (congrArg Subtype.val h)
      exact Prod.ext this.1 (Prod.ext this.2.1 this.2.2),
      fun ⟨g, ⟨p, hp⟩⟩ => ⟨p, Subtype.ext hp⟩⟩

theorem lowerUniEquiv_apply {F : Type*} [Field F] [CharP F 2] (p : F × F × F) :
    ((lowerUniEquiv F p : lowerUni F) : SL(3, F)) = u3 p.1 p.2.1 p.2.2 := rfl

@[expose] noncomputable def upperUniEquiv (F : Type*) [Field F] [CharP F 2] : F × F × F ≃ upperUni F :=
  Equiv.ofBijective (fun p => ⟨up3 p.1 p.2.1 p.2.2, ⟨p, rfl⟩⟩)
    ⟨fun p q h => by
      have := up3_inj (congrArg Subtype.val h)
      exact Prod.ext this.1 (Prod.ext this.2.1 this.2.2),
      fun ⟨g, ⟨p, hp⟩⟩ => ⟨p, Subtype.ext hp⟩⟩

noncomputable instance (F : Type*) [Field F] [CharP F 2] [Fintype F] : Fintype (lowerUni F) :=
  Fintype.ofEquiv _ (lowerUniEquiv F)

theorem card_lowerUni_eq (F : Type*) [Field F] [CharP F 2] [Fintype F] :
    Fintype.card (lowerUni F) = Fintype.card F ^ 3 := by
  rw [← Fintype.card_congr (lowerUniEquiv F), Fintype.card_prod, Fintype.card_prod]
  ring

end CFSG.QuasithinUnique.Setup.X7a
