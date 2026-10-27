module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

namespace TwA5Eight

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial Matrix

variable {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)

@[expose] def twA5Entries (a : Fˣ) (t2 t3 t4 : Fˣ) : Fin 6 → F :=
  ![↑a, ↑a, ↑a * ↑t2, ↑a * ↑t3, ↑a * ↑t4, ↑((a ^ 5 * t2 * t3 * t4)⁻¹)]

@[simp] theorem twA5Entries_zero (a : Fˣ) (t2 t3 t4 : Fˣ) :
    twA5Entries (F := F) a t2 t3 t4 0 = ↑a := rfl
@[simp] theorem twA5Entries_one (a : Fˣ) (t2 t3 t4 : Fˣ) :
    twA5Entries (F := F) a t2 t3 t4 1 = ↑a := rfl
@[simp] theorem twA5Entries_two (a : Fˣ) (t2 t3 t4 : Fˣ) :
    twA5Entries (F := F) a t2 t3 t4 2 = ↑a * ↑t2 := rfl
@[simp] theorem twA5Entries_three (a : Fˣ) (t2 t3 t4 : Fˣ) :
    twA5Entries (F := F) a t2 t3 t4 3 = ↑a * ↑t3 := rfl
@[simp] theorem twA5Entries_four (a : Fˣ) (t2 t3 t4 : Fˣ) :
    twA5Entries (F := F) a t2 t3 t4 4 = ↑a * ↑t4 := rfl
@[simp] theorem twA5Entries_five (a : Fˣ) (t2 t3 t4 : Fˣ) :
    twA5Entries (F := F) a t2 t3 t4 5 = ↑((a ^ 5 * t2 * t3 * t4)⁻¹) := rfl

theorem norm_eq_one_of_pow_nine {x : F} (hx : x ^ 9 = 1) : h.norm x = 1 := by
  change x * h.bar x = 1
  rw [h.bar_apply]
  norm_num
  rw [show x * x ^ 8 = x ^ 9 by ring, hx]

theorem norm_eq_one_of_pow_three {x : F} (hx : x ^ 3 = 1) : h.norm x = 1 := by
  apply norm_eq_one_of_pow_nine h
  rw [show x ^ 9 = (x ^ 3) ^ 3 by ring, hx, one_pow]

theorem twA5Entries_norm (a : Fˣ) (t2 t3 t4 : Fˣ)
    (ha : h.norm (a : F) = 1) (h2 : h.norm (t2 : F) = 1)
    (h3 : h.norm (t3 : F) = 1) (h4 : h.norm (t4 : F) = 1) :
    ∀ i, h.norm (twA5Entries (F := F) a t2 t3 t4 i) = 1 := by
  intro i
  fin_cases i <;>
    simp [norm_mul_eq h, norm_inv_eq h, ha, h2, h3, h4,
      show h.norm ((a : F) ^ 5) = 1 from by
        simpa using CFSG.LocalAnalysis.GLTheoremA.Y10F.unitaryNorm_pow_eq_one h ha 5]

theorem twA5Entries_prod (a : Fˣ) (t2 t3 t4 : Fˣ) :
    ∏ i, twA5Entries (F := F) a t2 t3 t4 i = 1 := by
  rw [Fin.prod_univ_six]
  simp only [twA5Entries_zero, twA5Entries_one, twA5Entries_two, twA5Entries_three,
    twA5Entries_four, twA5Entries_five]
  rw [show (↑a * ↑a * (↑a * ↑t2) * (↑a * ↑t3) * (↑a * ↑t4)) =
      (↑(a ^ 5 * t2 * t3 * t4) : F) by
    push_cast
    ring]
  rw [Units.val_inv_eq_inv_val]
  exact mul_inv_cancel₀ (Units.ne_zero (a ^ 5 * t2 * t3 * t4))

@[expose] noncomputable def twA5Diag (a : Fˣ) (t2 t3 t4 : Fˣ)
    (ha : h.norm (a : F) = 1) (h2 : h.norm (t2 : F) = 1)
    (h3 : h.norm (t3 : F) = 1) (h4 : h.norm (t4 : F) = 1) : unitarySU 2 3 F 6 :=
  diagSU h (twA5Entries (F := F) a t2 t3 t4)
    (twA5Entries_norm h a t2 t3 t4 ha h2 h3 h4)
    (twA5Entries_prod (F := F) a t2 t3 t4)

theorem twA5Diag_mul (a t2 t3 t4 a' t2' t3' t4' : Fˣ)
    (ha : h.norm (a : F) = 1) (h2 : h.norm (t2 : F) = 1)
    (h3 : h.norm (t3 : F) = 1) (h4 : h.norm (t4 : F) = 1)
    (ha' : h.norm (a' : F) = 1) (h2' : h.norm (t2' : F) = 1)
    (h3' : h.norm (t3' : F) = 1) (h4' : h.norm (t4' : F) = 1) :
    twA5Diag h a t2 t3 t4 ha h2 h3 h4 * twA5Diag h a' t2' t3' t4' ha' h2' h3' h4' =
      twA5Diag h (a * a') (t2 * t2') (t3 * t3') (t4 * t4')
        (by rw [Units.val_mul, norm_mul_eq h, ha, ha', one_mul])
        (by rw [Units.val_mul, norm_mul_eq h, h2, h2', one_mul])
        (by rw [Units.val_mul, norm_mul_eq h, h3, h3', one_mul])
        (by rw [Units.val_mul, norm_mul_eq h, h4, h4', one_mul]) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, twA5Diag, coe_diagSU]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;>
    simp [twA5Entries, Units.val_mul, mul_pow, mul_assoc, mul_left_comm, mul_comm]
  all_goals group

@[expose] def twA5Param : Subgroup (Fˣ × Fˣ × Fˣ × Fˣ) :=
  (rootsOfUnity 9 F).prod ((rootsOfUnity 3 F).prod ((rootsOfUnity 3 F).prod (rootsOfUnity 3 F)))

theorem mem_twA5Param {x : Fˣ × Fˣ × Fˣ × Fˣ} :
    x ∈ twA5Param (F := F) ↔
      x.1 ^ 9 = 1 ∧ x.2.1 ^ 3 = 1 ∧ x.2.2.1 ^ 3 = 1 ∧ x.2.2.2 ^ 3 = 1 := by
  simp only [twA5Param, Subgroup.mem_prod, mem_rootsOfUnity, and_assoc]

theorem coe_pow_eq_one {u : Fˣ} {n : ℕ} (hu : u ^ n = 1) : ((u : F)) ^ n = 1 := by
  rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]

@[expose] noncomputable def twA5Hom : twA5Param (F := F) →* unitarySU 2 3 F 6 where
  toFun x :=
    twA5Diag h x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2
      (norm_eq_one_of_pow_nine h (coe_pow_eq_one (mem_twA5Param.mp x.2).1))
      (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp x.2).2.1))
      (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp x.2).2.2.1))
      (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp x.2).2.2.2))
  map_one' := by
    change twA5Diag h (1 : Fˣ) (1 : Fˣ) (1 : Fˣ) (1 : Fˣ) _ _ _ _ = 1
    apply Subtype.ext
    apply Units.ext
    simp only [twA5Diag, coe_diagSU, OneMemClass.coe_one, Units.val_one]
    change diagonal (twA5Entries (F := F) (1 : Fˣ) (1 : Fˣ) (1 : Fˣ) (1 : Fˣ)) = 1
    have hentries : twA5Entries (F := F) (1 : Fˣ) (1 : Fˣ) (1 : Fˣ) (1 : Fˣ) =
        fun _ => (1 : F) := by
      funext i
      fin_cases i <;> simp [twA5Entries]
    rw [hentries, Matrix.diagonal_one]
  map_mul' x y := by
    exact (twA5Diag_mul h x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2
      y.1.1 y.1.2.1 y.1.2.2.1 y.1.2.2.2
      (norm_eq_one_of_pow_nine h (coe_pow_eq_one (mem_twA5Param.mp x.2).1))
      (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp x.2).2.1))
      (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp x.2).2.2.1))
      (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp x.2).2.2.2))
      (norm_eq_one_of_pow_nine h (coe_pow_eq_one (mem_twA5Param.mp y.2).1))
      (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp y.2).2.1))
      (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp y.2).2.2.1))
      (norm_eq_one_of_pow_three h (coe_pow_eq_one (mem_twA5Param.mp y.2).2.2.2))).symm

theorem twA5Hom_injective : Function.Injective (twA5Hom h) := by
  intro x y hxy
  have hmat := congrArg (fun z : unitarySU 2 3 F 6 =>
    ((z : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) hxy
  simp only [twA5Hom, twA5Diag, coe_diagSU] at hmat
  have h0 := congrFun (congrFun hmat 0) 0
  have h2 := congrFun (congrFun hmat 2) 2
  have h3 := congrFun (congrFun hmat 3) 3
  have h4 := congrFun (congrFun hmat 4) 4
  have ha : x.1.1 = y.1.1 := by
    apply Units.ext
    simpa using h0
  have hay : (x.1.1 : F) = (y.1.1 : F) := by simpa using congrArg Units.val ha
  have h2' : x.1.2.1 = y.1.2.1 := by
    apply Units.ext
    have hv : (x.1.1 : F) * (x.1.2.1 : F) = (y.1.1 : F) * (y.1.2.1 : F) := by
      simpa using h2
    rw [hay] at hv
    exact mul_left_cancel₀ (Units.ne_zero y.1.1) hv
  have h3' : x.1.2.2.1 = y.1.2.2.1 := by
    apply Units.ext
    have hv : (x.1.1 : F) * (x.1.2.2.1 : F) = (y.1.1 : F) * (y.1.2.2.1 : F) := by
      simpa using h3
    rw [hay] at hv
    exact mul_left_cancel₀ (Units.ne_zero y.1.1) hv
  have h4' : x.1.2.2.2 = y.1.2.2.2 := by
    apply Units.ext
    have hv : (x.1.1 : F) * (x.1.2.2.2 : F) = (y.1.1 : F) * (y.1.2.2.2 : F) := by
      simpa using h4
    rw [hay] at hv
    exact mul_left_cancel₀ (Units.ne_zero y.1.1) hv
  rcases x with ⟨⟨a, t2, t3, t4⟩, hx⟩
  rcases y with ⟨⟨a', t2', t3', t4'⟩, hy⟩
  simp only at ha h2' h3' h4'
  subst ha
  subst h2'
  subst h3'
  subst h4'
  rfl

theorem card_twA5Param (hcard : Nat.card F = 64) :
    Nat.card (twA5Param (F := F)) = 243 := by
  letI : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hK : Nat.card Fˣ = 63 := by
    rw [Nat.card_units, hcard]
  have h9 : Nat.card (rootsOfUnity 9 F) = 9 := by
    apply CFSG.LinearGroups.card_rootsOfUnity_of_dvd
    rw [hcard]
    norm_num
  have h3 : Nat.card (rootsOfUnity 3 F) = 3 := by
    apply CFSG.LinearGroups.card_rootsOfUnity_of_dvd
    rw [hcard]
    norm_num
  have h33 : Nat.card ((rootsOfUnity 3 F).prod (rootsOfUnity 3 F)) = 9 := by
    rw [Nat.card_congr (Subgroup.prodEquiv (rootsOfUnity 3 F) (rootsOfUnity 3 F)).toEquiv,
      Nat.card_prod, h3]
  have h333 : Nat.card ((rootsOfUnity 3 F).prod
      ((rootsOfUnity 3 F).prod (rootsOfUnity 3 F))) = 27 := by
    rw [Nat.card_congr (Subgroup.prodEquiv (rootsOfUnity 3 F)
      ((rootsOfUnity 3 F).prod (rootsOfUnity 3 F))).toEquiv, Nat.card_prod, h3, h33]
  rw [twA5Param,
    Nat.card_congr (Subgroup.prodEquiv (rootsOfUnity 9 F)
      ((rootsOfUnity 3 F).prod ((rootsOfUnity 3 F).prod (rootsOfUnity 3 F)))).toEquiv,
    Nat.card_prod, h9, h333]

theorem card_range_twA5Hom (hcard : Nat.card F = 64) :
    Nat.card (twA5Hom h).range = 243 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (twA5Hom_injective h)).toEquiv]
  exact card_twA5Param (F := F) hcard

end TwA5Eight

end CFSG.LocalAnalysis.GLTheoremA.Y10F
