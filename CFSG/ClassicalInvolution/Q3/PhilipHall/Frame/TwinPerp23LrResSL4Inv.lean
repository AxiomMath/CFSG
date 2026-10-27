module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSL4Twin
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLinear
import CFSG.LocalAnalysis.SignalizerFunctor.TwoPrimeOrderSolvability

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc.Res

open CFSG.CGT.PushingUpLit.SolKNA CFSG.CGT.PushingUpLit.SolKNA.PSL4Twin
open scoped MatrixGroups

theorem isSolvable_gl_two_three :
    Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) := by
  have hcard : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) = 48 := by
    rw [Matrix.card_GL_field]
    simp [Fin.prod_univ_two, ZMod.card]
  exact CFSG.SignalizerFunctor.Helpers.two_prime_order_solvable _ 2 3 Nat.prime_two
    Nat.prime_three fun r hr hdvd => by
      rw [hcard, show (48 : ℕ) = 2 ^ 4 * 3 by norm_num] at hdvd
      rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h)

def topLeft (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  !![A 0 0, A 0 1; A 1 0, A 1 1]

def botRight (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  !![A 2 2, A 2 3; A 3 2, A 3 3]

theorem topLeft_mul {A B : Matrix (Fin 4) (Fin 4) (ZMod 3)} (hA : A * deltaMat = deltaMat * A)
    (hB : B * deltaMat = deltaMat * B) : topLeft (A * B) = topLeft A * topLeft B := by
  have eA := eq_diagBlk_of_comm A hA
  have eB := eq_diagBlk_of_comm B hB
  rw [eA, eB, diagBlk_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [topLeft, diagBlk, Matrix.mul_apply, Fin.sum_univ_two]

theorem botRight_mul {A B : Matrix (Fin 4) (Fin 4) (ZMod 3)} (hA : A * deltaMat = deltaMat * A)
    (hB : B * deltaMat = deltaMat * B) : botRight (A * B) = botRight A * botRight B := by
  have eA := eq_diagBlk_of_comm A hA
  have eB := eq_diagBlk_of_comm B hB
  rw [eA, eB, diagBlk_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [botRight, diagBlk, Matrix.mul_apply, Fin.sum_univ_two]

theorem topLeft_one : topLeft (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [topLeft]

theorem botRight_one : botRight (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [botRight]

theorem comm_of_mem_centralizer_delta {h : SL(4, ZMod 3)}
    (hh : h ∈ Subgroup.centralizer ({deltaSL} : Set SL(4, ZMod 3))) :
    (h : Matrix (Fin 4) (Fin 4) (ZMod 3)) * deltaMat = deltaMat * h := by
  have := Subgroup.mem_centralizer_singleton_iff.mp hh
  have h' := congrArg (fun y : SL(4, ZMod 3) => (y : Matrix (Fin 4) (Fin 4) (ZMod 3))) this
  simpa only [Matrix.SpecialLinearGroup.coe_mul, coe_deltaSL] using h'

def topLeftHom : Subgroup.centralizer ({deltaSL} : Set SL(4, ZMod 3)) →*
    Matrix (Fin 2) (Fin 2) (ZMod 3) where
  toFun h := topLeft (h.1 : Matrix (Fin 4) (Fin 4) (ZMod 3))
  map_one' := topLeft_one
  map_mul' h h' := by
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact topLeft_mul (comm_of_mem_centralizer_delta h.2) (comm_of_mem_centralizer_delta h'.2)

def botRightHom : Subgroup.centralizer ({deltaSL} : Set SL(4, ZMod 3)) →*
    Matrix (Fin 2) (Fin 2) (ZMod 3) where
  toFun h := botRight (h.1 : Matrix (Fin 4) (Fin 4) (ZMod 3))
  map_one' := botRight_one
  map_mul' h h' := by
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact botRight_mul (comm_of_mem_centralizer_delta h.2) (comm_of_mem_centralizer_delta h'.2)

theorem blocks_injective : Function.Injective
    ((topLeftHom.toHomUnits).prod (botRightHom.toHomUnits) : Subgroup.centralizer
      ({deltaSL} : Set SL(4, ZMod 3)) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) ×
        Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) := by
  intro h h' hh
  have h1 : topLeft (h.1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      topLeft (h'.1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) :=
    congrArg Units.val (congrArg Prod.fst hh)
  have h2 : botRight (h.1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      botRight (h'.1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) :=
    congrArg Units.val (congrArg Prod.snd hh)
  have eh := eq_diagBlk_of_comm _ (comm_of_mem_centralizer_delta h.2)
  have eh' := eq_diagBlk_of_comm _ (comm_of_mem_centralizer_delta h'.2)
  have e1 := congrFun (congrFun h1 0) 0
  have e2 := congrFun (congrFun h1 0) 1
  have e3 := congrFun (congrFun h1 1) 0
  have e4 := congrFun (congrFun h1 1) 1
  have e5 := congrFun (congrFun h2 0) 0
  have e6 := congrFun (congrFun h2 0) 1
  have e7 := congrFun (congrFun h2 1) 0
  have e8 := congrFun (congrFun h2 1) 1
  simp only [topLeft, botRight, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e1 e2 e3 e4 e5 e6 e7 e8
  apply Subtype.ext
  apply Subtype.ext
  rw [eh, eh', e1, e2, e3, e4, e5, e6, e7, e8]

theorem isSolvable_centralizer_delta :
    Group.IsSolvable (Subgroup.centralizer ({deltaSL} : Set SL(4, ZMod 3))) := by
  haveI := isSolvable_gl_two_three
  exact solvable_of_solvable_injective blocks_injective

theorem isSolvable_centralizer_of_sq_eq_one (g : SL(4, ZMod 3))
    (hg2 : (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * g = 1)
    (hgc : g ∉ Subgroup.center SL(4, ZMod 3)) :
    Group.IsSolvable (Subgroup.centralizer ({g} : Set SL(4, ZMod 3))) := by
  obtain ⟨a, ha, P, hP⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_sl_conj_diagonal
    (by decide : (2 : ZMod 3) ≠ 0) (by norm_num : 0 < 4) hg2
  have hdet :
      (Matrix.diagonal fun j : Fin 4 => if j.val < a then (-1 : ZMod 3) else 1).det = 1 := by
    have := congrArg Matrix.det hP
    rw [Matrix.det_mul, Matrix.det_mul, g.2, P.2, one_mul, one_mul] at this
    exact this.symm
  let D : SL(4, ZMod 3) :=
    ⟨Matrix.diagonal fun j : Fin 4 => if j.val < a then (-1 : ZMod 3) else 1, hdet⟩
  have hgD : g = P * D * P⁻¹ := by
    have h1 : g * P = P * D := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact hP)
    rw [← h1]
    group
  have hcentral : D ∈ Subgroup.center SL(4, ZMod 3) → False := fun hD => hgc (by
    rw [hgD]
    exact (inferInstance : (Subgroup.center SL(4, ZMod 3)).Normal).conj_mem D hD P)
  have hDd : D = deltaSL := by
    rcases diag_classes a ha hdet with h1 | h1 | h1
    · exact (hcentral ((mem_center_sl4 D).mpr (Or.inl h1))).elim
    · exact (hcentral ((mem_center_sl4 D).mpr (Or.inr h1))).elim
    · exact Subtype.ext h1
  rw [hDd] at hgD
  have hmem : ∀ x : Subgroup.centralizer ({g} : Set SL(4, ZMod 3)),
      ((MulAut.conj P⁻¹).toMonoidHom.comp
        (Subgroup.centralizer ({g} : Set SL(4, ZMod 3))).subtype) x ∈
        Subgroup.centralizer ({deltaSL} : Set SL(4, ZMod 3)) := by
    intro x
    have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    change P⁻¹ * (x : SL(4, ZMod 3)) * P⁻¹⁻¹ * deltaSL =
      deltaSL * (P⁻¹ * (x : SL(4, ZMod 3)) * P⁻¹⁻¹)
    have hx' : (x : SL(4, ZMod 3)) * (P * deltaSL * P⁻¹) = (P * deltaSL * P⁻¹) * x := by
      rw [← hgD]
      exact hx
    calc P⁻¹ * (x : SL(4, ZMod 3)) * P⁻¹⁻¹ * deltaSL
        = P⁻¹ * ((x : SL(4, ZMod 3)) * (P * deltaSL * P⁻¹)) * P := by group
      _ = P⁻¹ * ((P * deltaSL * P⁻¹) * (x : SL(4, ZMod 3))) * P := by rw [hx']
      _ = deltaSL * (P⁻¹ * (x : SL(4, ZMod 3)) * P⁻¹⁻¹) := by group
  let f : Subgroup.centralizer ({g} : Set SL(4, ZMod 3)) →*
      Subgroup.centralizer ({deltaSL} : Set SL(4, ZMod 3)) :=
    ((MulAut.conj P⁻¹).toMonoidHom.comp
      (Subgroup.centralizer ({g} : Set SL(4, ZMod 3))).subtype).codRestrict _ hmem
  have hf : Function.Injective f := by
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext ((MulAut.conj P⁻¹).injective this)
  haveI := isSolvable_centralizer_delta
  exact solvable_of_solvable_injective hf

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc.Res
