module

public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.Blueprint.Catalog
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Matrix Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def bar : F4 →+* F4 := frobenius F4 2

theorem bar_apply (c : F4) : bar c = c ^ 2 := frobenius_def 2 c

theorem bar_bar (c : F4) : bar (bar c) = c := by
  rw [bar_apply, bar_apply]
  exact F4.sq_sq c

theorem bar_ω : bar F4.ω = F4.ω + 1 := by decide

theorem hF4 : UnitaryFieldData 2 1 F4 :=
  ⟨Nat.prime_two, le_rfl, by rw [Nat.card_eq_fintype_card, F4.card]; norm_num⟩

theorem hF4_bar : hF4.bar = bar :=
  RingHom.ext fun c => by rw [UnitaryFieldData.bar_apply, bar_apply, pow_one]

@[expose] def J5 : Matrix (Fin 5) (Fin 5) F4 :=
  Matrix.of fun i j => if i.val + j.val = 4 then 1 else 0

theorem J5_mul_J5 : J5 * J5 = 1 := by decide

theorem J5_map_bar : J5.map bar = J5 := by decide

theorem J5_transpose : J5ᵀ = J5 := by decide

@[expose] def SU52 : Subgroup (GL (Fin 5) F4) := gramSU hF4 J5

abbrev mat (g : SU52) : Matrix (Fin 5) (Fin 5) F4 :=
  ((g : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4)

theorem mem_SU52 {g : GL (Fin 5) F4} :
    g ∈ SU52 ↔ ((g : Matrix (Fin 5) (Fin 5) F4).map bar)ᵀ * J5 * g = J5 ∧
      (g : Matrix (Fin 5) (Fin 5) F4).det = 1 := by
  rw [SU52, mem_gramSU, hF4_bar]

theorem unitary_comm {M : Matrix (Fin 5) (Fin 5) F4} :
    (M.map bar)ᵀ * J5 * M = J5 ↔ M * J5 * (M.map bar)ᵀ = J5 := by
  have key : ∀ {A B : Matrix (Fin 5) (Fin 5) F4}, A * J5 * B = J5 → B * J5 * A = J5 := by
    intro A B h
    have h' : A * (J5 * B) = J5 := by rwa [← Matrix.mul_assoc]
    have h1 : (J5 * A * J5) * B = 1 := by
      simp only [Matrix.mul_assoc]
      rw [h', J5_mul_J5]
    have h2 : B * (J5 * A * J5) = 1 := mul_eq_one_comm.mp h1
    calc B * J5 * A = B * (J5 * A * J5) * J5 := by
          simp only [Matrix.mul_assoc, J5_mul_J5, Matrix.mul_one]
      _ = J5 := by rw [h2, Matrix.one_mul]
  exact ⟨key, key⟩

theorem mem_SU52_iff {g : GL (Fin 5) F4} :
    g ∈ SU52 ↔ (g : Matrix (Fin 5) (Fin 5) F4) * J5 * ((g : Matrix (Fin 5) (Fin 5) F4).map bar)ᵀ =
      J5 ∧ (g : Matrix (Fin 5) (Fin 5) F4).det = 1 := by
  rw [mem_SU52, unitary_comm]

instance : DecidablePred (· ∈ SU52) := fun _ => decidable_of_iff _ mem_SU52.symm

theorem inv_mul_of_unitary {M : Matrix (Fin 5) (Fin 5) F4} (h : (M.map bar)ᵀ * J5 * M = J5) :
    (J5 * (M.map bar)ᵀ * J5) * M = 1 := by
  have h' : (M.map bar)ᵀ * (J5 * M) = J5 := by rwa [← Matrix.mul_assoc]
  simp only [Matrix.mul_assoc]
  rw [h', J5_mul_J5]

@[expose] def mkSU (M : Matrix (Fin 5) (Fin 5) F4) (h1 : (M.map bar)ᵀ * J5 * M = J5)
    (h2 : M.det = 1) : SU52 :=
  ⟨⟨M, J5 * (M.map bar)ᵀ * J5, mul_eq_one_comm.mp (inv_mul_of_unitary h1),
    inv_mul_of_unitary h1⟩, mem_SU52.2 ⟨h1, h2⟩⟩

@[simp] theorem mat_mkSU (M : Matrix (Fin 5) (Fin 5) F4) (h1 : (M.map bar)ᵀ * J5 * M = J5)
    (h2 : M.det = 1) : mat (mkSU M h1 h2) = M := rfl

theorem mat_injective : Function.Injective mat := fun _ _ h => Subtype.ext (Units.ext h)

theorem ext_mat {g g' : SU52} (h : mat g = mat g') : g = g' := mat_injective h

@[simp] theorem mat_mul (g g' : SU52) : mat (g * g') = mat g * mat g' := rfl

@[simp] theorem mat_one : mat 1 = 1 := rfl

theorem mat_inv (g : SU52) : mat g⁻¹ = J5 * ((mat g).map bar)ᵀ * J5 :=
  Units.inv_eq_of_mul_eq_one_right (mul_eq_one_comm.mp
    (inv_mul_of_unitary (mem_SU52.1 g.2).1))

theorem mat_inv_eq {g : SU52} {M : Matrix (Fin 5) (Fin 5) F4} (h : mat g * M = 1) :
    mat g⁻¹ = M :=
  Units.inv_eq_of_mul_eq_one_right h

@[expose] def x₁Mat (a b : F4) : Matrix (Fin 5) (Fin 5) F4 :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, a, 1, 0, 0; 0, b, bar a, 1, 0; 0, 0, 0, 0, 1]

@[expose] def x₂Mat (a : F4) : Matrix (Fin 5) (Fin 5) F4 :=
  !![1, 0, 0, 0, 0; a, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, bar a, 1]

@[expose] def x₃Mat (a : F4) : Matrix (Fin 5) (Fin 5) F4 :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; a, 0, 0, 1, 0; 0, bar a, 0, 0, 1]

@[expose] def x₄Mat (a b : F4) : Matrix (Fin 5) (Fin 5) F4 :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; a, 0, 1, 0, 0; 0, 0, 0, 1, 0; b, 0, bar a, 0, 1]

@[expose] def uMat : Matrix (Fin 5) (Fin 5) F4 :=
  !![1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1]

@[expose] def vMat : Matrix (Fin 5) (Fin 5) F4 :=
  !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0]

@[expose] def e₁Mat : Matrix (Fin 5) (Fin 5) F4 := Matrix.diagonal ![1, F4.ω, F4.ω, F4.ω, 1]

@[expose] def e₂Mat : Matrix (Fin 5) (Fin 5) F4 :=
  Matrix.diagonal ![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω]

theorem x₁Mat_unitary_iff : ∀ {a b : F4},
    ((x₁Mat a b).map bar)ᵀ * J5 * x₁Mat a b = J5 ↔ a * bar a = b + bar b := by
  decide

theorem x₄Mat_unitary_iff : ∀ {a b : F4},
    ((x₄Mat a b).map bar)ᵀ * J5 * x₄Mat a b = J5 ↔ a * bar a = b + bar b := by
  decide

theorem x₂Mat_unitary : ∀ a : F4, ((x₂Mat a).map bar)ᵀ * J5 * x₂Mat a = J5 := by decide

theorem x₃Mat_unitary : ∀ a : F4, ((x₃Mat a).map bar)ᵀ * J5 * x₃Mat a = J5 := by decide

theorem uMat_unitary : (uMat.map bar)ᵀ * J5 * uMat = J5 := by decide

theorem vMat_unitary : (vMat.map bar)ᵀ * J5 * vMat = J5 := by decide

theorem e₁Mat_unitary : (e₁Mat.map bar)ᵀ * J5 * e₁Mat = J5 := by decide

theorem e₂Mat_unitary : (e₂Mat.map bar)ᵀ * J5 * e₂Mat = J5 := by decide

theorem det_x₁Mat (a b : F4) : (x₁Mat a b).det = 1 := by
  simp [x₁Mat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

theorem det_x₂Mat (a : F4) : (x₂Mat a).det = 1 := by
  simp [x₂Mat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

theorem det_x₃Mat (a : F4) : (x₃Mat a).det = 1 := by
  simp [x₃Mat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

theorem det_x₄Mat (a b : F4) : (x₄Mat a b).det = 1 := by
  simp [x₄Mat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

theorem det_uMat : uMat.det = 1 := by
  simp [uMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

theorem det_vMat : vMat.det = 1 := by
  simp [vMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

theorem det_e₁Mat : e₁Mat.det = 1 := by
  rw [e₁Mat, Matrix.det_diagonal]
  decide

theorem det_e₂Mat : e₂Mat.det = 1 := by
  rw [e₂Mat, Matrix.det_diagonal]
  decide

@[expose] def x₁SU (a b : F4) (h : a * bar a = b + bar b) : SU52 :=
  mkSU (x₁Mat a b) (x₁Mat_unitary_iff.2 h) (det_x₁Mat a b)

@[expose] def x₂SU (a : F4) : SU52 := mkSU (x₂Mat a) (x₂Mat_unitary a) (det_x₂Mat a)

@[expose] def x₃SU (a : F4) : SU52 := mkSU (x₃Mat a) (x₃Mat_unitary a) (det_x₃Mat a)

@[expose] def x₄SU (a b : F4) (h : a * bar a = b + bar b) : SU52 :=
  mkSU (x₄Mat a b) (x₄Mat_unitary_iff.2 h) (det_x₄Mat a b)

@[expose] def uSU : SU52 := mkSU uMat uMat_unitary det_uMat

@[expose] def vSU : SU52 := mkSU vMat vMat_unitary det_vMat

@[expose] def e₁SU : SU52 := mkSU e₁Mat e₁Mat_unitary det_e₁Mat

@[expose] def e₂SU : SU52 := mkSU e₂Mat e₂Mat_unitary det_e₂Mat

@[simp] theorem mat_x₁SU (a b : F4) (h : a * bar a = b + bar b) : mat (x₁SU a b h) = x₁Mat a b :=
  rfl

@[simp] theorem mat_x₂SU (a : F4) : mat (x₂SU a) = x₂Mat a := rfl

@[simp] theorem mat_x₃SU (a : F4) : mat (x₃SU a) = x₃Mat a := rfl

@[simp] theorem mat_x₄SU (a b : F4) (h : a * bar a = b + bar b) : mat (x₄SU a b h) = x₄Mat a b :=
  rfl

@[simp] theorem mat_uSU : mat uSU = uMat := rfl

@[simp] theorem mat_vSU : mat vSU = vMat := rfl

@[simp] theorem mat_e₁SU : mat e₁SU = e₁Mat := rfl

@[simp] theorem mat_e₂SU : mat e₂SU = e₂Mat := rfl

theorem x₁Mat_mul (a b c d : F4) :
    x₁Mat a b * x₁Mat c d = x₁Mat (a + c) (b + d + bar a * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x₁Mat, Matrix.mul_apply, Fin.sum_univ_five]
  ring

theorem x₄Mat_mul (a b c d : F4) :
    x₄Mat a b * x₄Mat c d = x₄Mat (a + c) (b + d + bar a * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x₄Mat, Matrix.mul_apply, Fin.sum_univ_five]
  ring

theorem x₂Mat_mul (a c : F4) : x₂Mat a * x₂Mat c = x₂Mat (a + c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x₂Mat, Matrix.mul_apply, Fin.sum_univ_five]

theorem x₃Mat_mul (a c : F4) : x₃Mat a * x₃Mat c = x₃Mat (a + c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x₃Mat, Matrix.mul_apply, Fin.sum_univ_five]

theorem x₁Mat_zero : x₁Mat 0 0 = 1 := by decide

theorem x₂Mat_zero : x₂Mat 0 = 1 := by decide

theorem x₃Mat_zero : x₃Mat 0 = 1 := by decide

theorem x₄Mat_zero : x₄Mat 0 0 = 1 := by decide

theorem inv_coord : ∀ a b : F4, a + a = 0 ∧ b + (b + a * bar a) + bar a * a = 0 := by decide

section Roots

variable (P : F4 → Prop) (hP0 : P 0) (hPadd : ∀ a c, P a → P c → P (a + c))

@[expose] def x₁Sub : Subgroup SU52 where
  carrier := {g | ∃ a b : F4, P a ∧ mat g = x₁Mat a b}
  mul_mem' := by
    rintro g g' ⟨a, b, ha, hg⟩ ⟨c, d, hc, hg'⟩
    exact ⟨a + c, b + d + bar a * c, hPadd a c ha hc, by rw [mat_mul, hg, hg', x₁Mat_mul]⟩
  one_mem' := ⟨0, 0, hP0, by rw [mat_one, x₁Mat_zero]⟩
  inv_mem' := by
    rintro g ⟨a, b, ha, hg⟩
    refine ⟨a, b + a * bar a, ha, mat_inv_eq ?_⟩
    rw [hg, x₁Mat_mul, (inv_coord a b).1, (inv_coord a b).2, x₁Mat_zero]

@[expose] def x₄Sub : Subgroup SU52 where
  carrier := {g | ∃ a b : F4, P a ∧ mat g = x₄Mat a b}
  mul_mem' := by
    rintro g g' ⟨a, b, ha, hg⟩ ⟨c, d, hc, hg'⟩
    exact ⟨a + c, b + d + bar a * c, hPadd a c ha hc, by rw [mat_mul, hg, hg', x₄Mat_mul]⟩
  one_mem' := ⟨0, 0, hP0, by rw [mat_one, x₄Mat_zero]⟩
  inv_mem' := by
    rintro g ⟨a, b, ha, hg⟩
    refine ⟨a, b + a * bar a, ha, mat_inv_eq ?_⟩
    rw [hg, x₄Mat_mul, (inv_coord a b).1, (inv_coord a b).2, x₄Mat_zero]

@[expose] def x₂Sub : Subgroup SU52 where
  carrier := {g | ∃ a : F4, P a ∧ mat g = x₂Mat a}
  mul_mem' := by
    rintro g g' ⟨a, ha, hg⟩ ⟨c, hc, hg'⟩
    exact ⟨a + c, hPadd a c ha hc, by rw [mat_mul, hg, hg', x₂Mat_mul]⟩
  one_mem' := ⟨0, hP0, by rw [mat_one, x₂Mat_zero]⟩
  inv_mem' := by
    rintro g ⟨a, ha, hg⟩
    refine ⟨a, ha, mat_inv_eq ?_⟩
    rw [hg, x₂Mat_mul, (inv_coord a 0).1, x₂Mat_zero]

@[expose] def x₃Sub : Subgroup SU52 where
  carrier := {g | ∃ a : F4, P a ∧ mat g = x₃Mat a}
  mul_mem' := by
    rintro g g' ⟨a, ha, hg⟩ ⟨c, hc, hg'⟩
    exact ⟨a + c, hPadd a c ha hc, by rw [mat_mul, hg, hg', x₃Mat_mul]⟩
  one_mem' := ⟨0, hP0, by rw [mat_one, x₃Mat_zero]⟩
  inv_mem' := by
    rintro g ⟨a, ha, hg⟩
    refine ⟨a, ha, mat_inv_eq ?_⟩
    rw [hg, x₃Mat_mul, (inv_coord a 0).1, x₃Mat_zero]

variable {P hP0 hPadd}

theorem mem_x₁Sub {g : SU52} :
    g ∈ x₁Sub P hP0 hPadd ↔ ∃ a b : F4, P a ∧ mat g = x₁Mat a b := Iff.rfl

theorem mem_x₂Sub {g : SU52} : g ∈ x₂Sub P hP0 hPadd ↔ ∃ a : F4, P a ∧ mat g = x₂Mat a :=
  Iff.rfl

theorem mem_x₃Sub {g : SU52} : g ∈ x₃Sub P hP0 hPadd ↔ ∃ a : F4, P a ∧ mat g = x₃Mat a :=
  Iff.rfl

theorem mem_x₄Sub {g : SU52} :
    g ∈ x₄Sub P hP0 hPadd ↔ ∃ a b : F4, P a ∧ mat g = x₄Mat a b := Iff.rfl

theorem x₁Mat_apply_two_one (a b : F4) : x₁Mat a b 2 1 = a := rfl

theorem x₁Mat_apply_three_one (a b : F4) : x₁Mat a b 3 1 = b := rfl

theorem x₂Mat_apply_one_zero (a : F4) : x₂Mat a 1 0 = a := rfl

theorem x₃Mat_apply_three_zero (a : F4) : x₃Mat a 3 0 = a := rfl

theorem x₄Mat_apply_two_zero (a b : F4) : x₄Mat a b 2 0 = a := rfl

theorem x₄Mat_apply_four_zero (a b : F4) : x₄Mat a b 4 0 = b := rfl

theorem x₁Mat_inj {a b c d : F4} (h : x₁Mat a b = x₁Mat c d) : a = c ∧ b = d :=
  ⟨congrFun (congrFun h 2) 1, congrFun (congrFun h 3) 1⟩

theorem x₄Mat_inj {a b c d : F4} (h : x₄Mat a b = x₄Mat c d) : a = c ∧ b = d :=
  ⟨congrFun (congrFun h 2) 0, congrFun (congrFun h 4) 0⟩

theorem x₂Mat_inj {a c : F4} (h : x₂Mat a = x₂Mat c) : a = c := congrFun (congrFun h 1) 0

theorem x₃Mat_inj {a c : F4} (h : x₃Mat a = x₃Mat c) : a = c := congrFun (congrFun h 3) 0

theorem x₁_coord_rel {g : SU52} {a b : F4} (hg : mat g = x₁Mat a b) : a * bar a = b + bar b :=
  x₁Mat_unitary_iff.1 (hg ▸ (mem_SU52.1 g.2).1)

theorem x₄_coord_rel {g : SU52} {a b : F4} (hg : mat g = x₄Mat a b) : a * bar a = b + bar b :=
  x₄Mat_unitary_iff.1 (hg ▸ (mem_SU52.1 g.2).1)

variable [DecidablePred P]

theorem card_x₁Sub : Nat.card (x₁Sub P hP0 hPadd) =
    Fintype.card {p : F4 × F4 // P p.1 ∧ p.1 * bar p.1 = p.2 + bar p.2} := by
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun g => ⟨(mat g 2 1, mat g 3 1), ?_⟩
      invFun := fun p => ⟨x₁SU p.1.1 p.1.2 p.2.2, p.1.1, p.1.2, p.2.1, rfl⟩
      left_inv := fun g => ?_
      right_inv := fun p => rfl }
  · obtain ⟨a, b, ha, hg⟩ := g.2
    rw [hg, x₁Mat_apply_two_one, x₁Mat_apply_three_one]
    exact ⟨ha, x₁_coord_rel hg⟩
  · obtain ⟨a, b, -, hg⟩ := g.2
    refine Subtype.ext (ext_mat ?_)
    simp only [mat_x₁SU, hg, x₁Mat_apply_two_one, x₁Mat_apply_three_one]

theorem card_x₄Sub : Nat.card (x₄Sub P hP0 hPadd) =
    Fintype.card {p : F4 × F4 // P p.1 ∧ p.1 * bar p.1 = p.2 + bar p.2} := by
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun g => ⟨(mat g 2 0, mat g 4 0), ?_⟩
      invFun := fun p => ⟨x₄SU p.1.1 p.1.2 p.2.2, p.1.1, p.1.2, p.2.1, rfl⟩
      left_inv := fun g => ?_
      right_inv := fun p => rfl }
  · obtain ⟨a, b, ha, hg⟩ := g.2
    rw [hg, x₄Mat_apply_two_zero, x₄Mat_apply_four_zero]
    exact ⟨ha, x₄_coord_rel hg⟩
  · obtain ⟨a, b, -, hg⟩ := g.2
    refine Subtype.ext (ext_mat ?_)
    simp only [mat_x₄SU, hg, x₄Mat_apply_two_zero, x₄Mat_apply_four_zero]

theorem card_x₂Sub : Nat.card (x₂Sub P hP0 hPadd) = Fintype.card {a : F4 // P a} := by
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun g => ⟨mat g 1 0, ?_⟩
      invFun := fun a => ⟨x₂SU a, a, a.2, rfl⟩
      left_inv := fun g => ?_
      right_inv := fun a => rfl }
  · obtain ⟨a, ha, hg⟩ := g.2
    rwa [hg, x₂Mat_apply_one_zero]
  · obtain ⟨a, -, hg⟩ := g.2
    refine Subtype.ext (ext_mat ?_)
    simp only [mat_x₂SU, hg, x₂Mat_apply_one_zero]

theorem card_x₃Sub : Nat.card (x₃Sub P hP0 hPadd) = Fintype.card {a : F4 // P a} := by
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun g => ⟨mat g 3 0, ?_⟩
      invFun := fun a => ⟨x₃SU a, a, a.2, rfl⟩
      left_inv := fun g => ?_
      right_inv := fun a => rfl }
  · obtain ⟨a, ha, hg⟩ := g.2
    rwa [hg, x₃Mat_apply_three_zero]
  · obtain ⟨a, -, hg⟩ := g.2
    refine Subtype.ext (ext_mat ?_)
    simp only [mat_x₃SU, hg, x₃Mat_apply_three_zero]

end Roots

theorem true_add : ∀ (_ _ : F4), True → True → True := fun _ _ _ _ => trivial

theorem zero_add_zero (a c : F4) (ha : a = 0) (hc : c = 0) : a + c = 0 := by rw [ha, hc, add_zero]

theorem bar_add_fixed (a c : F4) (ha : bar a = a) (hc : bar c = c) : bar (a + c) = a + c := by
  rw [map_add, ha, hc]

@[expose] def X₁sub : Subgroup SU52 := x₁Sub (fun _ => True) trivial true_add

@[expose] def X₂sub : Subgroup SU52 := x₂Sub (fun _ => True) trivial true_add

@[expose] def X₃sub : Subgroup SU52 := x₃Sub (fun _ => True) trivial true_add

@[expose] def X₄sub : Subgroup SU52 := x₄Sub (fun _ => True) trivial true_add

@[expose] def ZX₁sub : Subgroup SU52 := x₁Sub (· = 0) rfl zero_add_zero

@[expose] def ZX₄sub : Subgroup SU52 := x₄Sub (· = 0) rfl zero_add_zero

@[expose] def X₂zsub : Subgroup SU52 := x₂Sub (fun a => bar a = a) (map_zero bar) bar_add_fixed

@[expose] def X₃zsub : Subgroup SU52 := x₃Sub (fun a => bar a = a) (map_zero bar) bar_add_fixed

@[expose] def X₁starSub : Subgroup SU52 :=
  x₁Sub (fun a => bar a = a) (map_zero bar) bar_add_fixed

@[expose] def X₄starSub : Subgroup SU52 :=
  x₄Sub (fun a => bar a = a) (map_zero bar) bar_add_fixed

theorem mem_X₁sub {g : SU52} : g ∈ X₁sub ↔ ∃ a b : F4, mat g = x₁Mat a b := by
  simp [X₁sub, mem_x₁Sub]

theorem mem_X₂sub {g : SU52} : g ∈ X₂sub ↔ ∃ a : F4, mat g = x₂Mat a := by
  simp [X₂sub, mem_x₂Sub]

theorem mem_X₃sub {g : SU52} : g ∈ X₃sub ↔ ∃ a : F4, mat g = x₃Mat a := by
  simp [X₃sub, mem_x₃Sub]

theorem mem_X₄sub {g : SU52} : g ∈ X₄sub ↔ ∃ a b : F4, mat g = x₄Mat a b := by
  simp [X₄sub, mem_x₄Sub]

theorem x₁SU_mem (a b : F4) (h : a * bar a = b + bar b) : x₁SU a b h ∈ X₁sub :=
  mem_X₁sub.2 ⟨a, b, rfl⟩

theorem x₂SU_mem (a : F4) : x₂SU a ∈ X₂sub := mem_X₂sub.2 ⟨a, rfl⟩

theorem x₃SU_mem (a : F4) : x₃SU a ∈ X₃sub := mem_X₃sub.2 ⟨a, rfl⟩

theorem x₄SU_mem (a b : F4) (h : a * bar a = b + bar b) : x₄SU a b h ∈ X₄sub :=
  mem_X₄sub.2 ⟨a, b, rfl⟩

theorem mem_X₁sub_iff {g : SU52} :
    g ∈ X₁sub ↔ ∃ (a b : F4) (h : a * bar a = b + bar b), g = x₁SU a b h := by
  rw [mem_X₁sub]
  constructor
  · rintro ⟨a, b, hg⟩
    exact ⟨a, b, x₁_coord_rel hg, ext_mat hg⟩
  · rintro ⟨a, b, h, rfl⟩
    exact ⟨a, b, rfl⟩

theorem mem_X₄sub_iff {g : SU52} :
    g ∈ X₄sub ↔ ∃ (a b : F4) (h : a * bar a = b + bar b), g = x₄SU a b h := by
  rw [mem_X₄sub]
  constructor
  · rintro ⟨a, b, hg⟩
    exact ⟨a, b, x₄_coord_rel hg, ext_mat hg⟩
  · rintro ⟨a, b, h, rfl⟩
    exact ⟨a, b, rfl⟩

theorem card_X₁sub : Nat.card X₁sub = 8 := by
  rw [X₁sub, card_x₁Sub]
  decide

theorem card_X₂sub : Nat.card X₂sub = 4 := by
  rw [X₂sub, card_x₂Sub]
  decide

theorem card_X₃sub : Nat.card X₃sub = 4 := by
  rw [X₃sub, card_x₃Sub]
  decide

theorem card_X₄sub : Nat.card X₄sub = 8 := by
  rw [X₄sub, card_x₄Sub]
  decide

theorem card_ZX₁sub : Nat.card ZX₁sub = 2 := by
  rw [ZX₁sub, card_x₁Sub]
  decide

theorem card_ZX₄sub : Nat.card ZX₄sub = 2 := by
  rw [ZX₄sub, card_x₄Sub]
  decide

theorem card_X₂zsub : Nat.card X₂zsub = 2 := by
  rw [X₂zsub, card_x₂Sub]
  decide

theorem card_X₃zsub : Nat.card X₃zsub = 2 := by
  rw [X₃zsub, card_x₃Sub]
  decide

theorem card_X₁starSub : Nat.card X₁starSub = 4 := by
  rw [X₁starSub, card_x₁Sub]
  decide

theorem card_X₄starSub : Nat.card X₄starSub = 4 := by
  rw [X₄starSub, card_x₄Sub]
  decide

theorem x₁Mat_x₂Mat_comm : ∀ {a b : F4} (c : F4), a * bar a = b + bar b →
    x₁Mat a (b + a * bar a) * x₂Mat c * x₁Mat a b * x₂Mat c =
      x₃Mat (bar b * c) * x₄Mat (a * c) (b * c * bar c) := by
  intro a b c h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x₁Mat, x₂Mat, x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five] <;>
    revert a b c <;> decide

theorem x₁Mat_x₄Mat_comm : ∀ {a b c d : F4}, a * bar a = b + bar b → c * bar c = d + bar d →
    x₁Mat a (b + a * bar a) * x₄Mat c (d + c * bar c) * x₁Mat a b * x₄Mat c d =
      x₃Mat (bar a * c) := by
  intro a b c d h h'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x₁Mat, x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five] <;>
    revert a b c d <;> decide

theorem x₂Mat_x₃Mat_comm (a c : F4) :
    x₂Mat a * x₃Mat c * x₂Mat a * x₃Mat c = x₄Mat 0 (a * bar c + bar a * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x₂Mat, x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five] <;>
    revert a c <;> decide

theorem x₁Mat_x₃Mat_comm (a b c : F4) : x₁Mat a b * x₃Mat c = x₃Mat c * x₁Mat a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x₁Mat, x₃Mat, Matrix.mul_apply, Fin.sum_univ_five]

theorem x₂Mat_x₄Mat_comm (a c d : F4) : x₂Mat a * x₄Mat c d = x₄Mat c d * x₂Mat a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x₂Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five]

theorem x₃Mat_x₄Mat_comm (a c d : F4) : x₃Mat a * x₄Mat c d = x₄Mat c d * x₃Mat a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five]

theorem mat_inv_of_x₁ {g : SU52} {a b : F4} (hg : mat g = x₁Mat a b) :
    mat g⁻¹ = x₁Mat a (b + a * bar a) :=
  mat_inv_eq (by rw [hg, x₁Mat_mul, (inv_coord a b).1, (inv_coord a b).2, x₁Mat_zero])

theorem mat_inv_of_x₂ {g : SU52} {a : F4} (hg : mat g = x₂Mat a) : mat g⁻¹ = x₂Mat a :=
  mat_inv_eq (by rw [hg, x₂Mat_mul, (inv_coord a 0).1, x₂Mat_zero])

theorem mat_inv_of_x₃ {g : SU52} {a : F4} (hg : mat g = x₃Mat a) : mat g⁻¹ = x₃Mat a :=
  mat_inv_eq (by rw [hg, x₃Mat_mul, (inv_coord a 0).1, x₃Mat_zero])

theorem mat_inv_of_x₄ {g : SU52} {a b : F4} (hg : mat g = x₄Mat a b) :
    mat g⁻¹ = x₄Mat a (b + a * bar a) :=
  mat_inv_eq (by rw [hg, x₄Mat_mul, (inv_coord a b).1, (inv_coord a b).2, x₄Mat_zero])

theorem commutator_x₁_x₂ {g h : SU52} {a b c : F4} (hg : mat g = x₁Mat a b)
    (hh : mat h = x₂Mat c) :
    mat (g⁻¹ * h⁻¹ * g * h) = x₃Mat (bar b * c) * x₄Mat (a * c) (b * c * bar c) := by
  rw [mat_mul, mat_mul, mat_mul, mat_inv_of_x₁ hg, mat_inv_of_x₂ hh, hg, hh]
  exact x₁Mat_x₂Mat_comm c (x₁_coord_rel hg)

theorem commutator_x₁_x₄ {g h : SU52} {a b c d : F4} (hg : mat g = x₁Mat a b)
    (hh : mat h = x₄Mat c d) : mat (g⁻¹ * h⁻¹ * g * h) = x₃Mat (bar a * c) := by
  rw [mat_mul, mat_mul, mat_mul, mat_inv_of_x₁ hg, mat_inv_of_x₄ hh, hg, hh]
  exact x₁Mat_x₄Mat_comm (x₁_coord_rel hg) (x₄_coord_rel hh)

theorem commutator_x₂_x₃ {g h : SU52} {a c : F4} (hg : mat g = x₂Mat a)
    (hh : mat h = x₃Mat c) :
    mat (g⁻¹ * h⁻¹ * g * h) = x₄Mat 0 (a * bar c + bar a * c) := by
  rw [mat_mul, mat_mul, mat_mul, mat_inv_of_x₂ hg, mat_inv_of_x₃ hh, hg, hh]
  exact x₂Mat_x₃Mat_comm a c

theorem commute_X₁_X₃ {g h : SU52} (hg : g ∈ X₁sub) (hh : h ∈ X₃sub) : g * h = h * g := by
  obtain ⟨a, b, hg⟩ := mem_X₁sub.1 hg
  obtain ⟨c, hh⟩ := mem_X₃sub.1 hh
  exact ext_mat (by rw [mat_mul, mat_mul, hg, hh, x₁Mat_x₃Mat_comm])

theorem commute_X₂_X₄ {g h : SU52} (hg : g ∈ X₂sub) (hh : h ∈ X₄sub) : g * h = h * g := by
  obtain ⟨a, hg⟩ := mem_X₂sub.1 hg
  obtain ⟨c, d, hh⟩ := mem_X₄sub.1 hh
  exact ext_mat (by rw [mat_mul, mat_mul, hg, hh, x₂Mat_x₄Mat_comm])

theorem commute_X₃_X₄ {g h : SU52} (hg : g ∈ X₃sub) (hh : h ∈ X₄sub) : g * h = h * g := by
  obtain ⟨a, hg⟩ := mem_X₃sub.1 hg
  obtain ⟨c, d, hh⟩ := mem_X₄sub.1 hh
  exact ext_mat (by rw [mat_mul, mat_mul, hg, hh, x₃Mat_x₄Mat_comm])

@[expose] def yIdx : Fin 5 ≃ HypIndex 2 1 where
  toFun := ![.inr (.inr 0), .inr (.inr 1), .inr (.inl 0), .inl 1, .inl 0]
  invFun a := match a with
    | .inl i => ![4, 3] i
    | .inr (.inl _) => 2
    | .inr (.inr i) => ![0, 1] i
  left_inv := by decide
  right_inv := by decide

theorem reindex_J5 : Matrix.reindex yIdx yIdx J5 = hypGram 2 1 F4 := by
  ext a b
  rw [reindex_apply, submatrix_apply, hypGram_apply]
  revert a b
  decide

theorem fullPos_yIdx_lt_iff : ∀ i j : Fin 5, fullPos (yIdx j) < fullPos (yIdx i) ↔ i < j := by
  decide

@[expose] noncomputable def ρGL : GL (Fin 5) F4 ≃* GL (HypIndex 2 1) F4 :=
  Units.mapEquiv (Matrix.reindexAlgEquiv F4 F4 yIdx).toMulEquiv

theorem coe_ρGL (g : GL (Fin 5) F4) :
    ((ρGL g : GL (HypIndex 2 1) F4) : Matrix (HypIndex 2 1) (HypIndex 2 1) F4) =
      Matrix.reindex yIdx yIdx (g : Matrix (Fin 5) (Fin 5) F4) := rfl

theorem ρGL_mem_hypSU_iff {g : GL (Fin 5) F4} : ρGL g ∈ hypSU hF4 2 1 ↔ g ∈ SU52 := by
  rw [mem_hypSU, mem_SU52, coe_ρGL, hF4_bar, det_reindex_self, ← reindex_J5]
  have hmul : ∀ M N : Matrix (Fin 5) (Fin 5) F4,
      Matrix.reindex yIdx yIdx M * Matrix.reindex yIdx yIdx N = Matrix.reindex yIdx yIdx (M * N) :=
    fun M N => by rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv]
  have hmap : ∀ M : Matrix (Fin 5) (Fin 5) F4,
      ((Matrix.reindex yIdx yIdx M).map bar)ᵀ = Matrix.reindex yIdx yIdx ((M.map bar)ᵀ) :=
    fun M => by rw [reindex_apply, reindex_apply, ← submatrix_map, transpose_submatrix]
  rw [hmap, hmul, hmul, (Matrix.reindex yIdx yIdx).injective.eq_iff]

theorem map_ρGL_SU52 : SU52.map ρGL.toMonoidHom = hypSU hF4 2 1 := by
  ext g
  rw [Subgroup.mem_map_equiv, ← ρGL_mem_hypSU_iff, MulEquiv.apply_symm_apply]

@[expose] noncomputable def ρ : SU52 ≃* hypSU hF4 2 1 :=
  (ρGL.subgroupMap SU52).trans (MulEquiv.subgroupCongr map_ρGL_SU52)

theorem coe_ρ (g : SU52) : (ρ g : GL (HypIndex 2 1) F4) = ρGL g := rfl

theorem card_SU52 : Nat.card SU52 = 13685760 ∧ 2 ^ (Nat.card SU52).factorization 2 = 2 ^ 10 := by
  rw [Nat.card_congr ρ.toEquiv]
  obtain ⟨h1, h2⟩ := card_hypSU hF4 (r := 2) (ε := 1) (by norm_num)
  refine ⟨?_, by rw [h2]; norm_num⟩
  have h3 : (Nat.card (hypSU hF4 2 1) : ℤ) = 13685760 := by
    rw [h1]
    decide
  exact_mod_cast h3

@[expose] noncomputable def LTsub : Subgroup SU52 :=
  (hypUnitriangular hF4 2 1).map ρ.symm.toMonoidHom

theorem mem_LTsub {g : SU52} :
    g ∈ LTsub ↔ (∀ i j : Fin 5, i < j → mat g i j = 0) ∧ ∀ i : Fin 5, mat g i i = 1 := by
  rw [LTsub, Subgroup.mem_map_equiv, MulEquiv.symm_symm, mem_hypUnitriangular]
  simp only [coe_ρ, coe_ρGL, reindex_apply, Matrix.BlockTriangular, submatrix_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := @h1 (yIdx i) (yIdx j) ((fullPos_yIdx_lt_iff i j).2 hij)
      simpa using this
    · simpa using h2 (yIdx i)
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b hab => ?_, fun a => h2 _⟩
    apply h1
    rw [← fullPos_yIdx_lt_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hab

theorem card_LTsub : Nat.card LTsub = 2 ^ 10 := by
  rw [LTsub, Subgroup.card_map_of_injective ρ.symm.injective,
    card_hypUnitriangular hF4 (r := 2) (by norm_num)]
  norm_num

@[expose] def Ssub : Subgroup SU52 := X₁sub ⊔ X₂sub ⊔ X₃sub ⊔ X₄sub

theorem mem_LTsub_of {g : SU52} (h1 : ∀ i j : Fin 5, i < j → mat g i j = 0)
    (h2 : ∀ i : Fin 5, mat g i i = 1) : g ∈ LTsub :=
  mem_LTsub.2 ⟨h1, h2⟩

theorem X₁sub_le_LTsub : X₁sub ≤ LTsub := fun g hg => by
  obtain ⟨a, b, hg⟩ := mem_X₁sub.1 hg
  refine mem_LTsub_of (fun i j hij => ?_) fun i => ?_ <;> rw [hg]
  · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
  · fin_cases i <;> rfl

theorem X₂sub_le_LTsub : X₂sub ≤ LTsub := fun g hg => by
  obtain ⟨a, hg⟩ := mem_X₂sub.1 hg
  refine mem_LTsub_of (fun i j hij => ?_) fun i => ?_ <;> rw [hg]
  · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
  · fin_cases i <;> rfl

theorem X₃sub_le_LTsub : X₃sub ≤ LTsub := fun g hg => by
  obtain ⟨a, hg⟩ := mem_X₃sub.1 hg
  refine mem_LTsub_of (fun i j hij => ?_) fun i => ?_ <;> rw [hg]
  · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
  · fin_cases i <;> rfl

theorem X₄sub_le_LTsub : X₄sub ≤ LTsub := fun g hg => by
  obtain ⟨a, b, hg⟩ := mem_X₄sub.1 hg
  refine mem_LTsub_of (fun i j hij => ?_) fun i => ?_ <;> rw [hg]
  · fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
  · fin_cases i <;> rfl

theorem Ssub_le_LTsub : Ssub ≤ LTsub :=
  sup_le (sup_le (sup_le X₁sub_le_LTsub X₂sub_le_LTsub) X₃sub_le_LTsub) X₄sub_le_LTsub

theorem nf_entries (a₁ b₁ a₂ a₃ a₄ b₄ : F4) :
    (x₁Mat a₁ b₁ * x₂Mat a₂ * x₃Mat a₃ * x₄Mat a₄ b₄) 1 0 = a₂ ∧
    (x₁Mat a₁ b₁ * x₂Mat a₂ * x₃Mat a₃ * x₄Mat a₄ b₄) 2 1 = a₁ ∧
    (x₁Mat a₁ b₁ * x₂Mat a₂ * x₃Mat a₃ * x₄Mat a₄ b₄) 3 1 = b₁ ∧
    (x₁Mat a₁ b₁ * x₂Mat a₂ * x₃Mat a₃ * x₄Mat a₄ b₄) 2 0 = a₁ * a₂ + a₄ ∧
    (x₁Mat a₁ b₁ * x₂Mat a₂ * x₃Mat a₃ * x₄Mat a₄ b₄) 3 0 = b₁ * a₂ + a₃ + bar a₁ * a₄ ∧
    (x₁Mat a₁ b₁ * x₂Mat a₂ * x₃Mat a₃ * x₄Mat a₄ b₄) 4 0 = bar a₂ * a₃ + b₄ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [x₁Mat, x₂Mat, x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five]

theorem nf_injective : Function.Injective fun p : X₁sub × X₂sub × X₃sub × X₄sub =>
    (p.1 : SU52) * p.2.1 * p.2.2.1 * p.2.2.2 := by
  rintro ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩, ⟨g₃, hg₃⟩, ⟨g₄, hg₄⟩⟩ ⟨⟨h₁, hh₁⟩, ⟨h₂, hh₂⟩, ⟨h₃, hh₃⟩,
    ⟨h₄, hh₄⟩⟩ he
  obtain ⟨a₁, b₁, eg₁⟩ := mem_X₁sub.1 hg₁
  obtain ⟨a₂, eg₂⟩ := mem_X₂sub.1 hg₂
  obtain ⟨a₃, eg₃⟩ := mem_X₃sub.1 hg₃
  obtain ⟨a₄, b₄, eg₄⟩ := mem_X₄sub.1 hg₄
  obtain ⟨c₁, d₁, eh₁⟩ := mem_X₁sub.1 hh₁
  obtain ⟨c₂, eh₂⟩ := mem_X₂sub.1 hh₂
  obtain ⟨c₃, eh₃⟩ := mem_X₃sub.1 hh₃
  obtain ⟨c₄, d₄, eh₄⟩ := mem_X₄sub.1 hh₄
  have hm := congrArg mat he
  simp only [mat_mul, eg₁, eg₂, eg₃, eg₄, eh₁, eh₂, eh₃, eh₄] at hm
  obtain ⟨p₁, p₂, p₃, p₄, p₅, p₆⟩ := nf_entries a₁ b₁ a₂ a₃ a₄ b₄
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆⟩ := nf_entries c₁ d₁ c₂ c₃ c₄ d₄
  have k₂ : a₂ = c₂ := by rw [← p₁, ← q₁, hm]
  have k₁ : a₁ = c₁ := by rw [← p₂, ← q₂, hm]
  have l₁ : b₁ = d₁ := by rw [← p₃, ← q₃, hm]
  have k₄ : a₄ = c₄ := by
    have := p₄.symm.trans ((congrFun (congrFun hm 2) 0).trans q₄)
    rw [k₁, k₂] at this
    exact add_left_cancel this
  have k₃ : a₃ = c₃ := by
    have := p₅.symm.trans ((congrFun (congrFun hm 3) 0).trans q₅)
    rw [k₁, k₂, k₄, l₁] at this
    exact add_left_cancel (add_right_cancel this)
  have l₄ : b₄ = d₄ := by
    have := p₆.symm.trans ((congrFun (congrFun hm 4) 0).trans q₆)
    rw [k₂, k₃] at this
    exact add_left_cancel this
  subst k₁ l₁ k₂ k₃ k₄ l₄
  simp only [Prod.mk.injEq, Subtype.mk.injEq]
  exact ⟨ext_mat (eg₁.trans eh₁.symm), ext_mat (eg₂.trans eh₂.symm),
    ext_mat (eg₃.trans eh₃.symm), ext_mat (eg₄.trans eh₄.symm)⟩

@[expose] noncomputable def nfMap (p : X₁sub × X₂sub × X₃sub × X₄sub) : Ssub :=
  ⟨p.1 * p.2.1 * p.2.2.1 * p.2.2.2,
    mul_mem (mul_mem (mul_mem (mem_sup_left (mem_sup_left (mem_sup_left p.1.2)))
      (mem_sup_left (mem_sup_left (mem_sup_right p.2.1.2))))
      (mem_sup_left (mem_sup_right p.2.2.1.2))) (mem_sup_right p.2.2.2.2)⟩

theorem nfMap_injective : Function.Injective nfMap := fun _ _ h =>
  nf_injective (congrArg Subtype.val h)

theorem card_Ssub : Nat.card Ssub = 2 ^ 10 := by
  refine le_antisymm (card_LTsub ▸ Subgroup.card_le_of_le Ssub_le_LTsub) ?_
  have h := Nat.card_le_card_of_injective nfMap nfMap_injective
  rwa [Nat.card_prod, Nat.card_prod, Nat.card_prod, card_X₁sub, card_X₂sub, card_X₃sub,
    card_X₄sub] at h

theorem Ssub_eq_LTsub : Ssub = LTsub :=
  Subgroup.eq_of_le_of_card_ge Ssub_le_LTsub (by rw [card_Ssub, card_LTsub])

theorem exists_sylow_Ssub : ∃ P : Sylow 2 SU52, (P : Subgroup SU52) = Ssub :=
  ⟨Sylow.ofCard Ssub (by rw [card_Ssub, card_SU52.2]), rfl⟩

theorem exists_eq_nf {g : SU52} (hg : g ∈ Ssub) :
    ∃ g₁ ∈ X₁sub, ∃ g₂ ∈ X₂sub, ∃ g₃ ∈ X₃sub, ∃ g₄ ∈ X₄sub, g = g₁ * g₂ * g₃ * g₄ := by
  have hbij : Function.Bijective nfMap := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨nfMap_injective, ?_⟩
    rw [card_Ssub, Nat.card_prod, Nat.card_prod, Nat.card_prod, card_X₁sub, card_X₂sub,
      card_X₃sub, card_X₄sub]
    norm_num
  obtain ⟨⟨g₁, g₂, g₃, g₄⟩, hp⟩ := hbij.2 ⟨g, hg⟩
  exact ⟨g₁, g₁.2, g₂, g₂.2, g₃, g₃.2, g₄, g₄.2, (congrArg Subtype.val hp).symm⟩

@[expose] def A₁sub : Subgroup SU52 := X₂sub ⊔ X₃sub ⊔ X₄sub

@[expose] def A₂sub : Subgroup SU52 := X₁sub ⊔ X₃sub ⊔ X₄sub

@[expose] def Fsub : Subgroup SU52 := ZX₁sub ⊔ X₃sub ⊔ ZX₄sub

@[expose] def K₁sub : Subgroup SU52 := X₁sub ⊔ zpowers uSU

@[expose] def K₂sub : Subgroup SU52 := X₂sub ⊔ zpowers vSU

@[expose] def K₃sub : Subgroup SU52 :=
  ZX₁sub ⊔ X₂sub ⊔ X₃sub ⊔ ZX₄sub ⊔ zpowers uSU ⊔ zpowers vSU

@[expose] def Esub : Subgroup SU52 := zpowers e₁SU ⊔ zpowers e₂SU

@[expose] def Dsub : Subgroup SU52 := zpowers uSU ⊔ zpowers vSU

theorem A₁sub_le_Ssub : A₁sub ≤ Ssub := by
  rw [A₁sub, Ssub]
  exact sup_le (sup_le (le_sup_right.trans (le_sup_left.trans le_sup_left))
    (le_sup_right.trans le_sup_left)) le_sup_right

theorem A₂sub_le_Ssub : A₂sub ≤ Ssub := by
  rw [A₂sub, Ssub]
  exact sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
    (le_sup_right.trans le_sup_left)) le_sup_right

theorem ZX₁sub_le_X₁sub : ZX₁sub ≤ X₁sub := fun _ hg => by
  obtain ⟨a, b, -, hg⟩ := mem_x₁Sub.1 hg
  exact mem_X₁sub.2 ⟨a, b, hg⟩

theorem ZX₄sub_le_X₄sub : ZX₄sub ≤ X₄sub := fun _ hg => by
  obtain ⟨a, b, -, hg⟩ := mem_x₄Sub.1 hg
  exact mem_X₄sub.2 ⟨a, b, hg⟩

theorem Fsub_le_A₂sub : Fsub ≤ A₂sub := by
  rw [Fsub, A₂sub]
  exact sup_le (sup_le (ZX₁sub_le_X₁sub.trans (le_sup_left.trans le_sup_left))
    (le_sup_right.trans le_sup_left)) (ZX₄sub_le_X₄sub.trans le_sup_right)

theorem mat_pow_two (g : SU52) : mat (g ^ 2) = mat g * mat g := by rw [pow_two, mat_mul]

theorem mat_pow_three (g : SU52) : mat (g ^ 3) = mat g * mat g * mat g := by
  rw [pow_succ, pow_two, mat_mul, mat_mul]

theorem orderOf_uSU : orderOf uSU = 2 :=
  orderOf_eq_prime (ext_mat (by rw [mat_pow_two, mat_uSU, mat_one]; decide))
    fun h => absurd (congrArg mat h) (by rw [mat_uSU, mat_one]; decide)

theorem orderOf_vSU : orderOf vSU = 2 :=
  orderOf_eq_prime (ext_mat (by rw [mat_pow_two, mat_vSU, mat_one]; decide))
    fun h => absurd (congrArg mat h) (by rw [mat_vSU, mat_one]; decide)

theorem orderOf_e₁SU : orderOf e₁SU = 3 :=
  orderOf_eq_prime (ext_mat (by rw [mat_pow_three, mat_e₁SU, mat_one]; decide))
    fun h => absurd (congrArg mat h) (by rw [mat_e₁SU, mat_one]; decide)

theorem orderOf_e₂SU : orderOf e₂SU = 3 :=
  orderOf_eq_prime (ext_mat (by rw [mat_pow_three, mat_e₂SU, mat_one]; decide))
    fun h => absurd (congrArg mat h) (by rw [mat_e₂SU, mat_one]; decide)

theorem e₁SU_mul_e₂SU : e₁SU * e₂SU = e₂SU * e₁SU :=
  ext_mat (by rw [mat_mul, mat_mul, mat_e₁SU, mat_e₂SU]; decide)

theorem mem_Ssub {g : SU52} :
    g ∈ Ssub ↔ (∀ i j : Fin 5, i < j → mat g i j = 0) ∧ ∀ i : Fin 5, mat g i i = 1 := by
  rw [Ssub_eq_LTsub, mem_LTsub]

theorem mat_mul_one_zero {g h : SU52} (hg : g ∈ Ssub) (hh : h ∈ Ssub) :
    mat (g * h) 1 0 = mat g 1 0 + mat h 1 0 := by
  obtain ⟨g1, g2⟩ := mem_Ssub.1 hg
  obtain ⟨h1, h2⟩ := mem_Ssub.1 hh
  rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_five, g1 1 2 (by decide), g1 1 3 (by decide),
    g1 1 4 (by decide), h2 0, g2 1]
  ring

theorem mat_mul_two_one {g h : SU52} (hg : g ∈ Ssub) (hh : h ∈ Ssub) :
    mat (g * h) 2 1 = mat g 2 1 + mat h 2 1 := by
  obtain ⟨g1, g2⟩ := mem_Ssub.1 hg
  obtain ⟨h1, h2⟩ := mem_Ssub.1 hh
  rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_five, g1 2 3 (by decide), g1 2 4 (by decide),
    h1 0 1 (by decide), h2 1, g2 2]
  ring

theorem mat_mul_three_one {g h : SU52} (hg : g ∈ Ssub) (hh : h ∈ Ssub) :
    mat (g * h) 3 1 = mat g 3 1 + mat g 3 2 * mat h 2 1 + mat h 3 1 := by
  obtain ⟨g1, g2⟩ := mem_Ssub.1 hg
  obtain ⟨h1, h2⟩ := mem_Ssub.1 hh
  rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_five, g1 3 4 (by decide), h1 0 1 (by decide),
    h2 1, g2 3]
  ring

theorem mat_mul_two_zero {g h : SU52} (hg : g ∈ Ssub) (hh : h ∈ Ssub) :
    mat (g * h) 2 0 = mat g 2 0 + mat g 2 1 * mat h 1 0 + mat h 2 0 := by
  obtain ⟨g1, g2⟩ := mem_Ssub.1 hg
  obtain ⟨h1, h2⟩ := mem_Ssub.1 hh
  rw [mat_mul, Matrix.mul_apply, Fin.sum_univ_five, g1 2 3 (by decide), g1 2 4 (by decide),
    h2 0, g2 2]
  ring

theorem inv_entry_eq_zero {g : SU52} {i j : Fin 5} (hij : i ≠ j)
    (hadd : mat (g * g⁻¹) i j = mat g i j + mat g⁻¹ i j) (h0 : mat g i j = 0) :
    mat g⁻¹ i j = 0 := by
  rw [mul_inv_cancel, mat_one, Matrix.one_apply_ne hij, h0, zero_add] at hadd
  exact hadd.symm

@[expose] def T₂sub : Subgroup SU52 where
  carrier := {g | g ∈ Ssub ∧ mat g 1 0 = 0}
  mul_mem' := fun {g h} ⟨hg, hg0⟩ ⟨hh, hh0⟩ =>
    ⟨mul_mem hg hh, by rw [mat_mul_one_zero hg hh, hg0, hh0, add_zero]⟩
  one_mem' := ⟨one_mem _, rfl⟩
  inv_mem' := fun {g} ⟨hg, hg0⟩ =>
    ⟨inv_mem hg, inv_entry_eq_zero (by decide) (mat_mul_one_zero hg (inv_mem hg)) hg0⟩

@[expose] def T₁sub : Subgroup SU52 where
  carrier := {g | g ∈ Ssub ∧ mat g 2 1 = 0 ∧ mat g 3 1 = 0}
  mul_mem' := fun {g h} ⟨hg, hg0, hg1⟩ ⟨hh, hh0, hh1⟩ =>
    ⟨mul_mem hg hh, by rw [mat_mul_two_one hg hh, hg0, hh0, add_zero],
      by rw [mat_mul_three_one hg hh, hg1, hh0, hh1, mul_zero, add_zero, add_zero]⟩
  one_mem' := ⟨one_mem _, rfl, rfl⟩
  inv_mem' := fun {g} ⟨hg, hg0, hg1⟩ => by
    have hi0 := inv_entry_eq_zero (by decide) (mat_mul_two_one hg (inv_mem hg)) hg0
    refine ⟨inv_mem hg, hi0, inv_entry_eq_zero (by decide) ?_ hg1⟩
    rw [mat_mul_three_one hg (inv_mem hg), hi0, mul_zero, add_zero]

@[expose] def TFsub : Subgroup SU52 where
  carrier := {g | g ∈ Ssub ∧ mat g 2 1 = 0 ∧ mat g 1 0 = 0 ∧ mat g 2 0 = 0}
  mul_mem' := fun {g h} ⟨hg, hg0, hg1, hg2⟩ ⟨hh, hh0, hh1, hh2⟩ =>
    ⟨mul_mem hg hh, by rw [mat_mul_two_one hg hh, hg0, hh0, add_zero],
      by rw [mat_mul_one_zero hg hh, hg1, hh1, add_zero],
      by rw [mat_mul_two_zero hg hh, hg2, hg0, hh2, zero_mul, add_zero, add_zero]⟩
  one_mem' := ⟨one_mem _, rfl, rfl, rfl⟩
  inv_mem' := fun {g} ⟨hg, hg0, hg1, hg2⟩ => by
    refine ⟨inv_mem hg, inv_entry_eq_zero (by decide) (mat_mul_two_one hg (inv_mem hg)) hg0,
      inv_entry_eq_zero (by decide) (mat_mul_one_zero hg (inv_mem hg)) hg1,
      inv_entry_eq_zero (by decide) ?_ hg2⟩
    rw [mat_mul_two_zero hg (inv_mem hg), hg0, zero_mul, add_zero]

theorem card_of_nf {H Y₁ Y₂ Y₃ Y₄ : Subgroup SU52} (h₁ : Y₁ ≤ X₁sub) (h₂ : Y₂ ≤ X₂sub)
    (h₃ : Y₃ ≤ X₃sub) (h₄ : Y₄ ≤ X₄sub)
    (hmem : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, ∀ y₃ ∈ Y₃, ∀ y₄ ∈ Y₄, y₁ * y₂ * y₃ * y₄ ∈ H)
    (hsurj : ∀ g ∈ H, ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, ∃ y₃ ∈ Y₃, ∃ y₄ ∈ Y₄, g = y₁ * y₂ * y₃ * y₄) :
    Nat.card H = Nat.card Y₁ * (Nat.card Y₂ * (Nat.card Y₃ * Nat.card Y₄)) := by
  rw [← Nat.card_prod, ← Nat.card_prod, ← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p : Y₁ × Y₂ × Y₃ × Y₄ =>
    (⟨p.1 * p.2.1 * p.2.2.1 * p.2.2.2, hmem _ p.1.2 _ p.2.1.2 _ p.2.2.1.2 _ p.2.2.2.2⟩ : H))
    ⟨fun p q hpq => ?_, fun g => ?_⟩)
  · have := @nf_injective ⟨⟨p.1, h₁ p.1.2⟩, ⟨p.2.1, h₂ p.2.1.2⟩, ⟨p.2.2.1, h₃ p.2.2.1.2⟩,
      ⟨p.2.2.2, h₄ p.2.2.2.2⟩⟩ ⟨⟨q.1, h₁ q.1.2⟩, ⟨q.2.1, h₂ q.2.1.2⟩, ⟨q.2.2.1, h₃ q.2.2.1.2⟩,
      ⟨q.2.2.2, h₄ q.2.2.2.2⟩⟩ (congrArg Subtype.val hpq)
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at this
    obtain ⟨e₁, e₂, e₃, e₄⟩ := this
    exact Prod.ext (Subtype.ext e₁) (Prod.ext (Subtype.ext e₂) (Prod.ext (Subtype.ext e₃)
      (Subtype.ext e₄)))
  · obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, y₄, hy₄, hg⟩ := hsurj g g.2
    exact ⟨⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, ⟨y₃, hy₃⟩, ⟨y₄, hy₄⟩⟩, Subtype.ext hg.symm⟩

theorem exists_eq_nf_coord {g : SU52} (hg : g ∈ Ssub) :
    ∃ (a₁ b₁ a₂ a₃ a₄ b₄ : F4) (g₁ g₂ g₃ g₄ : SU52), mat g₁ = x₁Mat a₁ b₁ ∧
      mat g₂ = x₂Mat a₂ ∧ mat g₃ = x₃Mat a₃ ∧ mat g₄ = x₄Mat a₄ b₄ ∧ g = g₁ * g₂ * g₃ * g₄ ∧
      mat g 1 0 = a₂ ∧ mat g 2 1 = a₁ ∧ mat g 3 1 = b₁ ∧ mat g 2 0 = a₁ * a₂ + a₄ := by
  obtain ⟨g₁, hg₁, g₂, hg₂, g₃, hg₃, g₄, hg₄, rfl⟩ := exists_eq_nf hg
  obtain ⟨a₁, b₁, e₁⟩ := mem_X₁sub.1 hg₁
  obtain ⟨a₂, e₂⟩ := mem_X₂sub.1 hg₂
  obtain ⟨a₃, e₃⟩ := mem_X₃sub.1 hg₃
  obtain ⟨a₄, b₄, e₄⟩ := mem_X₄sub.1 hg₄
  obtain ⟨p₁, p₂, p₃, p₄, -, -⟩ := nf_entries a₁ b₁ a₂ a₃ a₄ b₄
  have hm : mat (g₁ * g₂ * g₃ * g₄) = x₁Mat a₁ b₁ * x₂Mat a₂ * x₃Mat a₃ * x₄Mat a₄ b₄ := by
    rw [mat_mul, mat_mul, mat_mul, e₁, e₂, e₃, e₄]
  exact ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, hm ▸ p₁, hm ▸ p₂,
    hm ▸ p₃, hm ▸ p₄⟩

theorem eq_one_of_x₂ {g : SU52} (hg : mat g = x₂Mat 0) : g = 1 :=
  ext_mat (by rw [hg, x₂Mat_zero, mat_one])

theorem eq_one_of_x₁ {g : SU52} (hg : mat g = x₁Mat 0 0) : g = 1 :=
  ext_mat (by rw [hg, x₁Mat_zero, mat_one])

theorem mem_A₂sub {g : SU52} : g ∈ A₂sub ↔ g ∈ Ssub ∧ mat g 1 0 = 0 := by
  constructor
  · intro hg
    have hle : A₂sub ≤ T₂sub := by
      rw [A₂sub]
      refine sup_le (sup_le ?_ ?_) ?_ <;> intro x hx
      · obtain ⟨a, b, hx⟩ := mem_X₁sub.1 hx
        exact ⟨mem_sup_left (mem_sup_left (mem_sup_left (mem_X₁sub.2 ⟨a, b, hx⟩))),
          by rw [hx]; rfl⟩
      · obtain ⟨a, hx⟩ := mem_X₃sub.1 hx
        exact ⟨mem_sup_left (mem_sup_right (mem_X₃sub.2 ⟨a, hx⟩)), by rw [hx]; rfl⟩
      · obtain ⟨a, b, hx⟩ := mem_X₄sub.1 hx
        exact ⟨mem_sup_right (mem_X₄sub.2 ⟨a, b, hx⟩), by rw [hx]; rfl⟩
    exact hle hg
  · rintro ⟨hg, h0⟩
    obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, k₂, -, -, -⟩ :=
      exists_eq_nf_coord hg
    rw [h0] at k₂
    rw [← k₂] at e₂
    rw [eq_one_of_x₂ e₂, mul_one]
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left (mem_X₁sub.2 ⟨a₁, b₁, e₁⟩)))
      (mem_sup_left (mem_sup_right (mem_X₃sub.2 ⟨a₃, e₃⟩))))
      (mem_sup_right (mem_X₄sub.2 ⟨a₄, b₄, e₄⟩))

theorem mem_A₁sub {g : SU52} : g ∈ A₁sub ↔ g ∈ Ssub ∧ mat g 2 1 = 0 ∧ mat g 3 1 = 0 := by
  constructor
  · intro hg
    have hle : A₁sub ≤ T₁sub := by
      rw [A₁sub]
      refine sup_le (sup_le ?_ ?_) ?_ <;> intro x hx
      · obtain ⟨a, hx⟩ := mem_X₂sub.1 hx
        exact ⟨mem_sup_left (mem_sup_left (mem_sup_right (mem_X₂sub.2 ⟨a, hx⟩))),
          by rw [hx]; rfl, by rw [hx]; rfl⟩
      · obtain ⟨a, hx⟩ := mem_X₃sub.1 hx
        exact ⟨mem_sup_left (mem_sup_right (mem_X₃sub.2 ⟨a, hx⟩)), by rw [hx]; rfl,
          by rw [hx]; rfl⟩
      · obtain ⟨a, b, hx⟩ := mem_X₄sub.1 hx
        exact ⟨mem_sup_right (mem_X₄sub.2 ⟨a, b, hx⟩), by rw [hx]; rfl, by rw [hx]; rfl⟩
    exact hle hg
  · rintro ⟨hg, h0, h1⟩
    obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, -, k₁, l₁, -⟩ :=
      exists_eq_nf_coord hg
    rw [h0] at k₁
    rw [h1] at l₁
    rw [← k₁, ← l₁] at e₁
    rw [eq_one_of_x₁ e₁, one_mul]
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left (mem_X₂sub.2 ⟨a₂, e₂⟩)))
      (mem_sup_left (mem_sup_right (mem_X₃sub.2 ⟨a₃, e₃⟩))))
      (mem_sup_right (mem_X₄sub.2 ⟨a₄, b₄, e₄⟩))

theorem mem_Fsub {g : SU52} :
    g ∈ Fsub ↔ g ∈ Ssub ∧ mat g 2 1 = 0 ∧ mat g 1 0 = 0 ∧ mat g 2 0 = 0 := by
  constructor
  · intro hg
    have hle : Fsub ≤ TFsub := by
      rw [Fsub]
      refine sup_le (sup_le ?_ ?_) ?_ <;> intro x hx
      · obtain ⟨a, b, ha, hx'⟩ := mem_x₁Sub.1 hx
        subst ha
        exact ⟨mem_sup_left (mem_sup_left (mem_sup_left (ZX₁sub_le_X₁sub hx))),
          by rw [hx']; rfl, by rw [hx']; rfl, by rw [hx']; rfl⟩
      · obtain ⟨a, hx'⟩ := mem_X₃sub.1 hx
        exact ⟨mem_sup_left (mem_sup_right hx), by rw [hx']; rfl, by rw [hx']; rfl,
          by rw [hx']; rfl⟩
      · obtain ⟨a, b, ha, hx'⟩ := mem_x₄Sub.1 hx
        subst ha
        exact ⟨mem_sup_right (ZX₄sub_le_X₄sub hx), by rw [hx']; rfl, by rw [hx']; rfl,
          by rw [hx']; rfl⟩
    exact hle hg
  · rintro ⟨hg, h0, h1, h2⟩
    obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, k₂, k₁, -, k₄⟩ :=
      exists_eq_nf_coord hg
    rw [h1] at k₂
    rw [h0] at k₁
    rw [← k₂] at e₂ k₄
    rw [← k₁, h2, mul_zero, zero_add] at k₄
    rw [← k₁] at e₁
    rw [← k₄] at e₄
    rw [eq_one_of_x₂ e₂, mul_one]
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left (mem_x₁Sub.2 ⟨0, b₁, rfl, e₁⟩)))
      (mem_sup_left (mem_sup_right (mem_X₃sub.2 ⟨a₃, e₃⟩))))
      (mem_sup_right (mem_x₄Sub.2 ⟨0, b₄, rfl, e₄⟩))

theorem card_A₂sub : Nat.card A₂sub = 2 ^ 8 := by
  have h := card_of_nf (H := A₂sub) (Y₂ := ⊥) le_rfl bot_le le_rfl le_rfl
    (fun y₁ hy₁ y₂ hy₂ y₃ hy₃ y₄ hy₄ => by
      rw [Subgroup.mem_bot.1 hy₂, mul_one]
      exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hy₁))
        (mem_sup_left (mem_sup_right hy₃))) (mem_sup_right hy₄))
    (fun g hg => by
      obtain ⟨hgS, h0⟩ := mem_A₂sub.1 hg
      obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, k₂, -, -, -⟩ :=
        exists_eq_nf_coord hgS
      rw [h0] at k₂
      rw [← k₂] at e₂
      exact ⟨g₁, mem_X₁sub.2 ⟨a₁, b₁, e₁⟩, g₂, Subgroup.mem_bot.2 (eq_one_of_x₂ e₂), g₃,
        mem_X₃sub.2 ⟨a₃, e₃⟩, g₄, mem_X₄sub.2 ⟨a₄, b₄, e₄⟩, rfl⟩)
  rw [h, card_X₁sub, Subgroup.card_bot, card_X₃sub, card_X₄sub]
  norm_num

theorem card_A₁sub : Nat.card A₁sub = 2 ^ 7 := by
  have h := card_of_nf (H := A₁sub) (Y₁ := ⊥) bot_le le_rfl le_rfl le_rfl
    (fun y₁ hy₁ y₂ hy₂ y₃ hy₃ y₄ hy₄ => by
      rw [Subgroup.mem_bot.1 hy₁, one_mul]
      exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hy₂))
        (mem_sup_left (mem_sup_right hy₃))) (mem_sup_right hy₄))
    (fun g hg => by
      obtain ⟨hgS, h0, h1⟩ := mem_A₁sub.1 hg
      obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, -, k₁, l₁, -⟩ :=
        exists_eq_nf_coord hgS
      rw [h0] at k₁
      rw [h1] at l₁
      rw [← k₁, ← l₁] at e₁
      exact ⟨g₁, Subgroup.mem_bot.2 (eq_one_of_x₁ e₁), g₂, mem_X₂sub.2 ⟨a₂, e₂⟩, g₃,
        mem_X₃sub.2 ⟨a₃, e₃⟩, g₄, mem_X₄sub.2 ⟨a₄, b₄, e₄⟩, rfl⟩)
  rw [h, Subgroup.card_bot, card_X₂sub, card_X₃sub, card_X₄sub]
  norm_num

theorem card_Fsub : Nat.card Fsub = 2 ^ 4 := by
  have h := card_of_nf (H := Fsub) (Y₂ := ⊥) ZX₁sub_le_X₁sub bot_le le_rfl ZX₄sub_le_X₄sub
    (fun y₁ hy₁ y₂ hy₂ y₃ hy₃ y₄ hy₄ => by
      rw [Subgroup.mem_bot.1 hy₂, mul_one]
      exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hy₁))
        (mem_sup_left (mem_sup_right hy₃))) (mem_sup_right hy₄))
    (fun g hg => by
      obtain ⟨hgS, h0, h1, h2⟩ := mem_Fsub.1 hg
      obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, k₂, k₁, -, k₄⟩ :=
        exists_eq_nf_coord hgS
      rw [h1] at k₂
      rw [h0] at k₁
      rw [← k₂] at e₂ k₄
      rw [← k₁, h2, mul_zero, zero_add] at k₄
      rw [← k₁] at e₁
      rw [← k₄] at e₄
      exact ⟨g₁, mem_x₁Sub.2 ⟨0, b₁, rfl, e₁⟩, g₂, Subgroup.mem_bot.2 (eq_one_of_x₂ e₂), g₃,
        mem_X₃sub.2 ⟨a₃, e₃⟩, g₄, mem_x₄Sub.2 ⟨0, b₄, rfl, e₄⟩, rfl⟩)
  rw [h, card_ZX₁sub, Subgroup.card_bot, card_X₃sub, card_ZX₄sub]
  norm_num

theorem map_bar_unitary {M : Matrix (Fin 5) (Fin 5) F4} (h : (M.map bar)ᵀ * J5 * M = J5) :
    ((M.map bar).map bar)ᵀ * J5 * M.map bar = J5 := by
  have h' := congrArg (fun N => N.map bar) h
  simp only [Matrix.map_mul, Matrix.transpose_map, J5_map_bar] at h'
  exact h'

theorem det_map_bar {M : Matrix (Fin 5) (Fin 5) F4} (h : M.det = 1) : (M.map bar).det = 1 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_one]

theorem map_bar_map_bar (M : Matrix (Fin 5) (Fin 5) F4) : (M.map bar).map bar = M := by
  ext i j
  simp only [Matrix.map_apply, bar_bar]

@[expose] def fldFun (g : SU52) : SU52 :=
  mkSU ((mat g).map bar) (map_bar_unitary (mem_SU52.1 g.2).1) (det_map_bar (mem_SU52.1 g.2).2)

theorem mat_fldFun (g : SU52) : mat (fldFun g) = (mat g).map bar := rfl

theorem fldFun_fldFun (g : SU52) : fldFun (fldFun g) = g :=
  ext_mat (by rw [mat_fldFun, mat_fldFun, map_bar_map_bar])

@[expose] def fld : MulAut SU52 where
  toFun := fldFun
  invFun := fldFun
  left_inv := fldFun_fldFun
  right_inv := fldFun_fldFun
  map_mul' g g' := ext_mat (by rw [mat_fldFun, mat_mul, mat_mul, mat_fldFun, mat_fldFun,
    Matrix.map_mul])

@[simp] theorem mat_fld (g : SU52) : mat (fld g) = (mat g).map bar := rfl

theorem fld_fld (g : SU52) : fld (fld g) = g := fldFun_fldFun g

theorem x₁Mat_map_bar (a b : F4) : (x₁Mat a b).map bar = x₁Mat (bar a) (bar b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x₁Mat]

theorem x₂Mat_map_bar (a : F4) : (x₂Mat a).map bar = x₂Mat (bar a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x₂Mat]

theorem x₃Mat_map_bar (a : F4) : (x₃Mat a).map bar = x₃Mat (bar a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x₃Mat]

theorem x₄Mat_map_bar (a b : F4) : (x₄Mat a b).map bar = x₄Mat (bar a) (bar b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x₄Mat]

theorem fld_x₁SU (a b : F4) (h : a * bar a = b + bar b) :
    fld (x₁SU a b h) = x₁SU (bar a) (bar b) (by rw [bar_bar, bar_bar, mul_comm, h, add_comm]) :=
  ext_mat (x₁Mat_map_bar a b)

theorem fld_x₂SU (a : F4) : fld (x₂SU a) = x₂SU (bar a) := ext_mat (x₂Mat_map_bar a)

theorem fld_x₃SU (a : F4) : fld (x₃SU a) = x₃SU (bar a) := ext_mat (x₃Mat_map_bar a)

theorem fld_x₄SU (a b : F4) (h : a * bar a = b + bar b) :
    fld (x₄SU a b h) = x₄SU (bar a) (bar b) (by rw [bar_bar, bar_bar, mul_comm, h, add_comm]) :=
  ext_mat (x₄Mat_map_bar a b)

theorem fld_uSU : fld uSU = uSU := ext_mat (by rw [mat_fld, mat_uSU]; decide)

theorem fld_vSU : fld vSU = vSU := ext_mat (by rw [mat_fld, mat_vSU]; decide)

theorem fld_e₁SU : fld e₁SU = e₁SU⁻¹ := ext_mat (by rw [mat_fld, mat_inv, mat_e₁SU]; decide)

theorem fld_e₂SU : fld e₂SU = e₂SU⁻¹ := ext_mat (by rw [mat_fld, mat_inv, mat_e₂SU]; decide)

@[expose] def CfldSub : Subgroup SU52 := MonoidHom.eqLocus fld.toMonoidHom (MonoidHom.id SU52)

theorem mem_CfldSub {g : SU52} : g ∈ CfldSub ↔ fld g = g := Iff.rfl

@[expose] def B₁sub : Subgroup SU52 := A₁sub ⊓ CfldSub

@[expose] def B₂sub : Subgroup SU52 := A₂sub ⊓ CfldSub

@[expose] def wittMat : Matrix (Fin 5) (Fin 5) F4 :=
  !![1, 0, 0, 0, F4.ω; 1, 0, 0, 0, F4.ω + 1; 0, 1, 0, F4.ω, 0; 0, 1, 0, F4.ω + 1, 0;
    0, 0, 1, 0, 0]

@[expose] def wittInv : Matrix (Fin 5) (Fin 5) F4 :=
  !![F4.ω + 1, F4.ω, 0, 0, 0; 0, 0, F4.ω + 1, F4.ω, 0; 0, 0, 0, 0, 1; 0, 0, 1, 1, 0;
    1, 1, 0, 0, 0]

theorem wittMat_mul_wittInv : wittMat * wittInv = 1 := by decide

theorem wittInv_mul_wittMat : wittInv * wittMat = 1 := by decide

theorem wittMat_form : (wittMat.map bar)ᵀ * wittMat = J5 := by decide

theorem wittInv_form : (wittInv.map bar)ᵀ * J5 * wittInv = 1 := by decide

theorem wittInv_map_wittMat_map : (wittInv.map bar)ᵀ * (wittMat.map bar)ᵀ = 1 := by decide

theorem wittInv_form_assoc (X : Matrix (Fin 5) (Fin 5) F4) :
    (wittInv.map bar)ᵀ * (J5 * (wittInv * X)) = X := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, wittInv_form, Matrix.one_mul]

theorem unitary_one_iff (A : Matrix (Fin 5) (Fin 5) F4) :
    (A.map bar)ᵀ * A = 1 ↔
      ((wittInv * A * wittMat).map bar)ᵀ * J5 * (wittInv * A * wittMat) = J5 := by
  have key : ((wittInv * A * wittMat).map bar)ᵀ * J5 * (wittInv * A * wittMat) =
      (wittMat.map bar)ᵀ * ((A.map bar)ᵀ * A) * wittMat := by
    simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [wittInv_form_assoc]
  rw [key]
  constructor
  · intro h
    rw [h, Matrix.mul_one, wittMat_form]
  · intro h
    calc (A.map bar)ᵀ * A =
          ((wittInv.map bar)ᵀ * (wittMat.map bar)ᵀ) * ((A.map bar)ᵀ * A) *
            (wittMat * wittInv) := by
          rw [wittInv_map_wittMat_map, wittMat_mul_wittInv, Matrix.one_mul, Matrix.mul_one]
      _ = (wittInv.map bar)ᵀ * ((wittMat.map bar)ᵀ * ((A.map bar)ᵀ * A) * wittMat) *
            wittInv := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, wittInv_form]

@[expose] def wittGL : GL (Fin 5) F4 :=
  ⟨wittMat, wittInv, wittMat_mul_wittInv, wittInv_mul_wittMat⟩

section Transport

open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] noncomputable def wittTransport (φ : K ≃+* F4) : GL (Fin 5) K ≃* GL (Fin 5) F4 :=
  (Units.mapEquiv (RingEquiv.mapMatrix φ).toMulEquiv).trans (MulAut.conj wittGL⁻¹)

theorem coe_wittTransport (φ : K ≃+* F4) (A : GL (Fin 5) K) :
    ((wittTransport φ A : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) =
      wittInv * (A : Matrix (Fin 5) (Fin 5) K).map φ * wittMat := rfl

theorem map_map_bar (φ : K ≃+* F4) (A : Matrix (Fin 5) (Fin 5) K) :
    (A.map φ).map bar = (A.map fun x => x ^ 2 ^ 1).map φ := by
  ext i j
  simp only [Matrix.map_apply, bar_apply, pow_one, map_pow]

theorem map_wittTransport (hK : Nat.card K = (2 ^ 1) ^ 2) (φ : K ≃+* F4) :
    (StatedSU 5 (2 ^ 1) K).map (wittTransport φ).toMonoidHom = SU52 := by
  have hset := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := 5)
    (by norm_num)).1
  have hU : ∀ A : Matrix (Fin 5) (Fin 5) K,
      (A.map fun x => x ^ 2 ^ 1)ᵀ * A = 1 ↔ ((A.map φ).map bar)ᵀ * A.map φ = 1 := by
    intro A
    have e : ((A.map φ).map bar)ᵀ * A.map φ = ((A.map fun x => x ^ 2 ^ 1)ᵀ * A).map φ := by
      ext i j
      simp [Matrix.mul_apply, map_sum, bar_apply]
    rw [e]
    constructor
    · intro h
      rw [h, Matrix.map_one _ (map_zero φ) (map_one φ)]
    · intro h
      apply Matrix.map_injective φ.injective
      change ((A.map fun x => x ^ 2 ^ 1)ᵀ * A).map φ = (1 : Matrix (Fin 5) (Fin 5) K).map φ
      rw [h, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hdet : ∀ A : Matrix (Fin 5) (Fin 5) K, (A.map φ).det = φ A.det := fun A => by
    rw [← RingHom.coe_coe φ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    have hA' : A ∈ (StatedSU 5 (2 ^ 1) K : Set (GL (Fin 5) K)) := hA
    rw [hset] at hA'
    refine mem_SU52.2 ⟨?_, ?_⟩
    · exact (unitary_one_iff _).1 ((hU _).1 hA'.2)
    · change (wittInv * (A : Matrix (Fin 5) (Fin 5) K).map φ * wittMat).det = 1
      rw [Matrix.det_mul, Matrix.det_mul, hdet, hA'.1, map_one, mul_one, ← Matrix.det_mul,
        wittInv_mul_wittMat, Matrix.det_one]
  · intro hB
    obtain ⟨hB1, hB2⟩ := mem_SU52.1 hB
    set A₀ : Matrix (Fin 5) (Fin 5) F4 := wittMat * (B : Matrix (Fin 5) (Fin 5) F4) * wittInv
    have hA₀ : wittInv * A₀ * wittMat = B := by
      simp only [A₀, ← Matrix.mul_assoc, wittInv_mul_wittMat, Matrix.one_mul]
      rw [Matrix.mul_assoc, wittInv_mul_wittMat, Matrix.mul_one]
    have hφ : (A₀.map φ.symm).map φ = A₀ := by
      ext i j
      simp only [Matrix.map_apply, RingEquiv.apply_symm_apply]
    have hdet₀ : (A₀.map φ.symm).det = 1 := by
      rw [← φ.injective.eq_iff, ← hdet, hφ, map_one, Matrix.det_mul, Matrix.det_mul, hB2,
        mul_one, ← Matrix.det_mul, wittMat_mul_wittInv, Matrix.det_one]
    let A : GL (Fin 5) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (A₀.map φ.symm)
      (by rw [hdet₀]; exact one_ne_zero)
    have hAmat : (A : Matrix (Fin 5) (Fin 5) K) = A₀.map φ.symm := rfl
    refine ⟨A, ?_, Units.ext ?_⟩
    · rw [hset]
      refine ⟨by rw [hAmat, hdet₀], (hU _).2 ?_⟩
      rw [hAmat, hφ]
      exact (unitary_one_iff A₀).2 (by rw [hA₀]; exact hB1)
    · change wittInv * (A : Matrix (Fin 5) (Fin 5) K).map φ * wittMat = B
      rw [hAmat, hφ, hA₀]

theorem statedScalars_subgroupOf_eq_bot (hK : Nat.card K = (2 ^ 1) ^ 2) :
    (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 1) K) = ⊥ := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := 5)
    (by norm_num)).2.2
  rw [← Subgroup.card_eq_one, h]
  norm_num

@[expose] noncomputable def statedProjEquiv [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    StatedProj (StatedSU 5 (2 ^ 1) K) ≃* SU52 :=
  have : Fintype K := Fintype.ofFinite K
  ((QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_eq_bot hK)).trans
    QuotientGroup.quotientBot).trans
    (((StatedSU 5 (2 ^ 1) K).equivMapOfInjective _
      (wittTransport (FiniteField.ringEquivOfCardEq (by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
          Nat.card_eq_fintype_card, F4.card]; norm_num))).injective).trans
      (MulEquiv.subgroupCongr (map_wittTransport hK _)))

end Transport

theorem modelEquiv {J : Type} [Group J] (hJ : CFSG.Blueprint.LieModel J .PSU 5 2 1) :
    Nonempty (J ≃* SU52) := by
  rcases hJ with ⟨-, -, K, _, _, hcard, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact ⟨e.trans (statedProjEquiv hcard)⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem lieModel_SU52 : CFSG.Blueprint.LieModel SU52 .PSU 5 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, F4, inferInstance,
    inferInstance, by rw [Nat.card_eq_fintype_card, F4.card]; norm_num,
    ⟨(statedProjEquiv (by rw [Nat.card_eq_fintype_card, F4.card]; norm_num)).symm⟩⟩

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
