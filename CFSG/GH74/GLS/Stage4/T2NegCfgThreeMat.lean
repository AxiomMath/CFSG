module

public import CFSG.GH74.GLS.Stage4.T2NegCfgThreeDefs
public import CFSG.GH74.GLS.Stage4.T2NegCfgOne

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

section Mat

variable {F : Type} [Field F]

theorem negF_sq_add_sq [Finite F] (hodd : Odd (Nat.card F)) (c : F) :
    ∃ a b : F, a * a + b * b = c := by
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]; exact Nat.odd_iff.1 hodd
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 - Polynomial.C c)
    (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_sub_C (by decide) _) hcard
  refine ⟨a, b, ?_⟩
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C] at hab
  linear_combination hab

theorem negF_exists_W : ∃ W : SL2 F, (W : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] :=
  ⟨⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩, rfl⟩

theorem negF_exists_V {a b : F} (h : a * a + b * b = -1) :
    ∃ V : SL2 F, (V : Matrix (Fin 2) (Fin 2) F) = !![a, b; b, -a] :=
  ⟨⟨!![a, b; b, -a], by rw [Matrix.det_fin_two_of]; linear_combination -h⟩, rfl⟩

theorem negF_sq_W {W : SL2 F} (hW : (W : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0]) :
    W * W = negOne F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, hW, coe_negOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem negF_sq_V {a b : F} (h : a * a + b * b = -1) {V : SL2 F}
    (hV : (V : Matrix (Fin 2) (Fin 2) F) = !![a, b; b, -a]) : V * V = negOne F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, hV, coe_negOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · exact h
  · ring
  · ring
  · linear_combination h

theorem negF_anti {a b : F} {W V : SL2 F}
    (hW : (W : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0])
    (hV : (V : Matrix (Fin 2) (Fin 2) F) = !![a, b; b, -a]) :
    (W : Matrix (Fin 2) (Fin 2) F) * (V : Matrix (Fin 2) (Fin 2) F) =
      -((V : Matrix (Fin 2) (Fin 2) F) * (W : Matrix (Fin 2) (Fin 2) F)) := by
  rw [hW, hV]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem negF_W_nonscalar {W : SL2 F} (hW : (W : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0]) :
    ¬ ∃ s : F, ((Matrix.SpecialLinearGroup.toGL W : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      s • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rintro ⟨s, hs⟩
  have h := congrFun (congrFun hs 0) 1
  simp [hW] at h

theorem negF_mem_cent {W Y : SL2 F} :
    Y ∈ Subgroup.centralizer ({W} : Set (SL2 F)) ↔
      (Y : Matrix (Fin 2) (Fin 2) F) * (W : Matrix (Fin 2) (Fin 2) F) =
        (W : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    simpa using congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F)) h
  · intro h
    exact Subtype.ext (by simpa using h)

theorem negF_T_inv (h2 : (2 : F) ≠ 0) {a b : F} {W V : SL2 F}
    (hW : (W : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0])
    (hV : (V : Matrix (Fin 2) (Fin 2) F) = !![a, b; b, -a]) (hVV : V * V = negOne F) :
    ∀ Y ∈ Subgroup.centralizer ({W} : Set (SL2 F)), V * Y * V⁻¹ = Y⁻¹ := by
  intro Y hY
  have hYW := (negF_mem_cent.1 hY).symm
  refine t2H_inv_of_anticomm h2 (Matrix.SpecialLinearGroup.toGL W) (-1) ?_
    (negF_W_nonscalar hW) V Y hVV ?_ hYW
  · have h : (W : Matrix (Fin 2) (Fin 2) F) * (W : Matrix (Fin 2) (Fin 2) F) = -1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, negF_sq_W hW, t2B_negOne_eq]
    change (W : Matrix (Fin 2) (Fin 2) F) * (W : Matrix (Fin 2) (Fin 2) F) = (-1 : F) • 1
    rw [h]
    simp
  · exact negF_anti hW hV

theorem negF_VW (h2 : (2 : F) ≠ 0) {a b : F} {W V : SL2 F}
    (hW : (W : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0])
    (hV : (V : Matrix (Fin 2) (Fin 2) F) = !![a, b; b, -a]) (hVV : V * V = negOne F) :
    V * W * V⁻¹ = W⁻¹ :=
  negF_T_inv h2 hW hV hVV W (Subgroup.mem_centralizer_singleton_iff.2 rfl)

theorem negF_T_cent {W : SL2 F} :
    ∀ Y ∈ Subgroup.centralizer ({W} : Set (SL2 F)), Y * Y ≠ 1 → ∀ D : SL2 F,
      D * Y = Y * D → D ∈ Subgroup.centralizer ({W} : Set (SL2 F)) := by
  intro Y hY hYY D hDY
  have hDY' : (D : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F) =
      (Y : Matrix (Fin 2) (Fin 2) F) * (D : Matrix (Fin 2) (Fin 2) F) := by
    simpa using congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F)) hDY
  have hWY := negF_mem_cent.1 hY
  have key := t2N_comm_of_nonscalar (t2N_nonscalar hYY) hDY' hWY.symm
  exact negF_mem_cent.2 key

theorem negF_T_cyc_card [Finite F] {q : ℕ} (hF : Nat.card F = q) (hq : q % 4 = 3) {W : SL2 F}
    (hWW : W * W = negOne F) :
    IsCyclic ↥(Subgroup.centralizer ({W} : Set (SL2 F))) ∧
      Nat.card ↥(Subgroup.centralizer ({W} : Set (SL2 F))) = q + 1 := by
  have hodd : Odd (Nat.card F) := by rw [hF]; exact Nat.odd_iff.2 (by omega)
  have hx : W * W = CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
    rw [hWW]
    apply Subtype.ext
    rw [CFSG.Semidihedral.OddFieldSL2.minusIdentity_matrix, t2B_negOne_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  obtain ⟨hcyc, -, hnsq⟩ := CFSG.GH74.GLS.IVK.L2Torus.centralizer_cyclic_card hodd W hx
  refine ⟨hcyc, ?_⟩
  rw [hnsq (not_isSquare_negOne (by rw [hF]; exact hq)), hF]

theorem negF_c_comm {c : Matrix (Fin 2) (Fin 2) F} {a₀ b₀ : F} {W : SL2 F}
    (hc : c = a₀ • (1 : Matrix (Fin 2) (Fin 2) F) + b₀ • (W : Matrix (Fin 2) (Fin 2) F))
    {Y : Matrix (Fin 2) (Fin 2) F} (hY : Y * (W : Matrix (Fin 2) (Fin 2) F) =
      (W : Matrix (Fin 2) (Fin 2) F) * Y) : c * Y = Y * c := by
  rw [hc, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hY]

theorem negF_c_eq {a₀ b₀ : F} {W : SL2 F} (hW : (W : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0]) :
    (!![a₀, -b₀; b₀, a₀] : Matrix (Fin 2) (Fin 2) F) =
      a₀ • (1 : Matrix (Fin 2) (Fin 2) F) + b₀ • (W : Matrix (Fin 2) (Fin 2) F) := by
  rw [hW]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem negF_gi {g : GL (Fin 2) F} {δ : F} (hδ : δ ≠ 0)
    (hg2 : (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      (-δ) • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (-δ⁻¹) • (g : Matrix (Fin 2) (Fin 2) F) := by
  have h1 : (g : Matrix (Fin 2) (Fin 2) F) * ((-δ⁻¹) • (g : Matrix (Fin 2) (Fin 2) F)) = 1 := by
    rw [Matrix.mul_smul, hg2, smul_smul]
    have : (-δ⁻¹) * (-δ) = 1 := by field_simp
    rw [this, one_smul]
  have hgg' : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      1 := by simp
  calc ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * 1 := (Matrix.mul_one _).symm
    _ = ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((g : Matrix (Fin 2) (Fin 2) F) * ((-δ⁻¹) • (g : Matrix (Fin 2) (Fin 2) F))) := by rw [h1]
    _ = (((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) *
        ((-δ⁻¹) • (g : Matrix (Fin 2) (Fin 2) F)) := by rw [Matrix.mul_assoc]
    _ = (-δ⁻¹) • (g : Matrix (Fin 2) (Fin 2) F) := by rw [hgg', Matrix.one_mul]

theorem negF_gi_sq {g : GL (Fin 2) F} {δ : F} (hδ : δ ≠ 0)
    (hg2 : (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      (-δ) • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (-δ⁻¹) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [negF_gi hδ hg2, smul_mul_smul_comm, hg2, smul_smul]
  have : (-δ⁻¹ * -δ⁻¹) * (-δ) = -δ⁻¹ := by field_simp
  rw [this]

theorem negF_mat_cent {c gi g Y : Matrix (Fin 2) (Fin 2) F} (hgg' : gi * g = 1)
    (hcY : c * Y = Y * c) : c * gi * (g * Y * gi) = Y * (c * gi) := by
  calc c * gi * (g * Y * gi) = c * (gi * g) * Y * gi := by simp only [Matrix.mul_assoc]
    _ = c * Y * gi := by rw [hgg', Matrix.mul_one]
    _ = Y * c * gi := by rw [hcY]
    _ = Y * (c * gi) := by simp only [Matrix.mul_assoc]

theorem negF_mat_sq {c gi g W : Matrix (Fin 2) (Fin 2) F} {δ : F}
    (hgg' : gi * g = 1) (hgi : gi * gi = (-δ⁻¹) • (1 : Matrix (Fin 2) (Fin 2) F))
    (hcW : c * W = W * c) :
    c * gi * (g * (c * gi) * gi) * W = W * (c * gi * (g * (c * gi) * gi)) := by
  have e : ∀ X : Matrix (Fin 2) (Fin 2) F, gi * (g * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hgg', Matrix.one_mul]
  have h : c * gi * (g * (c * gi) * gi) = (-δ⁻¹) • (c * c) := by
    calc c * gi * (g * (c * gi) * gi) = c * (gi * (g * (c * (gi * gi)))) := by
          simp only [Matrix.mul_assoc]
      _ = c * (c * (gi * gi)) := by rw [e]
      _ = (-δ⁻¹) • (c * c) := by
          rw [hgi, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
  have hcc : c * c * W = W * (c * c) := by
    rw [Matrix.mul_assoc, hcW, ← Matrix.mul_assoc, hcW, Matrix.mul_assoc]
  rw [h, Matrix.smul_mul, Matrix.mul_smul, hcc]

theorem negF_mat_V {Vm c c' Vi g gi : Matrix (Fin 2) (Fin 2) F} {δ : F} (hδ : δ ≠ 0)
    (hgg' : gi * g = 1) (hgi : gi * gi = (-δ⁻¹) • (1 : Matrix (Fin 2) (Fin 2) F))
    (h1 : Vm * c * Vi = c') (h2 : c' * c = δ • (1 : Matrix (Fin 2) (Fin 2) F)) :
    Vm * (c * gi) * (g * Vi * gi) * (g * (c * gi) * gi) = -1 := by
  have e : ∀ X : Matrix (Fin 2) (Fin 2) F, gi * (g * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hgg', Matrix.one_mul]
  calc Vm * (c * gi) * (g * Vi * gi) * (g * (c * gi) * gi)
      = Vm * (c * (gi * (g * (Vi * (gi * (g * (c * (gi * gi)))))))) := by
        simp only [Matrix.mul_assoc]
    _ = Vm * (c * (Vi * (c * (gi * gi)))) := by rw [e, e]
    _ = (Vm * c * Vi * c) * (gi * gi) := by simp only [Matrix.mul_assoc]
    _ = (c' * c) * (gi * gi) := by rw [h1]
    _ = -1 := by
        rw [h2, hgi, smul_mul_smul_comm, Matrix.one_mul]
        have : δ * -δ⁻¹ = -1 := by field_simp
        rw [this, neg_smul, one_smul]

theorem negF_E1 {a b a₀ b₀ : F} (hab : a * a + b * b = -1) :
    (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) F) * !![a₀, -b₀; b₀, a₀] * !![-a, -b; -b, a] =
      !![a₀, b₀; -b₀, a₀] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-a₀) * hab
  · linear_combination (-b₀) * hab
  · linear_combination b₀ * hab
  · linear_combination (-a₀) * hab

theorem negF_E2 {a₀ b₀ δ : F} (hδ : a₀ * a₀ + b₀ * b₀ = δ) :
    (!![a₀, b₀; -b₀, a₀] : Matrix (Fin 2) (Fin 2) F) * !![a₀, -b₀; b₀, a₀] =
      δ • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · exact hδ
  · ring
  · ring
  · linear_combination hδ

theorem negF_A_cent {g : GL (Fin 2) F} {c : Matrix (Fin 2) (Fin 2) F} {A Y : SL2 F}
    (hA : (A : Matrix (Fin 2) (Fin 2) F) =
      c * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    (hcY : c * (Y : Matrix (Fin 2) (Fin 2) F) = (Y : Matrix (Fin 2) (Fin 2) F) * c) :
    A * slConj g Y * A⁻¹ = Y := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_slConj, hA]
  have hgg' : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      1 := by simp
  exact negF_mat_cent hgg' hcY

theorem negF_A_sq {g : GL (Fin 2) F} {δ : F} {c : Matrix (Fin 2) (Fin 2) F} {W A : SL2 F}
    (hgi : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (-δ⁻¹) • (1 : Matrix (Fin 2) (Fin 2) F))
    (hA : (A : Matrix (Fin 2) (Fin 2) F) =
      c * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    (hcW : c * (W : Matrix (Fin 2) (Fin 2) F) = (W : Matrix (Fin 2) (Fin 2) F) * c) :
    A * slConj g A ∈ Subgroup.centralizer ({W} : Set (SL2 F)) := by
  rw [negF_mem_cent, Matrix.SpecialLinearGroup.coe_mul, coe_slConj, hA]
  have hgg' : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      1 := by simp
  exact negF_mat_sq hgg' hgi hcW

theorem negF_A_V {g : GL (Fin 2) F} {δ : F} (hδ : δ ≠ 0) {a b a₀ b₀ : F} {V A : SL2 F}
    (hgi : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (-δ⁻¹) • (1 : Matrix (Fin 2) (Fin 2) F))
    (hab : a * a + b * b = -1) (hab₀ : a₀ * a₀ + b₀ * b₀ = δ)
    (hV : (V : Matrix (Fin 2) (Fin 2) F) = !![a, b; b, -a])
    (hA : (A : Matrix (Fin 2) (Fin 2) F) =
      !![a₀, -b₀; b₀, a₀] * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) :
    V * A * slConj g V⁻¹ = negOne F * slConj g A⁻¹ := by
  have hVi : ((V⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![-a, -b; -b, a] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hV, Matrix.adjugate_fin_two_of]
  have hgg' : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      1 := by simp
  rw [map_inv (slConj g) A, eq_mul_inv_iff_mul_eq]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_slConj, hA, hVi, hV, t2B_negOne_eq]
  exact negF_mat_V hδ hgg' hgi (negF_E1 hab) (negF_E2 hab₀)

end Mat

theorem negFactor_exists {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q)
    (hq : q % 4 = 3) (g : GL (Fin 2) F)
    (hg2 : (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
      (-((g : Matrix (Fin 2) (Fin 2) F).det)) • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ∃ W V A : SL2 F, NegFactor q g W V A := by
  have hodd : Odd (Nat.card F) := by rw [hF]; exact Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := T2.two_ne_zero_of_odd_card hodd
  have hgg : (g : Matrix (Fin 2) (Fin 2) F) * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      1 := by simp
  have hδ : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have := congrArg Matrix.det hgg
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hdetg : (g : Matrix (Fin 2) (Fin 2) F).det *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← Matrix.det_mul, hgg, Matrix.det_one]
  obtain ⟨a, b, hab⟩ := negF_sq_add_sq hodd (-1 : F)
  obtain ⟨a₀, b₀, hab₀⟩ := negF_sq_add_sq hodd (g : Matrix (Fin 2) (Fin 2) F).det
  obtain ⟨W, hW⟩ := negF_exists_W (F := F)
  obtain ⟨V, hV⟩ := negF_exists_V hab
  have hWW := negF_sq_W hW
  have hVV := negF_sq_V hab hV
  have hdetc : (!![a₀, -b₀; b₀, a₀] : Matrix (Fin 2) (Fin 2) F).det =
      (g : Matrix (Fin 2) (Fin 2) F).det := by
    rw [Matrix.det_fin_two_of]
    linear_combination hab₀
  obtain ⟨A, hA⟩ : ∃ A : SL2 F, (A : Matrix (Fin 2) (Fin 2) F) =
      !![a₀, -b₀; b₀, a₀] * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
    ⟨⟨_, by rw [Matrix.det_mul, hdetc]; exact hdetg⟩, rfl⟩
  have hgi := negF_gi_sq hδ hg2
  have hc := negF_c_eq (a₀ := a₀) (b₀ := b₀) hW
  obtain ⟨hcyc, hcard⟩ := negF_T_cyc_card hF hq hWW
  refine ⟨W, V, A, ?_⟩
  exact
    { W_sq := hWW
      V_sq := hVV
      VW := negF_VW h2 hW hV hVV
      T_cyc := hcyc
      T_card := hcard
      T_cent := negF_T_cent
      T_inv := negF_T_inv h2 hW hV hVV
      A_cent := fun Y hY => negF_A_cent hA (negF_c_comm hc (negF_mem_cent.1 hY))
      A_sq := negF_A_sq hgi hA (negF_c_comm hc (Y := (W : Matrix (Fin 2) (Fin 2) F)) rfl)
      A_V := negF_A_V hδ hgi hab hab₀ hV hA }

end CFSG.GH74.GLS.Stage4.Rest
