module

public import CFSG.ClassicalInvolution.Q3.Q3T8B17
public import CFSG.Quasithin.SteinbergBIOddLinearThreeDiagonal
public import CFSG.ClassicalInvolution.Phan.Phan3SL3Pres

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open scoped MatrixGroups
open Matrix

section Diag

variable {K : Type} [Field K]

@[expose] noncomputable def diagSL (a b c : K) (h : a * b * c = 1) : SL(3, K) :=
  ⟨Matrix.diagonal ![a, b, c], by simp [Matrix.det_diagonal, Fin.prod_univ_three, h]⟩

theorem coe_diagSL (a b c : K) (h : a * b * c = 1) :
    ((diagSL a b c h : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![a, b, c] := rfl

@[expose] noncomputable def diagA (K : Type) [Field K] : SL(3, K) := diagSL (-1) (-1) 1 (by ring)

@[expose] noncomputable def diagB (K : Type) [Field K] : SL(3, K) := diagSL 1 (-1) (-1) (by ring)

@[expose] noncomputable def diagC (K : Type) [Field K] : SL(3, K) := diagSL (-1) 1 (-1) (by ring)

theorem transvection_comm_diagSL {i j : Fin 3} (hij : i ≠ j) (c : K) {a b d : K}
    (h : a * b * d = 1) (hd : (![a, b, d] : Fin 3 → K) i = (![a, b, d] : Fin 3 → K) j) :
    Matrix.SpecialLinearGroup.transvection hij c * diagSL a b d h =
      diagSL a b d h * Matrix.SpecialLinearGroup.transvection hij c := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diagSL,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext x y
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hxy : x = y
  · subst hxy
    exact mul_comm _ _
  · by_cases hx : i = x ∧ j = y
    · obtain ⟨rfl, rfl⟩ := hx
      simp [hxy, hd, mul_comm]
    · simp [hxy, hx]

theorem sup_centralizer_diagA_diagB (hK : Nat.card K = 3) :
    Subgroup.centralizer ({diagA K} : Set SL(3, K)) ⊔
      Subgroup.centralizer ({diagB K} : Set SL(3, K)) = ⊤ := by
  rw [eq_top_iff, ← CFSG.ClassicalInvolution.Phan.Q3G.sl3Gen_closure hK, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · refine Subgroup.mem_sup_left ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact transvection_comm_diagSL (show (0 : Fin 3) ≠ 1 by decide) (1 : K) (a := -1) (b := -1)
      (d := 1) (by ring) (by simp)
  · refine Subgroup.mem_sup_left ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact transvection_comm_diagSL (show (1 : Fin 3) ≠ 0 by decide) (1 : K) (a := -1) (b := -1)
      (d := 1) (by ring) (by simp)
  · refine Subgroup.mem_sup_right ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact transvection_comm_diagSL (show (1 : Fin 3) ≠ 2 by decide) (1 : K) (a := 1) (b := -1)
      (d := -1) (by ring) (by simp)
  · refine Subgroup.mem_sup_right ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact transvection_comm_diagSL (show (2 : Fin 3) ≠ 1 by decide) (1 : K) (a := 1) (b := -1)
      (d := -1) (by ring) (by simp)

end Diag

section Conj

variable {K : Type} [Field K]

theorem coe_diagA : ((diagA K : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
    Matrix.diagonal ![-1, -1, 1] := rfl

theorem coe_diagB : ((diagB K : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
    Matrix.diagonal ![1, -1, -1] := rfl

theorem coe_diagC : ((diagC K : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
    Matrix.diagonal ![-1, 1, -1] := rfl

theorem exists_sl_conj_of_gl (hK : Nat.card K = 3) (g : GL (Fin 3) K) :
    ∃ g' : SL(3, K), ∀ x : Matrix (Fin 3) (Fin 3) K,
      (g' : Matrix (Fin 3) (Fin 3) K) * x * ((g'⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
        (g : Matrix (Fin 3) (Fin 3) K) * x * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  set d : K := Matrix.det (g : Matrix (Fin 3) (Fin 3) K) with hd
  have hd0 : d ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have hdd : d * d = 1 := by
    rcases CFSG.ClassicalInvolution.Phan.Q3G.eq_zero_or_one_or_neg_one hK d with h | h | h
    · exact absurd h hd0
    · rw [h]; ring
    · rw [h]; ring
  have hdet : Matrix.det (d • (g : Matrix (Fin 3) (Fin 3) K)) = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← hd]
    calc d ^ 3 * d = (d * d) * (d * d) := by ring
      _ = 1 := by rw [hdd, one_mul]
  let g' : SL(3, K) := ⟨d • (g : Matrix (Fin 3) (Fin 3) K), hdet⟩
  have hg'val : (g' : Matrix (Fin 3) (Fin 3) K) = d • (g : Matrix (Fin 3) (Fin 3) K) := rfl
  refine ⟨g', fun x => ?_⟩
  have h1 : ((g'⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.adjugate (g : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hg'val, Matrix.adjugate_smul, Fintype.card_fin]
    have : d ^ (3 - 1) = 1 := by norm_num [pow_two, hdd]
    rw [this, one_smul]
  have h2 : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      d • Matrix.adjugate (g : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, ← hd, Ring.inverse_eq_inv',
      inv_eq_of_mul_eq_one_right hdd]
  rw [h1, h2, hg'val, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul]

theorem exists_sl_conj_of_conj (hK : Nat.card K = 3) {u v : SL(3, K)} (g : GL (Fin 3) K)
    (h : g * Matrix.SpecialLinearGroup.toGL u * g⁻¹ = Matrix.SpecialLinearGroup.toGL v) :
    ∃ g' : SL(3, K), g' * u * g'⁻¹ = v := by
  obtain ⟨g', hg'⟩ := exists_sl_conj_of_gl hK g
  refine ⟨g', Subtype.ext ?_⟩
  have hm := congrArg (fun y : GL (Fin 3) K => (y : Matrix (Fin 3) (Fin 3) K)) h
  simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hm
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rw [hg' (u : Matrix (Fin 3) (Fin 3) K)]
  exact hm

end Conj

section Main

variable {K : Type} [Field K]

theorem diagA_mul_diagC : diagA K * diagC K = diagB K := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagA, coe_diagB, coe_diagC,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diagonal_involution_cases (hK : Nat.card K = 3) {w : SL(3, K)} (hw2 : w * w = 1)
    (hdiag : (w : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    w = 1 ∨ w = diagA K ∨ w = diagB K ∨ w = diagC K := by
  have := CFSG.ClassicalInvolution.Phan.Q3G.charP_three hK
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have h2 : (2 : K) ≠ 0 := fun h => one_ne_zero (show (1 : K) = 0 by linear_combination h3 - h)
  have hunit : ∀ x : K, x * x = 1 → x = 1 ∨ x = -1 := fun x hx => by
    have : (x - 1) * (x + 1) = 0 := by linear_combination hx
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  obtain ⟨a, ha⟩ : ∃ a : K, a = (w : Matrix (Fin 3) (Fin 3) K) 0 0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : K, b = (w : Matrix (Fin 3) (Fin 3) K) 1 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : K, c = (w : Matrix (Fin 3) (Fin 3) K) 2 2 := ⟨_, rfl⟩
  have hwd : (w : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![a, b, c] := by
    rw [← hdiag.diagonal_diag]
    congr 1
    funext i
    fin_cases i <;> simp [Matrix.diag, ha, hb, hc]
  have hdet : a * b * c = 1 := by
    have h := w.2
    rw [hwd, Matrix.det_diagonal, Fin.prod_univ_three] at h
    simpa using h
  have hsq : (w : Matrix (Fin 3) (Fin 3) K) * (w : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hw2]; rfl
  rw [hwd, Matrix.diagonal_mul_diagonal] at hsq
  have ha2 : a * a = 1 := by
    have := congrFun (congrFun hsq 0) 0
    simpa using this
  have hb2 : b * b = 1 := by
    have := congrFun (congrFun hsq 1) 1
    simpa using this
  have hc2 : c * c = 1 := by
    have := congrFun (congrFun hsq 2) 2
    simpa using this
  have hwe : w = diagSL a b c hdet := Subtype.ext (by rw [hwd, coe_diagSL])
  rcases hunit a ha2 with rfl | rfl <;> rcases hunit b hb2 with rfl | rfl <;>
    rcases hunit c hc2 with rfl | rfl
  · left
    rw [hwe]
    apply Subtype.ext
    rw [coe_diagSL, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · exact absurd (show (2 : K) = 0 by linear_combination (-1 : K) * hdet) h2
  · exact absurd (show (2 : K) = 0 by linear_combination (-1 : K) * hdet) h2
  · right; right; left
    rw [hwe]
    rfl
  · exact absurd (show (2 : K) = 0 by linear_combination (-1 : K) * hdet) h2
  · right; right; right
    rw [hwe]
    rfl
  · right; left
    rw [hwe]
    rfl
  · exact absurd (show (2 : K) = 0 by linear_combination (-1 : K) * hdet) h2

end Main

section Facts

variable {K : Type} [Field K]

theorem linkModelFacts_sl3 (hK : Nat.card K = 3) : LinkModelFacts SL(3, K) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have := CFSG.ClassicalInvolution.Phan.Q3G.charP_three hK
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  refine ⟨?_, ?_⟩
  · intro u v hu hu1 hv hv1
    have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu) hu1
    have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hv) hv1
    obtain ⟨gu, hgu⟩ := CFSG.Quasithin.SteinbergBI.exists_conj_eq_negNegOne hodd hu2
    obtain ⟨gv, hgv⟩ := CFSG.Quasithin.SteinbergBI.exists_conj_eq_negNegOne hodd hv2
    have hgu' : gu * Matrix.SpecialLinearGroup.toGL u * gu⁻¹ =
        Matrix.SpecialLinearGroup.toGL (diagA K) :=
      Units.ext (by simpa [Units.val_mul, coe_diagA] using hgu)
    have hgv' : gv * Matrix.SpecialLinearGroup.toGL v * gv⁻¹ =
        Matrix.SpecialLinearGroup.toGL (diagA K) :=
      Units.ext (by simpa [Units.val_mul, coe_diagA] using hgv)
    refine exists_sl_conj_of_conj hK (gv⁻¹ * gu) ?_
    calc gv⁻¹ * gu * Matrix.SpecialLinearGroup.toGL u * (gv⁻¹ * gu)⁻¹ =
        gv⁻¹ * (gu * Matrix.SpecialLinearGroup.toGL u * gu⁻¹) * gv := by group
      _ = gv⁻¹ * (gv * Matrix.SpecialLinearGroup.toGL v * gv⁻¹) * gv := by rw [hgu', hgv']
      _ = Matrix.SpecialLinearGroup.toGL v := by group
  · intro u v hu hu1 hv hv1 huv hcomm
    have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu) hu1
    set A : Subgroup SL(3, K) := Subgroup.closure ({u, v} : Set SL(3, K)) with hA
    have hD := CFSG.ClassicalInvolution.Asc77.T7A.isElemAbelian2_closure_pair hu hv hu1 hv1 huv
      hcomm
    have huA : u ∈ A := Subgroup.subset_closure (by simp)
    have hvA : v ∈ A := Subgroup.subset_closure (by simp)
    have hAz : ∀ a ∈ A, a * u = u * a := by
      intro a ha
      have : A ≤ Subgroup.centralizer ({u} : Set SL(3, K)) := by
        rw [hA, Subgroup.closure_le]
        rintro y (rfl | rfl)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (this ha)
    have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
      intro a ha b hb
      have h1 := hD.2 (a * b) (A.mul_mem ha hb)
      have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hD.2 a ha)
      have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hD.2 b hb)
      have habi : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
      rw [_root_.mul_inv_rev, hai, hbi] at habi
      exact habi.symm
    have hAcyc : ¬ IsCyclic A := by
      intro hcyc
      obtain ⟨x, hx⟩ := hcyc.exists_ofOrder_eq_natCard
      have hx2 : x ^ 2 = 1 := by
        apply Subtype.ext
        rw [pow_two]
        exact hD.2 x x.2
      have h4 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
      rw [hx, hD.1] at h4
      omega
    have hAchar : (Nat.card A : K) ≠ 0 := by
      rw [hD.1]
      intro h
      have h4 : (4 : K) = 0 := by exact_mod_cast h
      exact one_ne_zero (show (1 : K) = 0 by linear_combination h4 - h3)
    obtain ⟨g, hg1, hgd⟩ := CFSG.Quasithin.SteinbergBI.exists_conj_diagonal_of_commute hodd hu2 A
      hAz hAcomm hAcyc hAchar
    obtain ⟨g', hg'⟩ := exists_sl_conj_of_gl hK g
    have hg'u : g' * u * g'⁻¹ = diagA K := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        hg' (u : Matrix (Fin 3) (Fin 3) K), hg1, coe_diagA]
    set w : SL(3, K) := g' * v * g'⁻¹ with hw
    have hwdiag : (w : Matrix (Fin 3) (Fin 3) K).IsDiag := by
      have h := hgd v hvA
      rw [hw, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        hg' (v : Matrix (Fin 3) (Fin 3) K)]
      exact h
    have hw2 : w * w = 1 := by
      calc w * w = g' * (v * v) * g'⁻¹ := by rw [hw]; group
        _ = 1 := by rw [hv]; group
    have hw1 : w ≠ 1 := fun h => hv1 (by
      calc v = g'⁻¹ * (g' * v * g'⁻¹) * g' := by group
        _ = 1 := by rw [← hw, h]; group)
    have hwA : w ≠ diagA K := fun h => huv (by
      calc u = g'⁻¹ * (g' * u * g'⁻¹) * g' := by group
        _ = g'⁻¹ * w * g' := by rw [hg'u, h]
        _ = v := by rw [hw]; group)
    have hcent : ∀ x : SL(3, K), Subgroup.centralizer ({g' * x * g'⁻¹} : Set SL(3, K)) ≤
        (Subgroup.centralizer ({x} : Set SL(3, K))).map (MulAut.conj g').toMonoidHom := by
      intro x y hy
      refine Subgroup.mem_map.mpr ⟨g'⁻¹ * y * g', ?_, ?_⟩
      swap
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      calc g'⁻¹ * y * g' * x = g'⁻¹ * (y * (g' * x * g'⁻¹)) * g' := by group
        _ = g'⁻¹ * ((g' * x * g'⁻¹) * y) * g' := by rw [hy]
        _ = x * (g'⁻¹ * y * g') := by group
    have hconjuv : g' * (u * v) * g'⁻¹ = diagA K * w := by
      rw [← hg'u, hw]; group
    have hmapW : (⊤ : Subgroup SL(3, K)) ≤
        (Subgroup.centralizer ({u} : Set SL(3, K)) ⊔ Subgroup.centralizer ({v} : Set SL(3, K)) ⊔
          Subgroup.centralizer ({u * v} : Set SL(3, K))).map (MulAut.conj g').toMonoidHom := by
      rw [← sup_centralizer_diagA_diagB hK]
      rcases diagonal_involution_cases hK hw2 hwdiag with h | h | h | h
      · exact absurd h hw1
      · exact absurd h hwA
      · refine sup_le (le_trans ?_ (Subgroup.map_mono (le_sup_of_le_left le_sup_left))) ?_
        · rw [← hg'u]; exact hcent u
        · refine le_trans ?_ (Subgroup.map_mono (le_sup_of_le_left le_sup_right))
          rw [← h, hw]; exact hcent v
      · have hB : g' * (u * v) * g'⁻¹ = diagB K := by
          rw [hconjuv, h, diagA_mul_diagC]
        refine sup_le (le_trans ?_ (Subgroup.map_mono (le_sup_of_le_left le_sup_left))) ?_
        · rw [← hg'u]; exact hcent u
        · refine le_trans ?_ (Subgroup.map_mono le_sup_right)
          rw [← hB]; exact hcent (u * v)
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hyW, hyx⟩ := hmapW (Subgroup.mem_top ((MulAut.conj g') x))
    have hxy : y = x := (MulAut.conj g').injective hyx
    rwa [hxy] at hyW

end Facts

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
