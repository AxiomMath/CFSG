module

public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAut
public import CFSG.ClassicalInvolution.Asc77.AscL62Pair

public section

namespace CFSG.ClassicalInvolution.Asc77.AscL62

open CFSG.ABGLocalTools CFSG.GorensteinWalter Matrix
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups Pointwise commutatorElement

variable {F : Type} [Field F]

@[expose] noncomputable def semilinHom (G : GL (Fin 2) F) (σ : F ≃+* F) :
    SL(2, F) →* SL(2, F) where
  toFun b := ⟨(G : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F).map σ *
      ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
    rw [Matrix.det_mul, Matrix.det_mul]
    have h1 : (G : Matrix (Fin 2) (Fin 2) F).det *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    have h2 : ((b : Matrix (Fin 2) (Fin 2) F).map σ).det = 1 := by
      have := RingHom.map_det (σ : F →+* F) (b : Matrix (Fin 2) (Fin 2) F)
      rw [b.det_coe, map_one] at this
      exact this.symm
    rw [h2, mul_one, h1]⟩
  map_one' := by
    apply Subtype.ext
    show (G : Matrix (Fin 2) (Fin 2) F) * (1 : Matrix (Fin 2) (Fin 2) F).map σ *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.mul_one, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  map_mul' a b := by
    apply Subtype.ext
    show (G : Matrix (Fin 2) (Fin 2) F) * ((a : Matrix (Fin 2) (Fin 2) F) *
          (b : Matrix (Fin 2) (Fin 2) F)).map σ *
          ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((G : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F).map σ *
          ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
        ((G : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F).map σ *
          ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    have hGG : ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (G : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.map_mul]
    calc (G : Matrix (Fin 2) (Fin 2) F) * ((a : Matrix (Fin 2) (Fin 2) F).map σ *
            (b : Matrix (Fin 2) (Fin 2) F).map σ) *
          ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = (G : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F).map σ * 1 *
            (b : Matrix (Fin 2) (Fin 2) F).map σ *
          ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
          simp [Matrix.mul_assoc]
      _ = _ := by rw [← hGG]; simp only [Matrix.mul_assoc]

theorem coe_semilinHom (G : GL (Fin 2) F) (σ : F ≃+* F) (b : SL(2, F)) :
    ((semilinHom G σ b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (G : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F).map σ *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl

theorem eq_semilinHom_of_smul [Finite F] (h4 : 4 ≤ Nat.card F) (α : MulAut SL(2, F))
    (G : GL (Fin 2) F) (σ : F ≃+* F)
    (h : ∀ b : SL(2, F), ∃ u : F, u ≠ 0 ∧
      ((α b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        u • ((semilinHom G σ b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) :
    ∀ b, α b = semilinHom G σ b := by
  have hcent : ∀ b : SL(2, F), α b * (semilinHom G σ b)⁻¹ ∈ Subgroup.center SL(2, F) := by
    intro b
    obtain ⟨u, hu0, hu⟩ := h b
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h1 : ((α b * (semilinHom G σ b)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = u • 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, hu, Matrix.smul_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    simp only [Matrix.SpecialLinearGroup.coe_mul, h1, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  let δ : SL(2, F) →* Subgroup.center SL(2, F) :=
    { toFun := fun b => ⟨α b * (semilinHom G σ b)⁻¹, hcent b⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro b c
        apply Subtype.ext
        have hz := Subgroup.mem_center_iff.mp (hcent c) (α b)
        have hz' := Subgroup.mem_center_iff.mp (hcent b) (α c * (semilinHom G σ c)⁻¹)
        show α (b * c) * (semilinHom G σ (b * c))⁻¹ =
          (α b * (semilinHom G σ b)⁻¹) * (α c * (semilinHom G σ c)⁻¹)
        calc α (b * c) * (semilinHom G σ (b * c))⁻¹
            = α b * (α c * (semilinHom G σ c)⁻¹) * (semilinHom G σ b)⁻¹ := by
              rw [map_mul, map_mul]; group
          _ = ((α c * (semilinHom G σ c)⁻¹) * α b) * (semilinHom G σ b)⁻¹ := by rw [hz]
          _ = (α c * (semilinHom G σ c)⁻¹) * (α b * (semilinHom G σ b)⁻¹) := by group
          _ = (α b * (semilinHom G σ b)⁻¹) * (α c * (semilinHom G σ c)⁻¹) := hz' }
  have hperf : Group.IsPerfect SL(2, F) := CFSG.ClassicalInvolution.sl2_isPerfect h4
  have hker : commutator SL(2, F) ≤ δ.ker := Abelianization.commutator_subset_ker δ
  intro b
  have hb : b ∈ commutator SL(2, F) := by
    rw [hperf.commutator_eq_top]
    exact Subgroup.mem_top b
  have h1 : δ b = 1 := hker hb
  have h2 : α b * (semilinHom G σ b)⁻¹ = 1 := congrArg Subtype.val h1
  exact mul_inv_eq_one.mp h2

theorem exists_semilinear_data [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut SL(2, F)) :
    ∃ (γ : PGammaL2 F) (G : GL (Fin 2) F),
      pGammaL2ToMulAutPSL2 F (isOddPrimePower_card_of_odd hodd) h3 γ = psl2MulAutOf α ∧
      ∀ b : SL(2, F), ∃ u : F, u ≠ 0 ∧ ((α b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        u • ((G : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F).map γ.right *
          ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
  have hK := isOddPrimePower_card_of_odd hodd
  obtain ⟨f, -, hKcard⟩ := card_eq_ringChar_pow (F := F)
  have : Fact (ringChar F).Prime := ⟨ringChar_prime⟩
  obtain ⟨γ, hγ⟩ := pGammaL2ToMulAutPSL2_surjective F hKcard hK h3 (psl2MulAutOf α)
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective γ.left
  exact ⟨γ, G, hγ, coe_mulAut_eq_smul_conj hK h3 α γ hγ G hG⟩

theorem traceless_mul_add_mul (X Y : Matrix (Fin 2) (Fin 2) F) (hX : X.trace = 0)
    (hY : Y.trace = 0) : X * Y + Y * X = (X * Y).trace • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have hX' : X 1 1 = -X 0 0 := by
    rw [Matrix.trace_fin_two] at hX
    linear_combination hX
  have hY' : Y 1 1 = -Y 0 0 := by
    rw [Matrix.trace_fin_two] at hY
    linear_combination hY
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, hX', hY'] <;> ring

theorem mul_eq_half_trace (hF : (2 : F) ≠ 0) (X Y : Matrix (Fin 2) (Fin 2) F) (hX : X.trace = 0)
    (hY : Y.trace = 0) (hc : Y * X = X * Y) :
    X * Y = ((X * Y).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have h := traceless_mul_add_mul X Y hX hY
  rw [hc, ← two_smul F (X * Y)] at h
  have h1 : (2 : F)⁻¹ • ((2 : F) • (X * Y)) = X * Y := by
    rw [smul_smul, inv_mul_cancel₀ hF, one_smul]
  calc X * Y = (2 : F)⁻¹ • ((2 : F) • (X * Y)) := h1.symm
    _ = (2 : F)⁻¹ • ((X * Y).trace • (1 : Matrix (Fin 2) (Fin 2) F)) := by rw [h]
    _ = ((X * Y).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [smul_smul, div_eq_inv_mul]

theorem exists_smul_one_of_commute_quat (hF : (2 : F) ≠ 0) (a b M : Matrix (Fin 2) (Fin 2) F)
    (ha : a * a = -1) (hb : b * b = -1) (hab : a * b = -(b * a)) (hat : a.trace = 0)
    (hbt : b.trace = 0) (hMa : M * a = a * M) (hMb : M * b = b * M) :
    ∃ c : F, M = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  set m : F := M.trace / 2 with hm
  set M₀ : Matrix (Fin 2) (Fin 2) F := M - m • 1 with hM₀
  have hM₀t : M₀.trace = 0 := by
    rw [hM₀, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul, hm]
    field_simp
    ring
  have hM₀a : M₀ * a = a * M₀ := by
    rw [hM₀, sub_mul, mul_sub, hMa]
    simp
  have hM₀b : M₀ * b = b * M₀ := by
    rw [hM₀, sub_mul, mul_sub, hMb]
    simp
  have hA := mul_eq_half_trace hF a M₀ hat hM₀t hM₀a
  have hB := mul_eq_half_trace hF b M₀ hbt hM₀t hM₀b
  set u : F := (a * M₀).trace / 2 with hu
  set w : F := (b * M₀).trace / 2 with hw
  have e1 : M₀ = -(u • a) := by
    have : -(a * (a * M₀)) = M₀ := by
      rw [← mul_assoc, ha]; simp
    rw [← this, hA]
    simp
  have e2 : M₀ = -(w • b) := by
    have : -(b * (b * M₀)) = M₀ := by
      rw [← mul_assoc, hb]; simp
    rw [← this, hB]
    simp
  have e3 : u • a = w • b := by
    have := e1.symm.trans e2
    exact neg_injective this
  have h1 : (1 : Matrix (Fin 2) (Fin 2) F) ≠ 0 := one_ne_zero
  by_cases hu0 : u = 0
  · refine ⟨m, ?_⟩
    have : M₀ = 0 := by rw [e1, hu0]; simp
    rw [hM₀] at this
    exact sub_eq_zero.mp this
  · exfalso
    set lam : F := u⁻¹ * w with hlam
    have e4 : a = lam • b := by
      have := congrArg (fun X => u⁻¹ • X) e3
      simpa [smul_smul, inv_mul_cancel₀ hu0, hlam] using this
    have e5 : a * b = (-lam) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [e4, smul_mul_assoc, hb]; simp
    have e6 : b * a = (-lam) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [e4, mul_smul_comm, hb]; simp
    rw [e5, e6] at hab
    have e7 : ((2 : F) * lam) • (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by
      have h8 : (-lam) • (1 : Matrix (Fin 2) (Fin 2) F) = lam • 1 := by
        rw [hab]; simp
      calc ((2 : F) * lam) • (1 : Matrix (Fin 2) (Fin 2) F)
          = lam • (1 : Matrix (Fin 2) (Fin 2) F) + lam • 1 := by rw [two_mul, add_smul]
        _ = lam • (1 : Matrix (Fin 2) (Fin 2) F) + (-lam) • 1 := by rw [h8]
        _ = 0 := by rw [neg_smul, add_neg_cancel]
    have e8 : (2 : F) * lam = 0 := by
      rcases smul_eq_zero.mp e7 with h9 | h9
      · exact h9
      · exact absurd h9 h1
    have e9 : lam = 0 := by
      rcases mul_eq_zero.mp e8 with h9 | h9
      · exact absurd h9 hF
      · exact h9
    rw [e9, zero_smul] at e4
    rw [e4] at ha
    simp at ha

theorem trace_eq_zero_of_mul_self_eq_neg_one (a : SL(2, F))
    (h : a * a = -1) : (a : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
  have h1 : (a : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) = -1 := by
    have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) h
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  have hdet := a.det_coe
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun h1 0) 0
  have e11 := congrFun (congrFun h1 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
  rw [Matrix.trace_fin_two]
  have : ((a : Matrix (Fin 2) (Fin 2) F) 0 0 + (a : Matrix (Fin 2) (Fin 2) F) 1 1) ^ 2 = 0 := by
    linear_combination e00 + e11 + 2 * hdet
  exact pow_eq_zero_iff (two_ne_zero) |>.mp this

theorem mul_eq_of_conj_eq (G : GL (Fin 2) F) {x y : Matrix (Fin 2) (Fin 2) F}
    (h : (G : Matrix (Fin 2) (Fin 2) F) * x *
      ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = y) :
    (G : Matrix (Fin 2) (Fin 2) F) * x = y * (G : Matrix (Fin 2) (Fin 2) F) := by
  have hGG : ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (G : Matrix (Fin 2) (Fin 2) F) * x = (G : Matrix (Fin 2) (Fin 2) F) * x * 1 := by
        rw [Matrix.mul_one]
    _ = (G : Matrix (Fin 2) (Fin 2) F) * x * (((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (G : Matrix (Fin 2) (Fin 2) F)) := by rw [hGG]
    _ = ((G : Matrix (Fin 2) (Fin 2) F) * x * ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
          (G : Matrix (Fin 2) (Fin 2) F) := by simp only [Matrix.mul_assoc]
    _ = y * (G : Matrix (Fin 2) (Fin 2) F) := by rw [h]

theorem semilinHom_one_eq_id (hF : (2 : F) ≠ 0) (G : GL (Fin 2) F) (a b : SL(2, F))
    (ha : a * a = -1) (hb : b * b = -1) (hab : a * b = (-1) * (b * a))
    (hfa : semilinHom G 1 a = a) (hfb : semilinHom G 1 b = b) :
    ∀ x, semilinHom G 1 x = x := by
  have hat := trace_eq_zero_of_mul_self_eq_neg_one a ha
  have hbt := trace_eq_zero_of_mul_self_eq_neg_one b hb
  have hcoe : ∀ x : SL(2, F), ((semilinHom G 1 x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (G : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro x
    rw [coe_semilinHom]
    simp
  have hMa : (G : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) =
      (a : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) := by
    apply mul_eq_of_conj_eq
    rw [← hcoe, hfa]
  have hMb : (G : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F) =
      (b : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) := by
    apply mul_eq_of_conj_eq
    rw [← hcoe, hfb]
  have ha' : (a : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) = -1 := by
    simpa [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) ha
  have hb' : (b : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F) = -1 := by
    simpa [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) hb
  have hab' : (a : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F) =
      -((b : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F)) := by
    simpa [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) hab
  obtain ⟨c, hc⟩ := exists_smul_one_of_commute_quat hF _ _ _ ha' hb' hab' hat hbt hMa hMb
  intro x
  apply Subtype.ext
  rw [hcoe]
  have hcomm : (G : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) =
      (x : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) := by
    rw [hc]
    simp
  have hGG : (G : Matrix (Fin 2) (Fin 2) F) * ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hcomm, Matrix.mul_assoc, hGG, Matrix.mul_one]

@[expose] noncomputable def diagHom : Fˣ →* SL(2, F) where
  toFun μ := ⟨!![(μ : F), 0; 0, ((μ⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    show (!![((a * b : Fˣ) : F), 0; 0, (((a * b)⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F) =
      !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] * !![(b : F), 0; 0, ((b⁻¹ : Fˣ) : F)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem coe_diagHom (μ : Fˣ) : ((diagHom μ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    !![(μ : F), 0; 0, ((μ⁻¹ : Fˣ) : F)] := rfl

theorem sigma_eq_of_fixes_diag (G : GL (Fin 2) F) (σ : F ≃+* F) (μ : Fˣ)
    (hfix : semilinHom G σ (diagHom μ) = diagHom μ) :
    σ (μ : F) = μ ∨ (σ (μ : F))⁻¹ = μ := by
  have h1 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) hfix
  simp only [coe_semilinHom, coe_diagHom] at h1
  have h2 := mul_eq_of_conj_eq G h1
  have hdet : (G : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 G.isUnit).ne_zero
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun h2 0) 0
  have e01 := congrFun (congrFun h2 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  by_cases hg : (G : Matrix (Fin 2) (Fin 2) F) 0 0 = 0
  · right
    rw [hg] at hdet
    have hg01 : (G : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := by
      intro h0
      apply hdet
      rw [h0]
      ring
    have h3 : (G : Matrix (Fin 2) (Fin 2) F) 0 1 * (σ (μ : F))⁻¹ =
        (G : Matrix (Fin 2) (Fin 2) F) 0 1 * μ := by
      rw [e01, mul_comm]
    exact mul_left_cancel₀ hg01 h3
  · left
    have h3 : (G : Matrix (Fin 2) (Fin 2) F) 0 0 * σ (μ : F) =
        (G : Matrix (Fin 2) (Fin 2) F) 0 0 * μ := by
      rw [e00, mul_comm]
    exact mul_left_cancel₀ hg h3

variable {p f : ℕ} [Fact p.Prime]

theorem mulAut_involution_structure (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (β : MulAut SL(2, GaloisField p f)) (hβ : β * β = 1) :
    ∃ (G : GL (Fin 2) (GaloisField p f)) (σ : GaloisField p f ≃+* GaloisField p f),
      (∀ b, β b = semilinHom G σ b) ∧ σ * σ = 1 := by
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp hq
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have h3 : 3 < Nat.card (GaloisField p f) := by rw [hcard]; omega
  obtain ⟨γ, G, hγ, hsmul⟩ := exists_semilinear_data hodd h3 β
  refine ⟨G, γ.right, ?_, ?_⟩
  · refine eq_semilinHom_of_smul (by omega) β G γ.right ?_
    intro b
    obtain ⟨u, hu0, hu⟩ := hsmul b
    exact ⟨u, hu0, hu⟩
  · have hK := isOddPrimePower_card_of_odd hodd
    have h1 : psl2MulAutOf β ^ 2 = 1 := psl2MulAutOf_pow_eq_one (by rw [pow_two]; exact hβ)
    have h2 : γ ^ 2 = 1 := by
      apply pGammaL2ToMulAutPSL2_injective (GaloisField p f) hK h3
      rw [map_pow, hγ, h1, map_one]
    have h4 := pGammaL2_pow_right γ 2
    rw [h2] at h4
    have h5 : γ.right ^ 2 = 1 := by simpa using h4.symm
    rwa [pow_two] at h5

theorem eq_frobenius_of_sq_eq_one (hf : f ≠ 0) {σ : GaloisField p f ≃+* GaloisField p f}
    (hσ : σ * σ = 1) (hne : σ ≠ 1) : ∃ k : ℕ, f = 2 * k ∧ ∀ a, σ a = a ^ p ^ k := by
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  obtain ⟨φ, hφ, hord, hzp, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (Fact.out : p.Prime) (Nat.one_le_iff_ne_zero.mpr hf) hcard
  have hφfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; omega)
  obtain ⟨k, hk, hkσ⟩ : ∃ k < f, φ ^ k = σ := by
    have hmem : σ ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top σ
    rw [← hφfin.mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨k, hk⟩ := hmem
    have h1 : φ ^ (k % orderOf φ) = φ ^ k := pow_mod_orderOf φ k
    rw [hord] at h1
    exact ⟨k % f, Nat.mod_lt _ (Nat.pos_of_ne_zero hf), h1.trans hk⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hkσ
    exact hne hkσ.symm
  have hφ2 : φ ^ (2 * k) = 1 := by
    rw [two_mul, pow_add, hkσ]
    exact hσ
  have h2k : f ∣ 2 * k := by
    have := orderOf_dvd_of_pow_eq_one hφ2
    rwa [hord] at this
  obtain ⟨c, hc⟩ := h2k
  have hc1 : c = 1 := by
    rcases c with _ | _ | c
    · omega
    · rfl
    · nlinarith
  rw [hc1, mul_one] at hc
  have hpow : ∀ (j : ℕ) (x : GaloisField p f), (φ ^ j) x = x ^ p ^ j := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ, RingAut.mul_apply, hφ, ih, ← pow_mul, pow_succ, mul_comm]
  refine ⟨k, hc.symm, fun a => ?_⟩
  rw [← hkσ, hpow]

theorem false_of_fixes_diag (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {G : GL (Fin 2) (GaloisField p f)} {σ : GaloisField p f ≃+* GaloisField p f}
    (hσ2 : σ * σ = 1) (hσ : σ ≠ 1) {μ : (GaloisField p f)ˣ}
    (hμ : orderOf μ = 2 ^ padicValNat 2 (p ^ f - 1))
    (hfix : semilinHom G σ (diagHom μ) = diagHom μ) : False := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  obtain ⟨k, hfk, hσk⟩ := eq_frobenius_of_sq_eq_one hf hσ2 hσ
  set r := p ^ k with hr
  have hq' : p ^ f = r * r := by rw [hfk, two_mul, pow_add]
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hrodd : Odd r := hpodd.pow
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hk1 : 1 ≤ k := by omega
  have hr3 : 3 ≤ r := by
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk1
  have hσμ : σ (μ : GaloisField p f) = (μ : GaloisField p f) ^ r := hσk _
  have hμ0 : (μ : GaloisField p f) ≠ 0 := μ.ne_zero
  have hmu : (μ : GaloisField p f) ^ (r - 1) = 1 ∨ (μ : GaloisField p f) ^ (r + 1) = 1 := by
    rcases sigma_eq_of_fixes_diag G σ μ hfix with h | h
    · left
      rw [hσμ] at h
      have h1 : (μ : GaloisField p f) ^ (r - 1) * μ = 1 * μ := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul]
        exact h
      exact mul_right_cancel₀ hμ0 h1
    · right
      rw [hσμ] at h
      have h1 : (μ : GaloisField p f) ^ r * μ = 1 := by
        have := mul_inv_cancel₀ (pow_ne_zero r hμ0)
        rwa [h] at this
      rwa [← pow_succ] at h1
  have hdvd : ∀ n : ℕ, (μ : GaloisField p f) ^ n = 1 → 2 ^ padicValNat 2 (p ^ f - 1) ∣ n := by
    intro n hn
    rw [← hμ]
    apply orderOf_dvd_of_pow_eq_one
    apply Units.ext
    simpa using hn
  have hval : padicValNat 2 (p ^ f - 1) = padicValNat 2 (r + 1) + padicValNat 2 (r - 1) := by
    have : p ^ f - 1 = (r + 1) * (r - 1) := by
      rw [hq']
      have := Nat.mul_self_sub_mul_self_eq r 1
      simpa using this
    rw [this]
    exact padicValNat.mul (by omega) (by omega)
  have h1 : 1 ≤ padicValNat 2 (r + 1) :=
    one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.mp hrodd.add_one)
  have h2 : 1 ≤ padicValNat 2 (r - 1) := by
    refine one_le_padicValNat_of_dvd (by omega) ?_
    have : Even (r - 1) := by
      obtain ⟨m, hm⟩ := hrodd
      exact ⟨m, by omega⟩
    exact even_iff_two_dvd.mp this
  rcases hmu with h | h
  · have := (padicValNat_dvd_iff_le (by omega : r - 1 ≠ 0)).mp (hdvd _ h)
    omega
  · have := (padicValNat_dvd_iff_le (by omega : r + 1 ≠ 0)).mp (hdvd _ h)
    omega

theorem isUniqueInvolution_top_neg_one [Finite F] (hodd : Odd (Nat.card F)) :
    IsUniqueInvolution (⊤ : Subgroup SL(2, F)) (-1) where
  mem := Subgroup.mem_top _
  ne_one := CFSG.ClassicalInvolution.sl2_neg_one_ne_one hodd
  sq := by
    calc (-1 : SL(2, F)) * -1 = -1 * (-1)⁻¹ := by rw [neg_one_inv]
      _ = 1 := by simp
  unique := by
    intro y _ hy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · right
      refine (CFSG.ClassicalInvolution.sl2_orderOf_eq_two_iff hodd y).mp ?_
      exact orderOf_eq_prime (by rw [pow_two]; exact hy) hy1

theorem mulAut_involution_eq_one_of_mem (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (β : MulAut SL(2, GaloisField p f)) (hβ : β * β = 1) (P : Sylow 2 SL(2, GaloisField p f))
    (hfix : ∀ x ∈ P, β x = x) (μ : (GaloisField p f)ˣ)
    (hμ : orderOf μ = 2 ^ padicValNat 2 (p ^ f - 1)) (hx₀ : diagHom μ ∈ P) : β = 1 := by
  obtain ⟨G, σ, hβσ, hσ2⟩ := mulAut_involution_structure hp hq β hβ
  by_cases hσ : σ = 1
  · subst hσ
    have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp hq
    have hF2 : ringChar (GaloisField p f) ≠ 2 := by
      rw [ringChar.eq (GaloisField p f) p]
      exact hp
    obtain ⟨k, hk, ⟨e⟩⟩ := specialLinearGroup_sylow_quaternion (GaloisField p f) hF2 P
    have hquat : IsQuatSub (P : Subgroup SL(2, GaloisField p f)) := ⟨k, hk, ⟨e⟩⟩
    have hz := isUniqueInvolution_top_neg_one hodd
    have hzP : (-1 : SL(2, GaloisField p f)) ∈ (P : Subgroup SL(2, GaloisField p f)) :=
      mem_of_uniqueInvolution_of_pGroup hz le_top P.isPGroup'
        (by have := hquat.eight_le; omega)
    have hzP' := isUniqueInvolution_of_le hz le_top hzP
    obtain ⟨C, hCP, hCc, hCcard, -⟩ := hquat.exists_cyclic_max
    obtain ⟨b₀, hb₀P, hb₀C⟩ : ∃ b₀ ∈ (P : Subgroup SL(2, GaloisField p f)), b₀ ∉ C := by
      by_contra hcon
      push Not at hcon
      have hle : (P : Subgroup SL(2, GaloisField p f)) ≤ C := hcon
      have := Subgroup.card_le_of_le hle
      have h0 : 0 < Nat.card C := Nat.card_pos
      omega
    obtain ⟨a, haC, haa⟩ := exists_sq_eq_of_index_two hquat hzP' hCP hCc hCcard
    have hb₀b₀ : b₀ * b₀ = -1 := sq_eq_of_not_mem hquat hzP' hCP hCc hCcard hb₀P hb₀C
    have hconj := conj_eq_inv_of_not_mem hquat hzP' hCP hCc hCcard hb₀P hb₀C haC
    have haP : a ∈ (P : Subgroup SL(2, GaloisField p f)) := hCP haC
    have hcen : (-1 : SL(2, GaloisField p f)) * a = a * (-1) :=
      (uniqueInvolution_comm hzP' haP).symm
    have hz2 : (-1 : SL(2, GaloisField p f)) * -1 = 1 := hz.sq
    have hainv : a⁻¹ = (-1) * a := by
      apply inv_eq_of_mul_eq_one_right
      calc a * ((-1) * a) = (a * (-1)) * a := by group
        _ = ((-1) * a) * a := by rw [← hcen]
        _ = (-1) * (a * a) := by group
        _ = 1 := by rw [haa, hz2]
    have hab : a * b₀ = (-1) * (b₀ * a) := by
      have h1 : b₀ * a = a⁻¹ * b₀ := mul_inv_eq_iff_eq_mul.mp hconj
      rw [h1, hainv]
      calc a * b₀ = (-1) * (-1) * (a * b₀) := by rw [hz2, one_mul]
        _ = (-1) * ((-1) * a * b₀) := by group
    have hfa : semilinHom G 1 a = a := by rw [← hβσ]; exact hfix a haP
    have hfb : semilinHom G 1 b₀ = b₀ := by rw [← hβσ]; exact hfix b₀ hb₀P
    have hF2' : (2 : GaloisField p f) ≠ 0 := by
      intro h2
      have : ringChar (GaloisField p f) ∣ 2 := ringChar.dvd (by exact_mod_cast h2)
      have hdvd : p ∣ 2 := by rwa [ringChar.eq (GaloisField p f) p] at this
      have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd
      exact hp this
    have hid := semilinHom_one_eq_id hF2' G a b₀ haa hb₀b₀ hab hfa hfb
    ext x
    rw [hβσ, hid]
    rfl
  · exact absurd (false_of_fixes_diag hp hq hσ2 hσ hμ (by rw [← hβσ]; exact hfix _ hx₀)) id

theorem mulAut_involution_eq_one (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (β : MulAut SL(2, GaloisField p f)) (hβ : β * β = 1) (P : Sylow 2 SL(2, GaloisField p f))
    (hfix : ∀ x ∈ P, β x = x) : β = 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hN0 : p ^ f - 1 ≠ 0 := by omega
  obtain ⟨μ, hμ⟩ : ∃ μ : (GaloisField p f)ˣ, orderOf μ = 2 ^ padicValNat 2 (p ^ f - 1) := by
    have hcardU : Nat.card (GaloisField p f)ˣ = p ^ f - 1 := by rw [Nat.card_units, hcard]
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p f)ˣ)
    have hgord : orderOf g = p ^ f - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardU]
    have hM : 2 ^ padicValNat 2 (p ^ f - 1) ∣ p ^ f - 1 := pow_padicValNat_dvd
    have hM0 : 0 < 2 ^ padicValNat 2 (p ^ f - 1) := by positivity
    have hdvd : (p ^ f - 1) / 2 ^ padicValNat 2 (p ^ f - 1) ∣ orderOf g := by
      rw [hgord]
      exact Nat.div_dvd_of_dvd hM
    have hq0 : (p ^ f - 1) / 2 ^ padicValNat 2 (p ^ f - 1) ≠ 0 := by
      intro h0
      have := Nat.div_eq_zero_iff.mp h0
      have := Nat.le_of_dvd (by omega) hM
      omega
    refine ⟨g ^ ((p ^ f - 1) / 2 ^ padicValNat 2 (p ^ f - 1)), ?_⟩
    rw [orderOf_pow_of_dvd hq0 hdvd, hgord, Nat.div_div_self hM hN0]
  set x₀ : SL(2, GaloisField p f) := diagHom μ with hx₀
  have hx₀pow : x₀ ^ (2 ^ padicValNat 2 (p ^ f - 1)) = 1 := by
    rw [hx₀, ← map_pow, ← hμ, pow_orderOf_eq_one, map_one]
  have hx₀2 : IsPGroup 2 ↥(Subgroup.zpowers x₀) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx₀pow)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨P₀, hP₀⟩ := hx₀2.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq SL(2, GaloisField p f) P₀ P
  set c : MulAut SL(2, GaloisField p f) := MulAut.conj h with hc
  have hmem : ∀ y ∈ P₀, c y ∈ P := by
    intro y hy
    have h1 : (MulAut.conj h) • y ∈ (MulAut.conj h) • (P₀ : Subgroup SL(2, GaloisField p f)) :=
      Subgroup.smul_mem_pointwise_smul y (MulAut.conj h) _ hy
    rw [← Sylow.coe_subgroup_smul, hh] at h1
    exact h1
  have hβ' : (c⁻¹ * β * c) * (c⁻¹ * β * c) = 1 := by
    calc (c⁻¹ * β * c) * (c⁻¹ * β * c) = c⁻¹ * (β * β) * c := by group
      _ = 1 := by rw [hβ]; group
  have hfix' : ∀ x ∈ P₀, (c⁻¹ * β * c) x = x := by
    intro x hx
    have h1 : β (c x) = c x := hfix _ (hmem x hx)
    simp only [MulAut.mul_apply, h1]
    simp
  have hx₀P₀ : diagHom μ ∈ P₀ := hP₀ (Subgroup.mem_zpowers x₀)
  have h1 := mulAut_involution_eq_one_of_mem hp hq (c⁻¹ * β * c) hβ' P₀ hfix' μ hμ hx₀P₀
  calc β = c * (c⁻¹ * β * c) * c⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem mulAut_eq_one_of_pow_two_pow_eq_one (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (P : Sylow 2 SL(2, GaloisField p f)) (n : ℕ) :
    ∀ β : MulAut SL(2, GaloisField p f), β ^ 2 ^ n = 1 → (∀ x ∈ P, β x = x) → β = 1 := by
  induction n with
  | zero =>
    intro β hβ _
    simpa using hβ
  | succ n ih =>
    intro β hβ hfix
    have hγ : (β ^ 2 ^ n) * (β ^ 2 ^ n) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      exact hβ
    have hpowfix : ∀ m : ℕ, ∀ x ∈ P, (β ^ m) x = x := by
      intro m x hx
      induction m with
      | zero => simp
      | succ m ihm =>
        rw [pow_succ, MulAut.mul_apply, hfix x hx, ihm]
    have h1 : β ^ 2 ^ n = 1 :=
      mulAut_involution_eq_one hp hq _ hγ P (fun x hx => hpowfix _ x hx)
    exact ih β h1 hfix

theorem mulAut_trivial_quotient_of_fixes_sylow {K : Type} [Group K] (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (N : Subgroup K) [N.Normal] (e : K ⧸ N ≃* SL(2, GaloisField p f))
    (α : MulAut K) (hαN : N.map (α : K →* K) = N) (n : ℕ) (hα : α ^ 2 ^ n = 1)
    (P : Sylow 2 SL(2, GaloisField p f))
    (hfix : ∀ x ∈ P, ∃ r : K, e (QuotientGroup.mk r) = x ∧ e (QuotientGroup.mk (α r)) = x) :
    ∀ k : K, (QuotientGroup.mk (α k) : K ⧸ N) = QuotientGroup.mk k := by
  set ᾱ : MulAut (K ⧸ N) := QuotientGroup.congr N N (α : K ≃* K) hαN with hᾱ
  have hᾱmk : ∀ x : K, ᾱ (QuotientGroup.mk x) = QuotientGroup.mk (α x) := fun x => rfl
  have hpow : ∀ (m : ℕ) (x : K), (ᾱ ^ m) (QuotientGroup.mk x) =
      QuotientGroup.mk ((α ^ m) x) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, hᾱmk, ih, pow_succ, MulAut.mul_apply]
  have hᾱn : ᾱ ^ 2 ^ n = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => rw [hpow, hα]; rfl
  have hβn : (MulAut.congr e) ᾱ ^ 2 ^ n = 1 := by
    rw [← map_pow, hᾱn, map_one]
  have hβfix : ∀ x ∈ P, (MulAut.congr e) ᾱ x = x := by
    intro x hx
    obtain ⟨r, hr1, hr2⟩ := hfix x hx
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply]
    have : e.symm x = QuotientGroup.mk r := by rw [← hr1]; simp
    rw [this, hᾱmk]
    exact hr2
  have h1 := mulAut_eq_one_of_pow_two_pow_eq_one hp hq P n _ hβn hβfix
  intro k
  have h2 : (MulAut.congr e) ᾱ (e (QuotientGroup.mk k)) = e (QuotientGroup.mk k) := by
    rw [h1]; rfl
  rw [MulAut.congr_apply] at h2
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
  exact e.injective h2

theorem centSylow {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) : CentSylow Ω := by
  intro K R V hK hR hV2 hVK hcomm k hk v hv
  obtain ⟨e⟩ := hΩ.nonempty_equiv_sl2 hK
  have hvN : v ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_conjSub_eq.mpr (hVK v hv)
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨v, hvN⟩ with hα
  have hαN : (classicalInvolutionOddCore ↥K).map (α : ↥K →* ↥K) =
      classicalInvolutionOddCore ↥K :=
    CFSG.ComponentClassification.OddCore.equiv_invariant (α : ↥K ≃* ↥K)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, orderOf v = 2 ^ n := orderOf_eq_two_pow_of_isPGroup hV2 hv
  have hαn : α ^ 2 ^ n = 1 := by
    rw [hα, ← map_pow]
    have : (⟨v, hvN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← hn, pow_orderOf_eq_one]
    rw [this, map_one]
  let φ : ↥K →* SL(2, GaloisField p f) :=
    (e : ↥K ⧸ classicalInvolutionOddCore ↥K →* SL(2, GaloisField p f)).comp
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥K))
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P : Sylow 2 SL(2, GaloisField p f) :=
    Sylow.mapSurjective (f := φ) hφs (sylowOfIsSylow2In'' hR)
  have hfix : ∀ x ∈ P, ∃ r : ↥K, e (QuotientGroup.mk r) = x ∧ e (QuotientGroup.mk (α r)) = x := by
    intro x hx
    have hx' : x ∈ ((sylowOfIsSylow2In'' hR : Subgroup ↥K)).map φ := by
      have := Sylow.coe_mapSurjective (f := φ) hφs (sylowOfIsSylow2In'' hR)
      rw [← this]
      exact hx
    obtain ⟨r, hr, rfl⟩ := hx'
    have hrR : (r : G) ∈ R := hr
    have hvr : v * (r : G) * v⁻¹ = r := by
      rw [← hcomm r hrR v hv]
      group
    have hαr : α r = r := by
      apply Subtype.ext
      rw [hα]
      simpa using hvr
    exact ⟨r, rfl, by rw [hαr]; rfl⟩
  have h1 := mulAut_trivial_quotient_of_fixes_sylow hp hq _ e α hαN n hαn P hfix ⟨k, hk⟩
  have h2 : (α ⟨k, hk⟩ : ↥K) * (⟨k, hk⟩ : ↥K)⁻¹ ∈ classicalInvolutionOddCore ↥K := by
    rw [← div_eq_mul_inv, ← QuotientGroup.eq_iff_div_mem]
    exact h1
  have h3 : ((α ⟨k, hk⟩ : ↥K) : G) = v * k * v⁻¹ := by
    rw [hα]
    simp
  have hmem : ⁅v, k⁆ ∈ K := by
    rw [commutatorElement_def]
    have := (α ⟨k, hk⟩).2
    rw [h3] at this
    exact K.mul_mem this (K.inv_mem hk)
  refine mem_oddCoreOf_iff.mpr ⟨hmem, ?_⟩
  convert h2 using 1
  apply Subtype.ext
  simp [h3, commutatorElement_def]

end CFSG.ClassicalInvolution.Asc77.AscL62
