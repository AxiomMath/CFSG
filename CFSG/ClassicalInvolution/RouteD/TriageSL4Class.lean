module

public import CFSG.ClassicalInvolution.RouteD.GapsD4AAmbient
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open scoped MatrixGroups Matrix
open CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction CFSG.ClassicalInvolution.Models

variable {F : Type} [Field F]

@[expose] def blockEnt (μ : Fˣ) (i : Fin (3 + 1)) : Fˣ := if i.val < 2 then 1 else μ

@[expose] noncomputable def sl4Torus (a : Fˣ) : SL(3 + 1, F) :=
  ⟨Matrix.diagonal fun i : Fin (3 + 1) => if i.val < 2 then (a : F) else ((a⁻¹ : Fˣ) : F), by
    rw [Matrix.det_diagonal, Fin.prod_univ_four]
    simp⟩

@[expose] noncomputable def sl4Pair (b : Fˣ) : SL(3 + 1, F) :=
  ⟨Matrix.diagonal fun i : Fin (3 + 1) =>
    if i.val = 0 then (b : F) else if i.val = 2 then ((b⁻¹ : Fˣ) : F) else 1, by
    rw [Matrix.det_diagonal, Fin.prod_univ_four]
    simp⟩

theorem sl4Pair_mul (a b : Fˣ) : (sl4Pair a * sl4Pair b : SL(3 + 1, F)) = sl4Pair (a * b) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  show Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp [mul_comm]

theorem sl4Pair_one : (sl4Pair (1 : Fˣ) : SL(3 + 1, F)) = 1 := by
  refine Subtype.ext ?_
  show Matrix.diagonal _ = (1 : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F)
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem sl4Pair_inv (b : Fˣ) : (sl4Pair b : SL(3 + 1, F))⁻¹ = sl4Pair b⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [sl4Pair_mul, mul_inv_cancel, sl4Pair_one])

theorem blocks_classification [Finite F] (h5 : 5 ≤ Nat.card F)
    (hcl : LinearAutClassification F (3 + 1)) {Y : Type} [Group Y] (θ : SL(3 + 1, F) →* Y)
    (hker : θ.ker ≤ Subgroup.center SL(3 + 1, F)) (σ : Y ≃* Y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix₀ : ∀ A : SL(2, F), σ (θ (blockSL2 F 3 0 A)) = θ (blockSL2 F 3 0 A))
    (hfix₂ : ∀ A : SL(2, F), σ (θ (blockSL2 F 3 2 A)) = θ (blockSL2 F 3 2 A)) [Finite Y] :
    (∃ μ : Fˣ, ∀ x, σ (θ x) = θ (slConjugation (3 + 1) F (diagGL (blockEnt μ)) x)) ∨
      ((∀ b : Fˣ, σ (θ (sl4Pair b)) = θ (sl4Torus b⁻¹) * θ (sl4Pair b)) ∧
        ∀ x, σ (σ (θ x)) = θ x) := by
  classical
  have h4 : 4 ≤ Nat.card F := by omega
  have hQ : θ.range.map σ.toMonoidHom = θ.range := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, rfl⟩ := hy
      exact hstab x
    · rw [Subgroup.card_map_of_injective σ.injective]
  have hcoe : ∀ x, ((θ.rangeRestrict x : θ.range) : Y) = θ x := fun x => rfl
  obtain ⟨α, g, φ, ε, hαθ', hαmat⟩ := hcl θ.range θ.rangeRestrict θ.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hker) (restrictAut σ θ.range hQ)
  have hαθ : ∀ x, θ (α x) = σ (θ x) := fun x => by
    have := congrArg Subtype.val (hαθ' x)
    simpa [coe_restrictAut, hcoe] using this
  have hαfix : ∀ (a : Fin 3), (∀ A : SL(2, F), σ (θ (blockSL2 F 3 a A)) = θ (blockSL2 F 3 a A)) →
      ∀ A : SL(2, F), α (blockSL2 F 3 a A) = blockSL2 F 3 a A := by
    intro a hfix A
    have hP2 : Group.IsPerfect SL(2, F) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
    have := hom_eq_of_central_ker θ hker (L := SL(2, F)) (α.comp (blockSL2 F 3 a))
      (blockSL2 F 3 a) (fun A => by rw [MonoidHom.comp_apply, hαθ, hfix A])
    exact DFunLike.congr_fun this A
  have hαfix₀ := hαfix 0 hfix₀
  have hαfix₂ := hαfix 2 hfix₂
  have hup : ∀ a : Fin 3, (∀ A : SL(2, F), α (blockSL2 F 3 a A) = blockSL2 F 3 a A) → ∀ c : F,
      α (Matrix.SpecialLinearGroup.transvection
        (Fin.castSucc_lt_succ.ne : a.castSucc ≠ a.succ) c) =
        Matrix.SpecialLinearGroup.transvection
          (Fin.castSucc_lt_succ.ne : a.castSucc ≠ a.succ) c := by
    intro a ha c
    have := ha (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c)
    rwa [blockSL2_transvection_up] at this
  have hdown : ∀ a : Fin 3, (∀ A : SL(2, F), α (blockSL2 F 3 a A) = blockSL2 F 3 a A) → ∀ c : F,
      α (Matrix.SpecialLinearGroup.transvection
        (Fin.castSucc_lt_succ.ne' : a.succ ≠ a.castSucc) c) =
        Matrix.SpecialLinearGroup.transvection
          (Fin.castSucc_lt_succ.ne' : a.succ ≠ a.castSucc) c := by
    intro a ha c
    have := ha (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c)
    rwa [blockSL2_transvection_down] at this
  cases ε
  ·
    left
    simp only [Bool.false_eq_true, ↓reduceIte] at hαmat
    obtain ⟨hφ, hc1⟩ := fixed_transvection_false α g φ hαmat _ (hup 0 hαfix₀)
    have hc2 := (fixed_transvection_false α g φ hαmat _ (hdown 0 hαfix₀)).2
    obtain ⟨h00, -, -, hrow0, hrow1⟩ := block_of_commute_single _ hc1 hc2
    have hc1' := (fixed_transvection_false α g φ hαmat _ (hup 2 hαfix₂)).2
    have hc2' := (fixed_transvection_false α g φ hαmat _ (hdown 2 hαfix₂)).2
    obtain ⟨h22, -, -, hrow2, hrow3⟩ := block_of_commute_single _ hc1' hc2'
    have hoff : ∀ i j : Fin (3 + 1), i ≠ j →
        (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) i j = 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · exact hrow0 1 (by decide)
      · exact hrow0 2 (by decide)
      · exact hrow0 3 (by decide)
      · exact hrow1 0 (by decide)
      · exact hrow1 2 (by decide)
      · exact hrow1 3 (by decide)
      · exact hrow2 0 (by decide)
      · exact hrow2 1 (by decide)
      · exact hrow2 3 (by decide)
      · exact hrow3 0 (by decide)
      · exact hrow3 1 (by decide)
      · exact hrow3 2 (by decide)
    obtain ⟨u, rfl⟩ := exists_diagGL_of_offdiag_zero g hoff
    have hu01 : u 0 = u 1 := by
      have := h00
      rw [coe_diagGL, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at this
      exact Units.ext this
    have hu23 : u 2 = u 3 := by
      have := h22
      rw [coe_diagGL, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at this
      exact Units.ext this
    have hαconj : ∀ x, α x = slConjugation (3 + 1) F (diagGL u) x := by
      intro x
      refine Subtype.ext ?_
      rw [hαmat x, slConjugation_matrix]
      congr 2
      ext a b
      simp [RingEquiv.mapMatrix_apply, hφ]
    set μ : Fˣ := u 2 * (u 0)⁻¹ with hμdef
    have hentry : ∀ i : Fin (3 + 1), u i = u 0 * blockEnt μ i := by
      intro i
      fin_cases i
      · simp [blockEnt]
      · simp [blockEnt, hu01]
      · simp [blockEnt, hμdef]
      · simp [blockEnt, hμdef, ← hu23]
    refine ⟨μ, fun x => ?_⟩
    rw [← hαθ, hαconj]
    congr 1
    exact slConjugation_diagGL_congr u _ (u 0) hentry x
  ·
    right
    simp only [↓reduceIte] at hαmat
    obtain ⟨hφ, h1⟩ := fixed_transvection_true α g φ hαmat _ (hup 0 hαfix₀)
    obtain ⟨-, h2'⟩ := fixed_transvection_true α g φ hαmat _ (hdown 0 hαfix₀)
    obtain ⟨-, hl1, -, hl0, hij0⟩ := block_of_graph_commute _ h1 h2'
    obtain ⟨-, h3⟩ := fixed_transvection_true α g φ hαmat _ (hup 2 hαfix₂)
    obtain ⟨-, h4⟩ := fixed_transvection_true α g φ hαmat _ (hdown 2 hαfix₂)
    obtain ⟨-, hl3, -, hl2, hij2⟩ := block_of_graph_commute _ h3 h4
    set G : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F := (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F)
      with hG
    set Gi : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F :=
      ((g⁻¹ : GL (Fin (3 + 1)) F) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) with hGi
    have hGGi : G * Gi = 1 := Units.mul_inv g
    have hα' : ∀ x, ((α x : SL(3 + 1, F)) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) =
        G * (((x⁻¹ : SL(3 + 1, F)) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F))ᵀ * Gi := by
      intro x
      rw [hαmat x]
      congr 2
      ext a b
      simp [RingEquiv.mapMatrix_apply, hφ]
    have g00 : G 0 0 = 0 := hl0 0 (by decide)
    have g02 : G 0 2 = 0 := hl0 2 (by decide)
    have g03 : G 0 3 = 0 := hl0 3 (by decide)
    have g11 : G 1 1 = 0 := hl1 1 (by decide)
    have g12 : G 1 2 = 0 := hl1 2 (by decide)
    have g13 : G 1 3 = 0 := hl1 3 (by decide)
    have g20 : G 2 0 = 0 := hl2 0 (by decide)
    have g21 : G 2 1 = 0 := hl2 1 (by decide)
    have g22 : G 2 2 = 0 := hl2 2 (by decide)
    have g30 : G 3 0 = 0 := hl3 0 (by decide)
    have g31 : G 3 1 = 0 := hl3 1 (by decide)
    have g33 : G 3 3 = 0 := hl3 3 (by decide)
    have hij0' : G 0 1 = -G 1 0 := hij0
    have hij2' : G 2 3 = -G 3 2 := hij2
    have g10 : G 1 0 = -G 0 1 := by linear_combination hij0'
    have g32 : G 3 2 = -G 2 3 := by linear_combination hij2'
    have hskew : Gᵀ = -G := by
      ext k l
      fin_cases k <;> fin_cases l <;>
        simp [Matrix.transpose_apply, g00, g02, g03, g11, g12, g13, g20, g21, g22, g30, g31, g33]
      · linear_combination g10
      · linear_combination hij0'
      · linear_combination g32
      · linear_combination hij2'
    have hGiT : Giᵀ = -Gi := by
      have hT1 : Giᵀ * Gᵀ = 1 := by
        rw [← Matrix.transpose_mul, hGGi, Matrix.transpose_one]
      rw [hskew] at hT1
      have hGiG : Gi * G = 1 := Units.inv_mul g
      calc Giᵀ = Giᵀ * (G * Gi) := by rw [hGGi, Matrix.mul_one]
        _ = -((Giᵀ * -G) * Gi) := by noncomm_ring
        _ = -Gi := by rw [hT1, Matrix.one_mul]
    have hsq : ∀ x, α (α x) = x := by
      intro x
      refine Subtype.ext ?_
      rw [hα' (α x), ← map_inv, hα' (x⁻¹), inv_inv, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, hGiT, hskew]
      calc G * (-Gi * ((x : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) * -G)) * Gi
          = (G * Gi) * (x : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) * (G * Gi) := by noncomm_ring
        _ = _ := by rw [hGGi, Matrix.one_mul, Matrix.mul_one]
    have hcommP : ∀ b : Fˣ, G * ((sl4Pair b⁻¹ : SL(3 + 1, F)) :
        Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) = ((sl4Torus b⁻¹ * sl4Pair b : SL(3 + 1, F)) :
        Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) * G := by
      intro b
      rw [Matrix.SpecialLinearGroup.coe_mul]
      show G * Matrix.diagonal _ = (Matrix.diagonal _ * Matrix.diagonal _) * G
      rw [Matrix.diagonal_mul_diagonal]
      ext k l
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      fin_cases k <;> fin_cases l <;>
        simp [g00, g02, g03, g11, g12, g13, g20, g21, g22, g30, g31, g33] <;> ring
    have hαp : ∀ b : Fˣ, α (sl4Pair b) = sl4Torus b⁻¹ * sl4Pair b := by
      intro b
      refine Subtype.ext ?_
      rw [hα' (sl4Pair b), sl4Pair_inv]
      have hsym : ((sl4Pair b⁻¹ : SL(3 + 1, F)) :
          Matrix (Fin (3 + 1)) (Fin (3 + 1)) F)ᵀ = ((sl4Pair b⁻¹ : SL(3 + 1, F)) :
          Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) := by
        show (Matrix.diagonal _)ᵀ = Matrix.diagonal _
        rw [Matrix.diagonal_transpose]
      rw [hsym]
      exact conj_eq_of_mul_eq g (hcommP b)
    exact ⟨fun b => by rw [← hαθ, hαp b, map_mul], fun x => by rw [← hαθ x, ← hαθ (α x), hsq x]⟩

theorem blockEnt_eq_of_involution [Finite F] {Y : Type} [Group Y] (θ : SL(3 + 1, F) →* Y)
    (hker : θ.ker ≤ Subgroup.center SL(3 + 1, F)) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y) (μ : Fˣ)
    (hμ : ∀ x, σ (θ x) = θ (slConjugation (3 + 1) F (diagGL (blockEnt μ)) x)) :
    μ = 1 ∨ μ = -1 := by
  have : Group.IsPerfect SL(3 + 1, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by omega)
  have hsq : ∀ x : SL(3 + 1, F), slConjugation (3 + 1) F (diagGL (blockEnt μ))
      (slConjugation (3 + 1) F (diagGL (blockEnt μ)) x) = x := by
    have := hom_eq_of_central_ker θ hker (L := SL(3 + 1, F))
      ((slConjugation (3 + 1) F (diagGL (blockEnt μ))).toMonoidHom.comp
        (slConjugation (3 + 1) F (diagGL (blockEnt μ))).toMonoidHom) (MonoidHom.id _)
      (fun x => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
        rw [← hμ, ← hμ, hσ])
    intro x
    exact DFunLike.congr_fun this x
  have h1 := sq_eq_of_conj_sq (blockEnt μ) (i := 2) (j := 0) (by decide) hsq
  have h2 : (μ : F) ^ 2 = 1 := by simpa [blockEnt] using h1
  have h3 : (μ : F) * μ = 1 := by linear_combination h2
  rcases mul_self_eq_one_iff.mp h3 with h4 | h4
  · exact Or.inl (Units.ext h4)
  · exact Or.inr (Units.ext (by rw [Units.val_neg]; exact h4))

theorem conj_negOne_block4 (x : SL(3 + 1, F)) :
    slConjugation (3 + 1) F (diagGL (blockEnt (-1)))
      (blockSL2 F 3 0 (-1) * x * (blockSL2 F 3 0 (-1))⁻¹) = x := by
  have hr : (blockSL2 F 3 0 (-1))⁻¹ = blockSL2 F 3 0 (-1) := by
    rw [← map_inv]
    congr 1
    exact inv_eq_of_mul_eq_one_right (by simp)
  rw [hr]
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [slConjugation_diagGL_apply, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  have hc : ((blockSL2 F 3 0 (-1) : SL(3 + 1, F)) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) =
      Matrix.diagonal (fun a : Fin (3 + 1) => if a.val < 2 then (-1 : F) else 1) := by
    rw [show blockSL2 F 3 0 (-1) = blockSL F (3 + 1) 2 0 (by omega) (-1) from rfl,
      coe_blockSL_neg_one (by omega), negBlock_eq_diagonal]
    congr 1
    funext a
    simp
  rw [hc, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [blockEnt]

theorem sq_eq_one_of_sl4Torus_center (c : Fˣ)
    (h : (sl4Torus c : SL(3 + 1, F)) ∈ Subgroup.center SL(3 + 1, F)) : c ^ 2 = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have e0 := congrFun (congrFun hr 0) 0
  have e2 := congrFun (congrFun hr 2) 2
  simp [sl4Torus, Matrix.scalar_apply] at e0 e2
  have h1 := e0.symm.trans e2
  have hc : (c : F) ≠ 0 := c.ne_zero
  have h2 : (c : F) ^ 2 = 1 := by
    field_simp at h1
    linear_combination h1
  exact Units.ext (by simpa using h2)

theorem coe_blockSL2_negOne_zero :
    ((blockSL2 F 3 0 (-1) : SL(3 + 1, F)) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) =
      Matrix.diagonal (fun a : Fin (3 + 1) => if a.val < 2 then (-1 : F) else 1) := by
  rw [show blockSL2 F 3 0 (-1) = blockSL F (3 + 1) 2 0 (by omega) (-1) from rfl,
    coe_blockSL_neg_one (by omega), negBlock_eq_diagonal]
  congr 1
  funext a
  simp

theorem slConjugation_blockEnt_one (x : SL(3 + 1, F)) :
    slConjugation (3 + 1) F (diagGL (blockEnt 1)) x = x := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [slConjugation_diagGL_apply]
  simp [blockEnt]

theorem sl4Pair_comm_negOne (b : Fˣ) :
    sl4Pair b * blockSL2 F 3 0 (-1) = blockSL2 F 3 0 (-1) * sl4Pair b := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_blockSL2_negOne_zero]
  show Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end CFSG.ClassicalInvolution.RouteD.Gaps
