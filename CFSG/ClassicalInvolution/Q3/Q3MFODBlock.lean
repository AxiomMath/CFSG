module

public import CFSG.ClassicalInvolution.Q3.Q3MFODSimE
public import CFSG.ClassicalInvolution.Q3.Q3MFODSim
public import CFSG.ClassicalInvolution.Q3.Q3NMBlocks
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Aut
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Center
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Split

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOD

open Matrix CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalGroups.Orthogonal.Small QuadraticMap CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Std

variable {F : Type} [Field F]

@[expose] def dsign (F : Type) [Field F] : Fin 4 ⊕ Fin 4 → F := Sum.elim (fun _ => 1) (fun _ => -1)

theorem dsign_mul_self (μ : Fin 4 ⊕ Fin 4) : dsign F μ * dsign F μ = 1 := by
  rcases μ with i | i <;> simp [dsign]

@[expose] noncomputable def a₀GL (F : Type) [Field F] : GL (Fin 4 ⊕ Fin 4) F :=
  ⟨diagonal (dsign F), diagonal (dsign F),
    by rw [diagonal_mul_diagonal, funext dsign_mul_self, diagonal_one],
    by rw [diagonal_mul_diagonal, funext dsign_mul_self, diagonal_one]⟩

@[expose] noncomputable def a₀ (F : Type) [Field F] :
    (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F) := glLin (a₀GL F)

theorem a₀_apply (v : Fin 4 ⊕ Fin 4 → F) (μ : Fin 4 ⊕ Fin 4) : a₀ F v μ = dsign F μ * v μ := by
  rw [a₀, glLin_apply]
  show (diagonal (dsign F) *ᵥ v) μ = _
  rw [mulVec_diagonal]

theorem quadPlus_a₀ (v : Fin 4 ⊕ Fin 4 → F) : quadPlus 4 F (a₀ F v) = -quadPlus 4 F v := by
  simp only [quadPlus_apply, a₀_apply, dsign, Sum.elim_inl, Sum.elim_inr, one_mul, neg_mul]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Std

section Block

variable {F : Type} [Field F]

@[expose] noncomputable def blockGL (B : GL (Fin 4) F) : GL (Fin 4 ⊕ Fin 4) F :=
  ⟨fromBlocks (B : Matrix (Fin 4) (Fin 4) F) 0 0
      ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ,
    fromBlocks ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0
      (B : Matrix (Fin 4) (Fin 4) F)ᵀ,
    by
      rw [fromBlocks_multiply]
      simp only [zero_mul, mul_zero, add_zero, zero_add]
      rw [Units.mul_inv, ← transpose_mul, Units.mul_inv, transpose_one, fromBlocks_one],
    by
      rw [fromBlocks_multiply]
      simp only [zero_mul, mul_zero, add_zero, zero_add]
      rw [Units.inv_mul, ← transpose_mul, Units.inv_mul, transpose_one, fromBlocks_one]⟩

theorem blockGL_val (B : GL (Fin 4) F) :
    (blockGL B : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) =
      fromBlocks (B : Matrix (Fin 4) (Fin 4) F) 0 0
        ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := rfl

@[expose] noncomputable def blockHom : GL (Fin 4) F →* GL (Fin 4 ⊕ Fin 4) F where
  toFun := blockGL
  map_one' := by
    apply Units.ext
    rw [blockGL_val]
    simp [fromBlocks_one]
  map_mul' A B := by
    apply Units.ext
    rw [Units.val_mul, blockGL_val, blockGL_val, blockGL_val, fromBlocks_multiply]
    simp [_root_.mul_inv_rev, transpose_mul]

theorem blockGL_injective : Function.Injective (blockGL : GL (Fin 4) F → GL (Fin 4 ⊕ Fin 4) F) := by
  intro A B h
  apply Units.ext
  have h' := congrArg (fun M : GL (Fin 4 ⊕ Fin 4) F =>
    (M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F)) h
  simp only [blockGL_val] at h'
  have := congrArg toBlocks₁₁ h'
  simpa using this

theorem quadPlus_blockGL (B : GL (Fin 4) F) (v : Fin 4 ⊕ Fin 4 → F) :
    quadPlus 4 F ((blockGL B : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) *ᵥ v) =
      quadPlus 4 F v := by
  rw [blockGL_val, fromBlocks_mulVec]
  simp only [zero_mulVec, add_zero, zero_add]
  have hD : (B : Matrix (Fin 4) (Fin 4) F)ᵀ * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ =
      1 := by
    rw [← transpose_mul, Units.inv_mul, transpose_one]
  rw [quadPlus_apply, quadPlus_apply]
  have key : ((B : Matrix (Fin 4) (Fin 4) F) *ᵥ (v ∘ Sum.inl)) ⬝ᵥ
      (((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *ᵥ (v ∘ Sum.inr)) =
      (v ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr) := by
    rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, hD, one_mulVec]
  simpa [dotProduct] using key

theorem blockGL_mul_a₀GL (B : GL (Fin 4) F) : blockGL B * a₀GL F = a₀GL F * blockGL B := by
  apply Units.ext
  have hd : (diagonal (dsign F) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) =
      fromBlocks (1 : Matrix (Fin 4) (Fin 4) F) 0 0 (-1 : Matrix (Fin 4) (Fin 4) F) := by
    ext μ ν
    rcases μ with i | i <;> rcases ν with j | j <;>
      simp [diagonal_apply, dsign, Matrix.one_apply]
    split_ifs <;> simp
  rw [Units.val_mul, Units.val_mul, blockGL_val]
  show _ * (diagonal (dsign F)) = (diagonal (dsign F)) * _
  rw [hd, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem diagonal_dsign : (diagonal (dsign F) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) =
    fromBlocks (1 : Matrix (Fin 4) (Fin 4) F) 0 0 (-1 : Matrix (Fin 4) (Fin 4) F) := by
  ext μ ν
  rcases μ with i | i <;> rcases ν with j | j <;>
    simp [diagonal_apply, dsign, Matrix.one_apply]
  split_ifs <;> simp

theorem glLin_inj {ι : Type} [Fintype ι] [DecidableEq ι] {M N : GL ι F}
    (h : glLin M = glLin N) : (M : Matrix ι ι F) = (N : Matrix ι ι F) := by
  have : Matrix.toLin' (M : Matrix ι ι F) = Matrix.toLin' (N : Matrix ι ι F) :=
    LinearMap.ext fun v => by
      simpa [glLin_apply, Matrix.toLin'_apply] using LinearEquiv.congr_fun h v
  exact Matrix.toLin'.injective this

theorem blockGL_mul (A B : GL (Fin 4) F) : blockGL (A * B) = blockGL A * blockGL B :=
  map_mul blockHom A B

theorem blockGL_inv (B : GL (Fin 4) F) : blockGL B⁻¹ = (blockGL B)⁻¹ := map_inv blockHom B

@[expose] noncomputable def embSL (F : Type) [Field F] :
    SL(4, F) →* ((Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) :=
  glLin.comp (blockHom.comp Matrix.SpecialLinearGroup.toGL)

theorem embSL_apply (A : SL(4, F)) :
    embSL F A = glLin (blockGL (Matrix.SpecialLinearGroup.toGL A)) := rfl

theorem embSL_injective : Function.Injective (embSL F) := by
  intro A B h
  rw [embSL_apply, embSL_apply] at h
  have h0 := glLin_inj h
  have h1 : blockGL (Matrix.SpecialLinearGroup.toGL A) =
      blockGL (Matrix.SpecialLinearGroup.toGL B) := Units.ext h0
  have h2 := blockGL_injective h1
  apply Subtype.ext
  exact congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) h2

theorem embSL_mem_orthogonalGroup (A : SL(4, F)) :
    embSL F A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [embSL_apply, glLin_apply]
  exact quadPlus_blockGL _ v

theorem embSL_mul_a₀ (A : SL(4, F)) : embSL F A * a₀ F = a₀ F * embSL F A := by
  rw [embSL_apply, a₀, ← map_mul, ← map_mul, blockGL_mul_a₀GL]

@[expose] noncomputable def conjSL4 (B : GL (Fin 4) F) (A : SL(4, F)) : SL(4, F) :=
  ⟨(B : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) *
    ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F), by
    rw [det_units_conj B (A : Matrix (Fin 4) (Fin 4) F)]
    exact A.2⟩

theorem toGL_conjSL4 (B : GL (Fin 4) F) (A : SL(4, F)) :
    Matrix.SpecialLinearGroup.toGL (conjSL4 B A) =
      B * Matrix.SpecialLinearGroup.toGL A * B⁻¹ := by
  apply Units.ext
  rfl

theorem blockGL_conj_embSL (B : GL (Fin 4) F) (A : SL(4, F)) :
    glLin (blockGL B) * embSL F A * (glLin (blockGL B))⁻¹ = embSL F (conjSL4 B A) := by
  rw [embSL_apply, embSL_apply, toGL_conjSL4, blockGL_mul, blockGL_mul, blockGL_inv, map_mul,
    map_mul, map_inv]

theorem eq_zero_of_eq_neg_matrix (h2 : (2 : F) ≠ 0) {n m : Type} {X : Matrix n m F}
    (h : X = -X) : X = 0 := by
  ext i j
  have h1 := congr_fun (congr_fun h i) j
  have h3 : (2 : F) * X i j = 0 := by
    simp only [Matrix.neg_apply] at h1
    linear_combination h1
  simpa using (mul_eq_zero.mp h3).resolve_left h2

theorem exists_blockGL_of_comm (h2 : (2 : F) ≠ 0)
    {g : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F)) (hc : g * a₀ F = a₀ F * g) :
    ∃ B : GL (Fin 4) F, g = glLin (blockGL B) := by
  classical
  set M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F :=
    LinearMap.toMatrix' (g : (Fin 4 ⊕ Fin 4 → F) →ₗ[F] (Fin 4 ⊕ Fin 4 → F)) with hM
  have hMv : ∀ v, M *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hD : ∀ v, (diagonal (dsign F) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) *ᵥ v = a₀ F v :=
    fun v => by rw [a₀, glLin_apply]; rfl
  have hMD : M * diagonal (dsign F) = diagonal (dsign F) * M := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hD, hMv]
    exact LinearEquiv.congr_fun hc v
  rw [← fromBlocks_toBlocks M, diagonal_dsign, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at hMD
  obtain ⟨-, h12, h21, -⟩ := hMD
  have h12' : M.toBlocks₁₂ = 0 := by
    apply eq_zero_of_eq_neg_matrix h2
    simpa using h12.symm
  have h21' : M.toBlocks₂₁ = 0 := by
    apply eq_zero_of_eq_neg_matrix h2
    simpa using h21
  have hMeq : M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks M, h12', h21']
  have hiso : ∀ x y : Fin 4 → F, (M.toBlocks₁₁ *ᵥ x) ⬝ᵥ (M.toBlocks₂₂ *ᵥ y) = x ⬝ᵥ y := by
    intro x y
    have h1 := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg) (Sum.elim x y)
    rw [← hMv, hMeq, fromBlocks_mulVec] at h1
    simp only [zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl, Sum.elim_comp_inr] at h1
    rw [quadPlus_apply, quadPlus_apply] at h1
    simpa [dotProduct] using h1
  have hMM : M.toBlocks₁₁ᵀ * M.toBlocks₂₂ = 1 := by
    ext i j
    have h1 := hiso (Pi.single i 1) (Pi.single j 1)
    rw [mulVec_single_one, mulVec_single_one] at h1
    simpa [Matrix.mul_apply, dotProduct, Matrix.one_apply, Pi.single_apply, Matrix.col,
      eq_comm] using h1
  have hB2 : M.toBlocks₂₂ᵀ * M.toBlocks₁₁ = 1 := by
    have := congrArg transpose hMM
    simpa [transpose_mul] using this
  have hB1 : M.toBlocks₁₁ * M.toBlocks₂₂ᵀ = 1 := mul_eq_one_comm.mpr hB2
  refine ⟨⟨M.toBlocks₁₁, M.toBlocks₂₂ᵀ, hB1, hB2⟩, ?_⟩
  refine LinearEquiv.ext fun v => ?_
  rw [glLin_apply, blockGL_val, ← hMv]
  congr 1

theorem blockGL_one : blockGL (1 : GL (Fin 4) F) = 1 := map_one blockHom

end Block

section Main

variable {F : Type} [Field F] [Finite F]

theorem scalar_of_commute_toGL {B : GL (Fin 4) F}
    (hB : ∀ A : SL(4, F), B * Matrix.SpecialLinearGroup.toGL A =
      Matrix.SpecialLinearGroup.toGL A * B) :
    ∃ c : F, (B : Matrix (Fin 4) (Fin 4) F) = Matrix.scalar (Fin 4) c := by
  have key : (B : Matrix (Fin 4) (Fin 4) F) ∈ Set.range (Matrix.scalar (Fin 4) : F → _) := by
    refine mem_range_scalar_of_commute_transvectionStruct fun t => ?_
    have h := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F))
      (hB ⟨t.toMatrix, t.det⟩)
    exact h.symm
  obtain ⟨c, hc⟩ := key
  exact ⟨c, hc.symm⟩

theorem blockGL_scalar_sq (hF : Nat.card F = 3) {B : GL (Fin 4) F} {c : F}
    (hc : (B : Matrix (Fin 4) (Fin 4) F) = Matrix.scalar (Fin 4) c) :
    glLin (blockGL B) * glLin (blockGL B) = 1 := by
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 := Units.mul_inv B
    rw [hc, h0, map_zero, zero_mul] at h1
    have := congr_fun (congr_fun h1 0) 0
    simp at this
  have hcc : c * c = 1 := by
    rcases cases_of_card_three hF c with h | h | h
    · exact absurd h hc0
    · rw [h, one_mul]
    · rw [h]; ring
  have hBB : B * B = 1 := by
    apply Units.ext
    rw [Units.val_mul, hc, ← map_mul, hcc, map_one]
    rfl
  rw [← map_mul, ← blockGL_mul, hBB, blockGL_one, map_one]

theorem oddCoreIn_fixed_conjES_a₀ (hF : Nat.card F = 3)
    (hSL : CFSG.Open.IsQuasisimple SL(4, F)) (hSLZ : IsPGroup 2 (Subgroup.center SL(4, F)))
    (hQ : (polarBilin (quadPlus 4 F)).Nondegenerate)
    (hE : elementaryGroup (quadPlus 4 F) = ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F)⁆) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup (quadPlus 4 F))
      (conjES (quadPlus 4 F) hE (neg_ne_zero.mpr one_ne_zero) (g := a₀ F)
        (fun v => by rw [quadPlus_a₀, neg_one_mul])))) = ⊥ := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_card_three hF
  have hμ : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hg : ∀ v, quadPlus 4 F (a₀ F v) = (-1 : F) * quadPlus 4 F v := fun v => by
    rw [quadPlus_a₀, neg_one_mul]
  have hdim : 3 ≤ Module.finrank F (Fin 4 ⊕ Fin 4 → F) := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hZ2 := isPGroup_center_elementaryGroup hF hQ hdim
  have : Group.IsPerfect SL(4, F) := ⟨hSL.1⟩
  have hP : ∀ A : SL(4, F), embSL F A ∈ elementaryGroup (quadPlus 4 F) := by
    intro A
    have hperf : ⁅(embSL F).range, (embSL F).range⁆ = (embSL F).range :=
      Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (embSL F))
    have hle : (embSL F).range ≤ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F) := by
      rintro _ ⟨A, rfl⟩
      exact embSL_mem_orthogonalGroup A
    have h3 : (embSL F).range ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F)⁆ :=
      calc (embSL F).range = ⁅(embSL F).range, (embSL F).range⁆ := hperf.symm
        _ ≤ _ := Subgroup.commutator_mono hle hle
    rw [hE]
    exact h3 ⟨A, rfl⟩
  let embE : SL(4, F) →* ↥(elementaryGroup (quadPlus 4 F)) := (embSL F).codRestrict _ hP
  have hker : ((QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup (quadPlus 4 F)))).comp
      embE).ker ≤ Subgroup.center SL(4, F) := by
    intro A hA
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hA
    rw [Subgroup.mem_center_iff]
    intro B
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hA (embE B))
    apply embSL_injective
    rw [map_mul, map_mul]
    exact h1
  have hno : oddCoreIn (embE.range.map
      (QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup (quadPlus 4 F))))) = ⊥ := by
    have h := oddCoreIn_range_eq_bot_of_isQuasisimple
      ((QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup (quadPlus 4 F)))).comp embE) hSL
      hSLZ hker
    rwa [MonoidHom.range_comp] at h
  refine oddCoreIn_fixed_eq_bot_of_blocks hZ2 _ (ι := Unit) (fun _ => embE.range) ?_ ?_
    (fun _ => hno) ?_
  · intro _ x hx
    obtain ⟨A, rfl⟩ := hx
    exact (mem_fixedSubgroup_conjES hE hμ hg _).mpr (embSL_mul_a₀ A)
  · intro _ b hb x hx
    obtain ⟨A, rfl⟩ := hx
    have hbc := (mem_fixedSubgroup_conjES hE hμ hg b).mp hb
    obtain ⟨B, hB⟩ := exists_blockGL_of_comm h2
      (elementaryGroup_le_orthogonalGroup (quadPlus 4 F) b.2) hbc
    refine ⟨conjSL4 B A, Subtype.ext ?_⟩
    show embSL F (conjSL4 B A) = (b : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) *
      embSL F A * (b : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F))⁻¹
    rw [← blockGL_conj_embSL, ← hB]
  · intro ν hν hcomm
    have hνc := (mem_fixedSubgroup_conjES hE hμ hg ν).mp hν
    obtain ⟨B, hB⟩ := exists_blockGL_of_comm h2
      (elementaryGroup_le_orthogonalGroup (quadPlus 4 F) ν.2) hνc
    have hBA : ∀ A : SL(4, F), B * Matrix.SpecialLinearGroup.toGL A =
        Matrix.SpecialLinearGroup.toGL A * B := by
      intro A
      have h1 := congrArg Subtype.val (hcomm () (embE A) ⟨A, rfl⟩)
      have h1' : (ν : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) * embSL F A =
          embSL F A * (ν : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) := h1
      rw [hB, embSL_apply, ← map_mul, ← map_mul] at h1'
      have h3 := Units.ext (glLin_inj h1')
      rw [← blockGL_mul, ← blockGL_mul] at h3
      exact blockGL_injective h3
    obtain ⟨c, hc⟩ := scalar_of_commute_toGL hBA
    have hsq := blockGL_scalar_sq hF hc
    refine ⟨1, ?_⟩
    have e : ν ^ (2 ^ 1) = ν * ν := by rw [pow_one, _root_.sq]
    rw [e]
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, hB, hsq]
    rfl

end Main

end CFSG.ClassicalInvolution.Q3.Q3MFOD
