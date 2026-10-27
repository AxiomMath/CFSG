module

public import CFSG.ClassicalInvolution.Q3.Q3MFODBlock

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Levi

open Matrix CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalGroups.Orthogonal.Small QuadraticMap CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Std

variable {F : Type} [Field F] {n : ℕ}

@[expose] def dsign (F : Type) [Field F] (n : ℕ) : Fin n ⊕ Fin n → F :=
  Sum.elim (fun _ => 1) (fun _ => -1)

theorem dsign_mul_self (μ : Fin n ⊕ Fin n) : dsign F n μ * dsign F n μ = 1 := by
  rcases μ with i | i <;> simp [dsign]

@[expose] noncomputable def a₀GL (F : Type) [Field F] (n : ℕ) : GL (Fin n ⊕ Fin n) F :=
  ⟨diagonal (dsign F n), diagonal (dsign F n),
    by rw [diagonal_mul_diagonal, funext dsign_mul_self, diagonal_one],
    by rw [diagonal_mul_diagonal, funext dsign_mul_self, diagonal_one]⟩

@[expose] noncomputable def a₀ (F : Type) [Field F] (n : ℕ) :
    (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F) := glLin (a₀GL F n)

theorem a₀_apply (v : Fin n ⊕ Fin n → F) (μ : Fin n ⊕ Fin n) :
    a₀ F n v μ = dsign F n μ * v μ := by
  rw [a₀, glLin_apply]
  show (diagonal (dsign F n) *ᵥ v) μ = _
  rw [mulVec_diagonal]

theorem quadPlus_a₀ (v : Fin n ⊕ Fin n → F) : quadPlus n F (a₀ F n v) = -quadPlus n F v := by
  simp only [quadPlus_apply, a₀_apply, dsign, Sum.elim_inl, Sum.elim_inr, one_mul, neg_mul]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Std

section Block

variable {F : Type} [Field F] {n : ℕ}

@[expose] noncomputable def blockGL (B : GL (Fin n) F) : GL (Fin n ⊕ Fin n) F :=
  ⟨fromBlocks (B : Matrix (Fin n) (Fin n) F) 0 0
      ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    fromBlocks ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) 0 0
      (B : Matrix (Fin n) (Fin n) F)ᵀ,
    by
      rw [fromBlocks_multiply]
      simp only [zero_mul, mul_zero, add_zero, zero_add]
      rw [Units.mul_inv, ← transpose_mul, Units.mul_inv, transpose_one, fromBlocks_one],
    by
      rw [fromBlocks_multiply]
      simp only [zero_mul, mul_zero, add_zero, zero_add]
      rw [Units.inv_mul, ← transpose_mul, Units.inv_mul, transpose_one, fromBlocks_one]⟩

theorem blockGL_val (B : GL (Fin n) F) :
    (blockGL B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      fromBlocks (B : Matrix (Fin n) (Fin n) F) 0 0
        ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ := rfl

@[expose] noncomputable def blockHom : GL (Fin n) F →* GL (Fin n ⊕ Fin n) F where
  toFun := blockGL
  map_one' := by
    apply Units.ext
    rw [blockGL_val]
    simp [fromBlocks_one]
  map_mul' A B := by
    apply Units.ext
    rw [Units.val_mul, blockGL_val, blockGL_val, blockGL_val, fromBlocks_multiply]
    simp [_root_.mul_inv_rev, transpose_mul]

theorem blockGL_injective :
    Function.Injective (blockGL : GL (Fin n) F → GL (Fin n ⊕ Fin n) F) := by
  intro A B h
  apply Units.ext
  have h' := congrArg (fun M : GL (Fin n ⊕ Fin n) F =>
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) h
  simp only [blockGL_val] at h'
  have := congrArg toBlocks₁₁ h'
  simpa using this

theorem quadPlus_blockGL (B : GL (Fin n) F) (v : Fin n ⊕ Fin n → F) :
    quadPlus n F ((blockGL B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) =
      quadPlus n F v := by
  rw [blockGL_val, fromBlocks_mulVec]
  simp only [zero_mulVec, add_zero, zero_add]
  have hD : (B : Matrix (Fin n) (Fin n) F)ᵀ *
      ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ = 1 := by
    rw [← transpose_mul, Units.inv_mul, transpose_one]
  rw [quadPlus_apply, quadPlus_apply]
  have key : ((B : Matrix (Fin n) (Fin n) F) *ᵥ (v ∘ Sum.inl)) ⬝ᵥ
      (((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ *ᵥ (v ∘ Sum.inr)) =
      (v ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr) := by
    rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, hD, one_mulVec]
  simpa [dotProduct] using key

theorem diagonal_dsign : (diagonal (dsign F n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
    fromBlocks (1 : Matrix (Fin n) (Fin n) F) 0 0 (-1 : Matrix (Fin n) (Fin n) F) := by
  ext μ ν
  rcases μ with i | i <;> rcases ν with j | j <;>
    simp [diagonal_apply, dsign, Matrix.one_apply]
  split_ifs <;> simp

theorem blockGL_mul_a₀GL (B : GL (Fin n) F) : blockGL B * a₀GL F n = a₀GL F n * blockGL B := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, blockGL_val]
  show _ * (diagonal (dsign F n)) = (diagonal (dsign F n)) * _
  rw [diagonal_dsign, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem blockGL_mul (A B : GL (Fin n) F) : blockGL (A * B) = blockGL A * blockGL B :=
  map_mul blockHom A B

theorem blockGL_inv (B : GL (Fin n) F) : blockGL B⁻¹ = (blockGL B)⁻¹ := map_inv blockHom B

theorem blockGL_one : blockGL (1 : GL (Fin n) F) = 1 := map_one blockHom

@[expose] noncomputable def embSL (F : Type) [Field F] (n : ℕ) :
    SL(n, F) →* ((Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) :=
  glLin.comp (blockHom.comp Matrix.SpecialLinearGroup.toGL)

theorem embSL_apply (A : SL(n, F)) :
    embSL F n A = glLin (blockGL (Matrix.SpecialLinearGroup.toGL A)) := rfl

theorem embSL_injective : Function.Injective (embSL F n) := by
  intro A B h
  rw [embSL_apply, embSL_apply] at h
  have h0 := Q3MFOD.glLin_inj h
  have h1 : blockGL (Matrix.SpecialLinearGroup.toGL A) =
      blockGL (Matrix.SpecialLinearGroup.toGL B) := Units.ext h0
  have h2 := blockGL_injective h1
  apply Subtype.ext
  exact congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h2

theorem embSL_mem_orthogonalGroup (A : SL(n, F)) :
    embSL F n A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [embSL_apply, glLin_apply]
  exact quadPlus_blockGL _ v

theorem embSL_mul_a₀ (A : SL(n, F)) : embSL F n A * a₀ F n = a₀ F n * embSL F n A := by
  rw [embSL_apply, a₀, ← map_mul, ← map_mul, blockGL_mul_a₀GL]

@[expose] noncomputable def conjSL (B : GL (Fin n) F) (A : SL(n, F)) : SL(n, F) :=
  ⟨(B : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) *
    ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), by
    rw [det_units_conj B (A : Matrix (Fin n) (Fin n) F)]
    exact A.2⟩

theorem toGL_conjSL (B : GL (Fin n) F) (A : SL(n, F)) :
    Matrix.SpecialLinearGroup.toGL (conjSL B A) =
      B * Matrix.SpecialLinearGroup.toGL A * B⁻¹ := by
  apply Units.ext
  rfl

theorem blockGL_conj_embSL (B : GL (Fin n) F) (A : SL(n, F)) :
    glLin (blockGL B) * embSL F n A * (glLin (blockGL B))⁻¹ = embSL F n (conjSL B A) := by
  rw [embSL_apply, embSL_apply, toGL_conjSL, blockGL_mul, blockGL_mul, blockGL_inv, map_mul,
    map_mul, map_inv]

theorem exists_blockGL_of_comm (h2 : (2 : F) ≠ 0)
    {g : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F))
    (hc : g * a₀ F n = a₀ F n * g) : ∃ B : GL (Fin n) F, g = glLin (blockGL B) := by
  classical
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    LinearMap.toMatrix' (g : (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F)) with hM
  have hMv : ∀ v, M *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hD : ∀ v, (diagonal (dsign F n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v =
      a₀ F n v := fun v => by rw [a₀, glLin_apply]; rfl
  have hMD : M * diagonal (dsign F n) = diagonal (dsign F n) * M := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hD, hMv]
    exact LinearEquiv.congr_fun hc v
  rw [← fromBlocks_toBlocks M, diagonal_dsign, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at hMD
  obtain ⟨-, h12, h21, -⟩ := hMD
  have h12' : M.toBlocks₁₂ = 0 := by
    apply Q3MFOD.eq_zero_of_eq_neg_matrix h2
    simpa using h12.symm
  have h21' : M.toBlocks₂₁ = 0 := by
    apply Q3MFOD.eq_zero_of_eq_neg_matrix h2
    simpa using h21
  have hMeq : M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks M, h12', h21']
  have hiso : ∀ x y : Fin n → F, (M.toBlocks₁₁ *ᵥ x) ⬝ᵥ (M.toBlocks₂₂ *ᵥ y) = x ⬝ᵥ y := by
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

end Block

section Main

variable {F : Type} [Field F] [Finite F] {n : ℕ}

omit [Finite F] in
theorem scalar_of_commute_toGL {B : GL (Fin n) F}
    (hB : ∀ A : SL(n, F), B * Matrix.SpecialLinearGroup.toGL A =
      Matrix.SpecialLinearGroup.toGL A * B) :
    ∃ c : F, (B : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) c := by
  have key : (B : Matrix (Fin n) (Fin n) F) ∈ Set.range (Matrix.scalar (Fin n) : F → _) := by
    refine mem_range_scalar_of_commute_transvectionStruct fun t => ?_
    have h := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F))
      (hB ⟨t.toMatrix, t.det⟩)
    exact h.symm
  obtain ⟨c, hc⟩ := key
  exact ⟨c, hc.symm⟩

theorem blockGL_scalar_sq (hF : Nat.card F = 3) (hn : 1 ≤ n) {B : GL (Fin n) F} {c : F}
    (hc : (B : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) c) :
    glLin (blockGL B) * glLin (blockGL B) = 1 := by
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 := Units.mul_inv B
    rw [hc, h0, map_zero, zero_mul] at h1
    have := congr_fun (congr_fun h1 ⟨0, hn⟩) ⟨0, hn⟩
    simp at this
  have hcc : c * c = 1 := by
    rcases Q3MFOD.cases_of_card_three hF c with h | h | h
    · exact absurd h hc0
    · rw [h, one_mul]
    · rw [h]; ring
  have hBB : B * B = 1 := by
    apply Units.ext
    rw [Units.val_mul, hc, ← map_mul, hcc, map_one]
    rfl
  rw [← map_mul, ← blockGL_mul, hBB, blockGL_one, map_one]

theorem oddCoreIn_fixed_conjES_a₀ (hF : Nat.card F = 3) (hn : 2 ≤ n)
    (hSL : CFSG.Open.IsQuasisimple SL(n, F)) (hSLZ : IsPGroup 2 (Subgroup.center SL(n, F)))
    (hQ : (polarBilin (quadPlus n F)).Nondegenerate)
    (hE : elementaryGroup (quadPlus n F) = ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F)⁆) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup (quadPlus n F))
      (Q3MFOD.conjES (quadPlus n F) hE (neg_ne_zero.mpr one_ne_zero) (g := a₀ F n)
        (fun v => by rw [quadPlus_a₀, neg_one_mul])))) = ⊥ := by
  classical
  have h2 : (2 : F) ≠ 0 := Q3MFOD.two_ne_zero_of_card_three hF
  have hμ : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hg : ∀ v, quadPlus n F (a₀ F n v) = (-1 : F) * quadPlus n F v := fun v => by
    rw [quadPlus_a₀, neg_one_mul]
  have hdim : 3 ≤ Module.finrank F (Fin n ⊕ Fin n → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hZ2 := isPGroup_center_elementaryGroup hF hQ hdim
  have : Group.IsPerfect SL(n, F) := ⟨hSL.1⟩
  have hP : ∀ A : SL(n, F), embSL F n A ∈ elementaryGroup (quadPlus n F) := by
    intro A
    have hperf : ⁅(embSL F n).range, (embSL F n).range⁆ = (embSL F n).range :=
      Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (embSL F n))
    have hle : (embSL F n).range ≤ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F) := by
      rintro _ ⟨A, rfl⟩
      exact embSL_mem_orthogonalGroup A
    have h3 : (embSL F n).range ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F)⁆ :=
      calc (embSL F n).range = ⁅(embSL F n).range, (embSL F n).range⁆ := hperf.symm
        _ ≤ _ := Subgroup.commutator_mono hle hle
    rw [hE]
    exact h3 ⟨A, rfl⟩
  let embE : SL(n, F) →* ↥(elementaryGroup (quadPlus n F)) := (embSL F n).codRestrict _ hP
  have hker : ((QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup (quadPlus n F)))).comp
      embE).ker ≤ Subgroup.center SL(n, F) := by
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
      (QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup (quadPlus n F))))) = ⊥ := by
    have h := CFSG.ClassicalInvolution.Q3.oddCoreIn_range_eq_bot_of_isQuasisimple
      ((QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup (quadPlus n F)))).comp embE) hSL
      hSLZ hker
    rwa [MonoidHom.range_comp] at h
  refine oddCoreIn_fixed_eq_bot_of_blocks hZ2 _ (ι := Unit) (fun _ => embE.range) ?_ ?_
    (fun _ => hno) ?_
  · intro _ x hx
    obtain ⟨A, rfl⟩ := hx
    exact (Q3MFOD.mem_fixedSubgroup_conjES hE hμ hg _).mpr (embSL_mul_a₀ A)
  · intro _ b hb x hx
    obtain ⟨A, rfl⟩ := hx
    have hbc := (Q3MFOD.mem_fixedSubgroup_conjES hE hμ hg b).mp hb
    obtain ⟨B, hB⟩ := exists_blockGL_of_comm h2
      (elementaryGroup_le_orthogonalGroup (quadPlus n F) b.2) hbc
    refine ⟨conjSL B A, Subtype.ext ?_⟩
    show embSL F n (conjSL B A) = (b : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) *
      embSL F n A * (b : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F))⁻¹
    rw [← blockGL_conj_embSL, ← hB]
  · intro ν hν hcomm
    have hνc := (Q3MFOD.mem_fixedSubgroup_conjES hE hμ hg ν).mp hν
    obtain ⟨B, hB⟩ := exists_blockGL_of_comm h2
      (elementaryGroup_le_orthogonalGroup (quadPlus n F) ν.2) hνc
    have hBA : ∀ A : SL(n, F), B * Matrix.SpecialLinearGroup.toGL A =
        Matrix.SpecialLinearGroup.toGL A * B := by
      intro A
      have h1 := congrArg Subtype.val (hcomm () (embE A) ⟨A, rfl⟩)
      have h1' : (ν : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) * embSL F n A =
          embSL F n A * (ν : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) := h1
      rw [hB, embSL_apply, ← map_mul, ← map_mul] at h1'
      have h3 := Units.ext (Q3MFOD.glLin_inj h1')
      rw [← blockGL_mul, ← blockGL_mul] at h3
      exact blockGL_injective h3
    obtain ⟨c, hc⟩ := scalar_of_commute_toGL hBA
    have hsq := blockGL_scalar_sq hF (by omega) hc
    refine ⟨1, ?_⟩
    have e : ν ^ (2 ^ 1) = ν * ν := by rw [pow_one, _root_.sq]
    rw [e]
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, hB, hsq]
    rfl

end Main

end CFSG.ClassicalInvolution.Q3.TL4.Levi
