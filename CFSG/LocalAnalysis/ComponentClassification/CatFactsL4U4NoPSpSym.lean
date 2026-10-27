module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabL
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag Blocks

variable {F : Type} [Field F] [Fintype F]

@[expose] noncomputable def glEquiv (G : GL (Fin 4) F) : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 4 → F) (GeneralLinearGroup.toLin G)

omit [Fintype F] in
theorem glEquiv_apply (G : GL (Fin 4) F) (v : Fin 4 → F) :
    glEquiv G v = (G : Matrix (Fin 4) (Fin 4) F) *ᵥ v := rfl

omit [Fintype F] in
theorem glEquiv_injective : Function.Injective (glEquiv (F := F)) := by
  intro G G' h
  apply Units.ext
  ext i j
  have := congrArg (fun φ : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) => φ (Pi.single j 1) i) h
  simpa [glEquiv_apply, Matrix.mulVec_single] using this

omit [Fintype F] in
theorem transpose_mul_inv_mul_of_isometry {A G : GL (Fin 4) F}
    (hG : (G : Matrix (Fin 4) (Fin 4) F) * A * (G : Matrix (Fin 4) (Fin 4) F)ᵀ = A) :
    (G : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * G =
      ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  set Gm := (G : Matrix (Fin 4) (Fin 4) F)
  set Gi := ((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  set Am := (A : Matrix (Fin 4) (Fin 4) F)
  set R := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  have hGiG : Gi * Gm = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAR : Am * R = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRA : R * Am = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAGt : Am * Gmᵀ = Gi * Am := by
    calc Am * Gmᵀ = Gi * (Gm * Am * Gmᵀ) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
      _ = Gi * Am := by rw [hG]
  calc Gmᵀ * R * Gm = R * (Am * (Gmᵀ * R * Gm)) := by
        rw [← Matrix.mul_assoc R Am, hRA, Matrix.one_mul]
    _ = R * ((Am * Gmᵀ) * R * Gm) := by simp only [Matrix.mul_assoc]
    _ = R * (Gi * (Am * R) * Gm) := by rw [hAGt]; simp only [Matrix.mul_assoc]
    _ = R := by rw [hAR, Matrix.mul_one, hGiG, Matrix.mul_one]

omit [Fintype F] in
theorem glEquiv_mem_orthogonalGroup {A : GL (Fin 4) F} {G : GL (Fin 4) F}
    (hG : (G : Matrix (Fin 4) (Fin 4) F) * A * (G : Matrix (Fin 4) (Fin 4) F)ᵀ = A) :
    glEquiv G ∈ TauCeti.QuadraticMap.orthogonalGroup
      (Matrix.toQuadraticForm' ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  have h1 := transpose_mul_inv_mul_of_isometry hG
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', glEquiv_apply]
  have key : ∀ w : Fin 4 → F, ((G : Matrix (Fin 4) (Fin 4) F) *ᵥ v) ⬝ᵥ w =
      v ⬝ᵥ ((G : Matrix (Fin 4) (Fin 4) F)ᵀ *ᵥ w) := by
    intro w
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.mulVec_transpose]
  rw [key, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1]

omit [Fintype F] in
theorem inv_mul_isometry {A G G₁ : GL (Fin 4) F}
    (hG : (G : Matrix (Fin 4) (Fin 4) F) * A * (G : Matrix (Fin 4) (Fin 4) F)ᵀ = -A)
    (hG₁ : (G₁ : Matrix (Fin 4) (Fin 4) F) * A * (G₁ : Matrix (Fin 4) (Fin 4) F)ᵀ = -A) :
    ((G₁⁻¹ * G : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * A *
      ((G₁⁻¹ * G : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = A := by
  set Gi := ((G₁⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  have hGi : Gi * G₁ = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGi' : (G₁ : Matrix (Fin 4) (Fin 4) F) * Gi = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : Gi * A * Giᵀ = -A := by
    calc Gi * A * Giᵀ = -(Gi * ((G₁ : Matrix (Fin 4) (Fin 4) F) * A *
          (G₁ : Matrix (Fin 4) (Fin 4) F)ᵀ) * Giᵀ) := by
          rw [hG₁, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
      _ = -A := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGi, Matrix.one_mul, Matrix.mul_assoc,
            ← Matrix.transpose_mul, hGi, Matrix.transpose_one, Matrix.mul_one]
  rw [Units.val_mul, Matrix.transpose_mul]
  calc Gi * (G : Matrix (Fin 4) (Fin 4) F) * A * ((G : Matrix (Fin 4) (Fin 4) F)ᵀ * Giᵀ)
      = Gi * ((G : Matrix (Fin 4) (Fin 4) F) * A * (G : Matrix (Fin 4) (Fin 4) F)ᵀ) * Giᵀ := by
        simp only [Matrix.mul_assoc]
    _ = A := by rw [hG, Matrix.mul_neg, Matrix.neg_mul, h1, neg_neg]

theorem card_le_of_fixed_conjAut_dualAut (hF : Fintype.card F % 4 = 3) (A : GL (Fin 4) F)
    {M : Subgroup (projectiveSL 4 F)} (hM : ∀ x ∈ M, (conjAut 4 F A * dualAut 4 F) x = x) :
    Nat.card M ≤ 2 * Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (Matrix.toQuadraticForm' ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))) := by
  classical
  set O := TauCeti.QuadraticMap.orthogonalGroup
      (Matrix.toQuadraticForm' ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) with hO
  choose L hL using fun x : M => proj_surjective 4 F (x : projectiveSL 4 F)
  set G : M → GL (Fin 4) F := fun x => SpecialLinearGroup.toGL (L x) with hG
  have hGinj : Function.Injective G := by
    intro x y hxy
    apply Subtype.ext
    rw [← hL x, ← hL y]
    congr 1
    exact SpecialLinearGroup.toGL_injective hxy
  have hsign : ∀ x : M, (G x : Matrix (Fin 4) (Fin 4) F) * A * (G x : Matrix (Fin 4) (Fin 4) F)ᵀ =
      A ∨ (G x : Matrix (Fin 4) (Fin 4) F) * A * (G x : Matrix (Fin 4) (Fin 4) F)ᵀ = -A := by
    intro x
    have h1 := hM x x.2
    rw [← hL x, MulAut.mul_apply, dualAut_proj, conjAut_proj] at h1
    obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin 4) (Fin 4) F,
        T = (((L x)⁻¹ : SpecialLinearGroup (Fin 4) F).transpose : Matrix (Fin 4) (Fin 4) F) :=
      ⟨_, rfl⟩
    have hgi : T * ((L x : Matrix (Fin 4) (Fin 4) F))ᵀ = 1 := by
      rw [hT, Matrix.SpecialLinearGroup.coe_transpose, ← Matrix.transpose_mul]
      have : ((L x : Matrix (Fin 4) (Fin 4) F)) * (((L x)⁻¹ : SpecialLinearGroup (Fin 4) F) :
          Matrix (Fin 4) (Fin 4) F) = 1 :=
        congrArg (fun y : SpecialLinearGroup (Fin 4) F => (y : Matrix (Fin 4) (Fin 4) F))
          (mul_inv_cancel (L x))
      rw [this, Matrix.transpose_one]
    have hAi : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * A = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hGx : (G x : Matrix (Fin 4) (Fin 4) F) = (L x : Matrix (Fin 4) (Fin 4) F) := rfl
    rcases eq_of_proj_eq hF h1.symm with h | h <;> rw [coe_slConjugation, ← hT] at h
    · left
      rw [hGx]
      nth_rewrite 1 [← h]
      rw [Matrix.mul_assoc _ _ (A : Matrix (Fin 4) (Fin 4) F), hAi, Matrix.mul_one,
        Matrix.mul_assoc, hgi, Matrix.mul_one]
    · right
      have h' : (L x : Matrix (Fin 4) (Fin 4) F) = -((A : Matrix (Fin 4) (Fin 4) F) * T *
          ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by rw [h, neg_neg]
      rw [hGx]
      nth_rewrite 1 [h']
      rw [Matrix.neg_mul, Matrix.neg_mul,
        Matrix.mul_assoc _ _ (A : Matrix (Fin 4) (Fin 4) F), hAi, Matrix.mul_one,
        Matrix.mul_assoc, hgi, Matrix.mul_one]
  have : Finite ((Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) :=
    Finite.of_injective (fun e => (e : (Fin 4 → F) → (Fin 4 → F)))
      (fun a b hab => LinearEquiv.ext (congrFun hab))
  by_cases hex : ∃ G₁ : GL (Fin 4) F,
      (G₁ : Matrix (Fin 4) (Fin 4) F) * A * (G₁ : Matrix (Fin 4) (Fin 4) F)ᵀ = -A
  · obtain ⟨G₁, hG₁⟩ := hex
    let φ : M → O ⊕ O := fun x =>
      if h : (G x : Matrix (Fin 4) (Fin 4) F) * A * (G x : Matrix (Fin 4) (Fin 4) F)ᵀ = A
      then Sum.inl ⟨glEquiv (G x), glEquiv_mem_orthogonalGroup h⟩
      else Sum.inr ⟨glEquiv (G₁⁻¹ * G x),
        glEquiv_mem_orthogonalGroup (inv_mul_isometry ((hsign x).resolve_left h) hG₁)⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      apply hGinj
      simp only [φ] at hxy
      split_ifs at hxy with h1 h2 h2
      · exact glEquiv_injective (congrArg Subtype.val (Sum.inl_injective hxy))
      · exact mul_left_cancel (glEquiv_injective (congrArg Subtype.val (Sum.inr_injective hxy)))
    calc Nat.card M ≤ Nat.card (O ⊕ O) := Nat.card_le_card_of_injective φ hφ
      _ = 2 * Nat.card O := by rw [Nat.card_sum, two_mul]
  · simp only [not_exists] at hex
    let φ : M → O := fun x =>
      ⟨glEquiv (G x), glEquiv_mem_orthogonalGroup ((hsign x).resolve_right (hex _))⟩
    have hφ : Function.Injective φ := fun x y hxy =>
      hGinj (glEquiv_injective (congrArg Subtype.val hxy))
    calc Nat.card M ≤ Nat.card O := Nat.card_le_card_of_injective φ hφ
      _ ≤ 2 * Nat.card O := by omega

end StabL

end CFSG.ComponentClassification.CatFactsL4U4
