module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3D4Strings

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3.D4

open CFSG.Blueprint.Chevalley Matrix

variable (K : Type) [Field K]

@[expose] def castM : M8 →+* Matrix (Fin 8) (Fin 8) K := RingHom.mapMatrix (Int.castRingHom K)

@[expose] def phiLabel : Label Tag.D4 → Matrix (Fin 8) (Fin 8) K
  | Sum.inl j => castM K (HZ j)
  | Sum.inr α => castM K (phiRootZ α.1)

@[expose] noncomputable def phi : RootModule Tag.D4 K →ₗ[K] Matrix (Fin 8) (Fin 8) K :=
  Finsupp.linearCombination K (phiLabel K)

@[expose] def rho (s : Matrix (Fin 8) (Fin 8) K) : Module.End K (Matrix (Fin 8) (Fin 8) K) :=
  LinearMap.mulLeft K s ∘ₗ LinearMap.mulRight K sᵀ

theorem rho_apply (s M : Matrix (Fin 8) (Fin 8) K) : rho K s M = s * M * sᵀ := by
  simp only [rho, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    Matrix.mul_assoc]

theorem rho_mul (s t : Matrix (Fin 8) (Fin 8) K) : rho K (s * t) = rho K s * rho K t := by
  apply LinearMap.ext
  intro M
  simp only [Module.End.mul_apply, rho_apply, Matrix.transpose_mul, Matrix.mul_assoc]

theorem rho_one : rho K 1 = 1 := by
  apply LinearMap.ext
  intro M
  simp only [Module.End.one_apply, rho_apply, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one]

theorem rho_one_add_smul (X M : Matrix (Fin 8) (Fin 8) K) (c : K) :
    rho K (1 + c • X) M = M + c • (X * M + M * Xᵀ) + c ^ 2 • (X * M * Xᵀ) := by
  rw [rho_apply, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul]
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_add,
    smul_smul, sq]
  module

theorem castM_transpose (A : M8) : castM K Aᵀ = (castM K A)ᵀ := by
  simp only [castM, RingHom.mapMatrix_apply, Matrix.transpose_map]

theorem castM_lin (X M : M8) :
    castM K (X * M + M * Xᵀ) = castM K X * castM K M + castM K M * (castM K X)ᵀ := by
  rw [map_add, map_mul, map_mul, castM_transpose]

theorem castM_quad (X M : M8) :
    castM K (X * M * Xᵀ) = castM K X * castM K M * (castM K X)ᵀ := by
  rw [map_mul, map_mul, castM_transpose]

theorem castM_orth1 (X B : M8) :
    castM K (Xᵀ * B + B * X) = (castM K X)ᵀ * castM K B + castM K B * castM K X := by
  rw [map_add, map_mul, map_mul, castM_transpose]

theorem castM_orth2 (X B : M8) :
    castM K (Xᵀ * B * X) = (castM K X)ᵀ * castM K B * castM K X := by
  rw [map_mul, map_mul, castM_transpose]

theorem castM_zsmul (n : ℤ) (A : M8) : castM K (n • A) = (n : K) • castM K A := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

theorem rho_castM (X M N P : M8) (c : K) (h1 : X * M + M * Xᵀ = N) (h2 : X * M * Xᵀ = P) :
    rho K (1 + c • castM K X) (castM K M) = castM K M + c • castM K N + c ^ 2 • castM K P := by
  rw [rho_one_add_smul, ← castM_lin, ← castM_quad, h1, h2]

theorem orth_expand (X B : Matrix (Fin 8) (Fin 8) K) (c : K) :
    (1 + c • X)ᵀ * B * (1 + c • X) = B + c • (Xᵀ * B + B * X) + c ^ 2 • (Xᵀ * B * X) := by
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul]
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_add,
    smul_smul, sq]
  module

theorem orth_castM (X B : M8) (c : K) (h1 : Xᵀ * B + B * X = 0) (h2 : Xᵀ * B * X = 0) :
    (1 + c • castM K X)ᵀ * castM K B * (1 + c • castM K X) = castM K B := by
  rw [orth_expand, ← castM_orth1, ← castM_orth2, h1, h2]
  simp

theorem add_mul_sub_eq_one_of_sq (X : Matrix (Fin 8) (Fin 8) K) (hX : X * X = 0) (c : K) :
    (1 + c • X) * (1 - c • X) = 1 ∧ (1 - c • X) * (1 + c • X) = 1 := by
  have hcX : (c • X) * (c • X) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hX, smul_zero, smul_zero]
  constructor
  · simp only [mul_sub, add_mul, one_mul, mul_one, hcX, add_zero]
    abel
  · simp only [mul_add, sub_mul, one_mul, mul_one, hcX, sub_zero]
    abel

theorem castM_sq_zero_X (i : Fin 4) : castM K (XZ i) * castM K (XZ i) = 0 := by
  rw [← map_mul, XZ_sq i, map_zero]

theorem castM_sq_zero_Y (i : Fin 4) : castM K (YZ i) * castM K (YZ i) = 0 := by
  rw [← map_mul, YZ_sq i, map_zero]

theorem cartan_D4_apply (j i : Fin 4) : Tag.cartan Tag.D4 j i = cartanD4 j i := by
  fin_cases j <;> fin_cases i <;> rfl

theorem phi_single (a : Label Tag.D4) : phi K (Finsupp.single a 1) = phiLabel K a := by
  rw [phi, Finsupp.linearCombination_single, one_smul]

theorem phi_hVec (j : Fin 4) : phi K (hVec Tag.D4 K j) = castM K (HZ j) :=
  phi_single K (Sum.inl j)

theorem phi_rootVec (β : Fin 4 → ℤ) : phi K (rootVec Tag.D4 K β) = castM K (phiRootZ β) := by
  by_cases h : IsRoot Tag.D4 β
  · rw [rootVec_eq_basisVec_of_isRoot (R := K) h]
    exact phi_single K (Sum.inr ⟨β, h⟩)
  · have h0 : rootVec Tag.D4 K β = 0 := by
      simp only [rootVec, dif_neg h]
    rw [h0, map_zero, phiRootZ_not_root (fun hb => h (isRoot_D4_iff.2 hb)), map_zero]

theorem phi_compat_xOp_hVec (i : Fin 4) (c : K) (j : Fin 4) :
    phi K (xOp Tag.D4 K i c (hVec Tag.D4 K j)) =
      rho K (1 + c • castM K (XZ i)) (phi K (hVec Tag.D4 K j)) := by
  have hx : xOp Tag.D4 K i c (hVec Tag.D4 K j) =
      hVec Tag.D4 K j + (((cartanD4 j i).natAbs : K) * c) • rootVec Tag.D4 K (e i) := by
    rw [xOp_apply_hVec (τ := Tag.D4) (R := K) i j c, cartan_D4_apply j i] <;> rfl
  rw [hx, map_add, map_smul, phi_hVec, phi_rootVec,
    rho_castM K (XZ i) (HZ j) (((cartanD4 j i).natAbs : ℤ) • phiRootZ (e i)) 0 c
      (tableX.1 i j).1 (tableX.1 i j).2, castM_zsmul, Int.cast_natCast, map_zero]
  simp only [smul_zero, add_zero]
  module

theorem phi_compat_xOp_rootVec (i : Fin 4) (c : K) {α : Fin 4 → ℤ} (hα : IsRoot Tag.D4 α) :
    phi K (xOp Tag.D4 K i c (rootVec Tag.D4 K α)) =
      rho K (1 + c • castM K (XZ i)) (phi K (rootVec Tag.D4 K α)) := by
  rw [phi_rootVec]
  by_cases h1 : α = e i
  · subst h1
    have hx : xOp Tag.D4 K i c (rootVec Tag.D4 K (e i)) = rootVec Tag.D4 K (e i) :=
      xOp_apply_rootVec_single (τ := Tag.D4) (R := K) i c
    rw [hx, phi_rootVec, rho_castM K (XZ i) (phiRootZ (e i)) 0 0 c (tableX.2.1 i).1
      (tableX.2.1 i).2]
    simp
  by_cases h2 : α = -e i
  · subst h2
    have hx : xOp Tag.D4 K i c (rootVec Tag.D4 K (-e i)) =
        rootVec Tag.D4 K (-e i) + c • hVec Tag.D4 K i + c ^ 2 • rootVec Tag.D4 K (e i) :=
      xOp_apply_rootVec_neg_single (τ := Tag.D4) (R := K) i c
    rw [hx, map_add, map_add, map_smul, map_smul, phi_rootVec, phi_rootVec, phi_hVec,
      rho_castM K (XZ i) (phiRootZ (-e i)) (HZ i) (phiRootZ (e i)) c (tableX.2.2.1 i).1
        (tableX.2.2.1 i).2]
  · have hα' : α ∈ d4Roots := isRoot_D4_iff.1 hα
    have hx : xOp Tag.D4 K i c (rootVec Tag.D4 K α) =
        rootVec Tag.D4 K α + c • rootVec Tag.D4 K (α + e i) :=
      xOp_D4_rootVec_of_ne i c hα' h1 h2
    rw [hx, map_add, map_smul, phi_rootVec, phi_rootVec,
      rho_castM K (XZ i) (phiRootZ α) (phiRootZ (α + e i)) 0 c
        (tableX.2.2.2 i α hα' h1 h2).1 (tableX.2.2.2 i α hα' h1 h2).2]
    simp

theorem phi_compat_xOp_label (i : Fin 4) (c : K) (a : Label Tag.D4) :
    phi K (xOp Tag.D4 K i c (Finsupp.single a 1)) =
      rho K (1 + c • castM K (XZ i)) (phi K (Finsupp.single a 1)) := by
  rcases a with j | ⟨α, hα⟩
  · exact phi_compat_xOp_hVec K i c j
  · have hv : (Finsupp.single (Sum.inr ⟨α, hα⟩) (1 : K)) = rootVec Tag.D4 K α :=
      (rootVec_eq_basisVec_of_isRoot (R := K) hα).symm
    rw [hv]
    exact phi_compat_xOp_rootVec K i c hα

theorem phi_compat_xOp (i : Fin 4) (c : K) :
    phi K ∘ₗ xOp Tag.D4 K i c = rho K (1 + c • castM K (XZ i)) ∘ₗ phi K := by
  apply Finsupp.lhom_ext'
  intro a
  apply LinearMap.ext_ring
  exact phi_compat_xOp_label K i c a

theorem phi_compat_yOp_hVec (i : Fin 4) (c : K) (j : Fin 4) :
    phi K (yOp Tag.D4 K i c (hVec Tag.D4 K j)) =
      rho K (1 + c • castM K (YZ i)) (phi K (hVec Tag.D4 K j)) := by
  have hy : yOp Tag.D4 K i c (hVec Tag.D4 K j) =
      hVec Tag.D4 K j + (((cartanD4 j i).natAbs : K) * c) • rootVec Tag.D4 K (-e i) := by
    rw [yOp_apply_hVec (τ := Tag.D4) (R := K) i j c, cartan_D4_apply j i] <;> rfl
  rw [hy, map_add, map_smul, phi_hVec, phi_rootVec,
    rho_castM K (YZ i) (HZ j) (((cartanD4 j i).natAbs : ℤ) • phiRootZ (-e i)) 0 c
      (tableY.1 i j).1 (tableY.1 i j).2, castM_zsmul, Int.cast_natCast, map_zero]
  simp only [smul_zero, add_zero]
  module

theorem phi_compat_yOp_rootVec (i : Fin 4) (c : K) {α : Fin 4 → ℤ} (hα : IsRoot Tag.D4 α) :
    phi K (yOp Tag.D4 K i c (rootVec Tag.D4 K α)) =
      rho K (1 + c • castM K (YZ i)) (phi K (rootVec Tag.D4 K α)) := by
  rw [phi_rootVec]
  by_cases h1 : α = -e i
  · subst h1
    have hx : yOp Tag.D4 K i c (rootVec Tag.D4 K (-e i)) = rootVec Tag.D4 K (-e i) :=
      yOp_apply_rootVec_neg_single (τ := Tag.D4) (R := K) i c
    rw [hx, phi_rootVec, rho_castM K (YZ i) (phiRootZ (-e i)) 0 0 c (tableY.2.1 i).1
      (tableY.2.1 i).2]
    simp
  by_cases h2 : α = e i
  · subst h2
    have hx : yOp Tag.D4 K i c (rootVec Tag.D4 K (e i)) =
        rootVec Tag.D4 K (e i) + c • hVec Tag.D4 K i + c ^ 2 • rootVec Tag.D4 K (-e i) :=
      yOp_apply_rootVec_single (τ := Tag.D4) (R := K) i c
    rw [hx, map_add, map_add, map_smul, map_smul, phi_rootVec, phi_rootVec, phi_hVec,
      rho_castM K (YZ i) (phiRootZ (e i)) (HZ i) (phiRootZ (-e i)) c (tableY.2.2.1 i).1
        (tableY.2.2.1 i).2]
  · have hα' : α ∈ d4Roots := isRoot_D4_iff.1 hα
    have hy : yOp Tag.D4 K i c (rootVec Tag.D4 K α) =
        rootVec Tag.D4 K α + c • rootVec Tag.D4 K (α - e i) :=
      yOp_D4_rootVec_of_ne i c hα' h2 h1
    rw [hy, map_add, map_smul, phi_rootVec, phi_rootVec,
      rho_castM K (YZ i) (phiRootZ α) (phiRootZ (α - e i)) 0 c
        (tableY.2.2.2 i α hα' h2 h1).1 (tableY.2.2.2 i α hα' h2 h1).2]
    simp

theorem phi_compat_yOp_label (i : Fin 4) (c : K) (a : Label Tag.D4) :
    phi K (yOp Tag.D4 K i c (Finsupp.single a 1)) =
      rho K (1 + c • castM K (YZ i)) (phi K (Finsupp.single a 1)) := by
  rcases a with j | ⟨α, hα⟩
  · exact phi_compat_yOp_hVec K i c j
  · have hv : (Finsupp.single (Sum.inr ⟨α, hα⟩) (1 : K)) = rootVec Tag.D4 K α :=
      (rootVec_eq_basisVec_of_isRoot (R := K) hα).symm
    rw [hv]
    exact phi_compat_yOp_rootVec K i c hα

theorem phi_compat_yOp (i : Fin 4) (c : K) :
    phi K ∘ₗ yOp Tag.D4 K i c = rho K (1 + c • castM K (YZ i)) ∘ₗ phi K := by
  apply Finsupp.lhom_ext'
  intro a
  apply LinearMap.ext_ring
  exact phi_compat_yOp_label K i c a

@[expose] def gX (i : Fin 4) (c : K) : GL (Fin 8) K where
  val := 1 + c • castM K (XZ i)
  inv := 1 - c • castM K (XZ i)
  val_inv := (add_mul_sub_eq_one_of_sq K _ (castM_sq_zero_X K i) c).1
  inv_val := (add_mul_sub_eq_one_of_sq K _ (castM_sq_zero_X K i) c).2

@[expose] def gY (i : Fin 4) (c : K) : GL (Fin 8) K where
  val := 1 + c • castM K (YZ i)
  inv := 1 - c • castM K (YZ i)
  val_inv := (add_mul_sub_eq_one_of_sq K _ (castM_sq_zero_Y K i) c).1
  inv_val := (add_mul_sub_eq_one_of_sq K _ (castM_sq_zero_Y K i) c).2

theorem gX_orth (i : Fin 4) (c : K) :
    ((gX K i c : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ *
      (gX K i c : GL (Fin 8) K) = castM K BZ :=
  orth_castM K (XZ i) BZ c (tableB i).1.1 (tableB i).1.2

theorem gY_orth (i : Fin 4) (c : K) :
    ((gY K i c : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ *
      (gY K i c : GL (Fin 8) K) = castM K BZ :=
  orth_castM K (YZ i) BZ c (tableB i).2.1 (tableB i).2.2

end CFSG.ComponentClassification.CatFC.KGHS3.D4
