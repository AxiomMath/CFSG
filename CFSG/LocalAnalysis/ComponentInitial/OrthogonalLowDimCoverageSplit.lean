module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitNormal

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

variable {K : Type*} [Field K]

@[expose] def determinantLeftFactor (K : Type*) [Field K] : Subgroup (DeterminantIsometries K) :=
  ((specialRho (K := K)).comp (MonoidHom.inl _ _)).range

@[expose] def determinantRightFactor (K : Type*) [Field K] :
    Subgroup (DeterminantIsometries K) :=
  ((specialRho (K := K)).comp (MonoidHom.inr _ _)).range

theorem rho_mem_specialImage_of_commonDeterminant_eq_sq (z : equalDeterminants K) {c : Kˣ}
    (hz : commonDeterminant z = c ^ 2) : rho z ∈ specialImage K := by
  have h := rho_mem_specialImage_of_commonDeterminant (z * scalarPair c⁻¹) (by
    rw [map_mul, hz]
    change c ^ 2 * GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) c⁻¹) = 1
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, mul_inv_cancel])
  rwa [map_mul, rho_scalarPair, mul_one] at h

theorem determinant_sq_mem_specialImage (g : DeterminantIsometries K) :
    g ^ 2 ∈ specialImage K := by
  obtain ⟨z, rfl | rfl⟩ := determinant_isometry_exhaustion g
  · rw [← map_pow]
    exact rho_mem_specialImage_of_commonDeterminant_eq_sq _ (map_pow _ _ _)
  · have heq : (rho z * tau) ^ 2 = rho (z * transposePair z) := by
      rw [pow_two, map_mul, ← tau_rho_tau]
      group
    rw [heq]
    apply rho_mem_specialImage_of_commonDeterminant
    rw [map_mul, commonDeterminant_transposePair, mul_inv_cancel]

theorem determinantLeftFactor_le : determinantLeftFactor K ≤ specialImage K := by
  rintro _ ⟨A, rfl⟩
  exact ⟨_, rfl⟩

theorem determinantRightFactor_le : determinantRightFactor K ≤ specialImage K := by
  rintro _ ⟨A, rfl⟩
  exact ⟨_, rfl⟩

theorem determinantFactors_sup :
    determinantLeftFactor K ⊔ determinantRightFactor K = specialImage K := by
  refine le_antisymm (sup_le determinantLeftFactor_le determinantRightFactor_le) ?_
  rintro _ ⟨⟨A, B⟩, rfl⟩
  have h : ((A, B) : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) =
      MonoidHom.inl _ _ A * MonoidHom.inr _ _ B := by
    ext <;> simp
  rw [h, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨A, rfl⟩) (Subgroup.mem_sup_right ⟨B, rfl⟩)

theorem determinantFactors_commute {x y : DeterminantIsometries K}
    (hx : x ∈ determinantLeftFactor K) (hy : y ∈ determinantRightFactor K) : x * y = y * x := by
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := hy
  simp only [MonoidHom.comp_apply, ← map_mul]
  congr 1
  ext <;> simp

theorem determinantLeftFactor_normal :
    ((determinantLeftFactor K).subgroupOf (specialImage K)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨C, hC⟩ := hn
  obtain ⟨⟨A, B⟩, hAB⟩ := g.property
  refine ⟨A * C * A⁻¹, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hC, ← hAB, MonoidHom.comp_apply, ← map_mul,
    ← map_inv]
  congr 1
  ext <;> simp

theorem determinantRightFactor_normal :
    ((determinantRightFactor K).subgroupOf (specialImage K)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨C, hC⟩ := hn
  obtain ⟨⟨A, B⟩, hAB⟩ := g.property
  refine ⟨B * C * B⁻¹, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hC, ← hAB, MonoidHom.comp_apply, ← map_mul,
    ← map_inv]
  congr 1
  ext <;> simp

@[expose] def unipotentSL (K : Type*) [Field K] : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem toGL_unipotentSL_ne_scalar (c : Kˣ) :
    SpecialLinearGroup.toGL (unipotentSL K) ≠ GeneralLinearGroup.scalar (Fin 2) c := by
  intro h
  have h01 := congrArg (fun B : GL (Fin 2) K => B.val 0 1) h
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h01
  change 1 = Matrix.diagonal (fun _ => (c : K)) 0 1 at h01
  rw [Matrix.diagonal_apply_ne _ (by decide)] at h01
  exact one_ne_zero h01

variable [Finite K]

theorem determinantLeftFactor_quasisimple (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) :
    CFSG.IsQuasisimple (determinantLeftFactor K) := by
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  rcases quasisimple_homomorphic_images hSL ((specialRho (K := K)).comp (MonoidHom.inl _ _))
    with h | h
  · exfalso
    have hmem : (specialRho (K := K)).comp (MonoidHom.inl _ _) (unipotentSL K) ∈
        ((specialRho (K := K)).comp (MonoidHom.inl _ _)).range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, MonoidHom.comp_apply, specialRho_eq_one_iff] at hmem
    obtain ⟨c, -, hc, -⟩ := hmem
    exact toGL_unipotentSL_ne_scalar c hc
  · exact h

theorem determinantRightFactor_quasisimple (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) :
    CFSG.IsQuasisimple (determinantRightFactor K) := by
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  rcases quasisimple_homomorphic_images hSL ((specialRho (K := K)).comp (MonoidHom.inr _ _))
    with h | h
  · exfalso
    have hmem : (specialRho (K := K)).comp (MonoidHom.inr _ _) (unipotentSL K) ∈
        ((specialRho (K := K)).comp (MonoidHom.inr _ _)).range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, MonoidHom.comp_apply, specialRho_eq_one_iff] at hmem
    obtain ⟨c, -, -, hc⟩ := hmem
    exact toGL_unipotentSL_ne_scalar c hc
  · exact h

theorem determinantSpecialImage_isPerfect (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) :
    Group.IsPerfect (specialImage K) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  rw [← determinantFactors_sup]
  refine sup_le ?_ ?_
  · calc determinantLeftFactor K = ⁅determinantLeftFactor K, determinantLeftFactor K⁆ :=
          (Subgroup.isPerfect_iff.mp (determinantLeftFactor_quasisimple hK2 hK3).1).symm
      _ ≤ _ := Subgroup.commutator_mono (le_sup_left.trans determinantFactors_sup.le)
          (le_sup_left.trans determinantFactors_sup.le)
      _ = _ := by rw [determinantFactors_sup]
  · calc determinantRightFactor K = ⁅determinantRightFactor K, determinantRightFactor K⁆ :=
          (Subgroup.isPerfect_iff.mp (determinantRightFactor_quasisimple hK2 hK3).1).symm
      _ ≤ _ := Subgroup.commutator_mono (le_sup_right.trans determinantFactors_sup.le)
          (le_sup_right.trans determinantFactors_sup.le)
      _ = _ := by rw [determinantFactors_sup]

theorem determinant_commutator_eq (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) :
    commutator (DeterminantIsometries K) = specialImage K :=
  commutator_eq_of_isPerfect_of_forall_sq_mem (determinantSpecialImage_isPerfect hK2 hK3)
    determinant_sq_mem_specialImage

theorem determinant_prime_dvd_card (hK : Nat.card K ≤ 3) {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card (DeterminantIsometries K)) : p = 2 ∨ p = 3 := by
  rw [← (leftRightImage K).card_mul_index] at hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · have hD : Nat.card (leftRightImage K) ∣
        Nat.card (GL (Fin 2) K) * Nat.card (GL (Fin 2) K) := by
      rw [← Nat.card_prod]
      exact (Subgroup.card_range_dvd (rho (K := K))).trans
        (Subgroup.card_subgroup_dvd_card (equalDeterminants K))
    rcases (Nat.Prime.dvd_mul hp).mp (h.trans hD) with h' | h' <;>
      exact prime_dvd_forty_eight hp (h'.trans (card_GL_two_dvd_forty_eight hK))
  · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) (h.trans leftRightImage_index_dvd_two)
    have := hp.two_le
    omega

end CFSG.LocalAnalysis.ComponentInitial
