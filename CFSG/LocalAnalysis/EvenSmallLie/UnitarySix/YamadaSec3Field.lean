module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3LeviG

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open Matrix CFSG.Fischer CFSG.ClassicalInvolution.WeakCT Subgroup
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd (conjR mem_conjR msigma sY pstd sigmaSL swapSL2)
open CFSG.ClassicalModels (specialLinearFieldEquiv specialLinearFieldEquiv_map_center)
open scoped MatrixGroups

section Field

variable {F K : Type} [Field F] [Field K] (φ : F ≃+* K)

theorem slMap_coe {n : ℕ} (A : SL(n, F)) (a b : Fin n) :
    (specialLinearFieldEquiv φ (Fin n) A : SL(n, K)) a b = φ (A a b) := rfl

theorem slMap_transvection {n : ℕ} {i j : Fin n} (h : i ≠ j) (c : F) :
    specialLinearFieldEquiv φ (Fin n) (SpecialLinearGroup.transvection h c) =
      SpecialLinearGroup.transvection h (φ c) := by
  ext a b
  rw [slMap_coe, SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe,
    Matrix.add_apply, Matrix.add_apply, map_add, one_apply, one_apply, single_apply,
    single_apply]
  split_ifs <;> simp

theorem slMap_comp_blockSL {m k i : ℕ} (h : i + k ≤ m) :
    (specialLinearFieldEquiv φ (Fin m)).toMonoidHom.comp (blockSL F m k i h) =
      (blockSL K m k i h).comp (specialLinearFieldEquiv φ (Fin k)).toMonoidHom := by
  refine MonoidHom.eq_of_eqOn_dense CFSG.LinearGroups.special_linear_elementary_generation ?_
  rintro _ ⟨a, b, hab, c, rfl⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [blockSL_transvection, slMap_transvection, slMap_transvection, blockSL_transvection]

theorem slMap_blockSL {m k i : ℕ} (h : i + k ≤ m) (A : SL(k, F)) :
    specialLinearFieldEquiv φ (Fin m) (blockSL F m k i h A) =
      blockSL K m k i h (specialLinearFieldEquiv φ (Fin k) A) :=
  DFunLike.congr_fun (slMap_comp_blockSL φ h) A

theorem map_blockSL_range {m k i : ℕ} (h : i + k ≤ m) :
    (blockSL F m k i h).range.map (specialLinearFieldEquiv φ (Fin m)).toMonoidHom =
      (blockSL K m k i h).range := by
  rw [← MonoidHom.range_comp, slMap_comp_blockSL, MonoidHom.range_comp,
    (MonoidHom.range_eq_top (f := (specialLinearFieldEquiv φ (Fin k)).toMonoidHom)).2
      (specialLinearFieldEquiv φ (Fin k)).surjective, ← MonoidHom.range_eq_map]

theorem map_B12_field : (B12 F).map (specialLinearFieldEquiv φ (Fin 3)).toMonoidHom = B12 K :=
  map_blockSL_range φ _

theorem map_B23_field : (B23 F).map (specialLinearFieldEquiv φ (Fin 3)).toMonoidHom = B23 K :=
  map_blockSL_range φ _

theorem comap_center_field (n : ℕ) :
    (center SL(n, K)).comap (specialLinearFieldEquiv φ (Fin n)).toMonoidHom = center SL(n, F) := by
  rw [← specialLinearFieldEquiv_map_center φ (Fin n)]
  exact Subgroup.comap_map_eq_self_of_injective (specialLinearFieldEquiv φ (Fin n)).injective _

theorem map_pstd_field : (pstd F).map (specialLinearFieldEquiv φ (Fin 4)).toMonoidHom = pstd K := by
  rw [pstd, pstd, MonoidHom.map_closure]
  congr 1
  ext A
  constructor
  · rintro ⟨_, ⟨i, j, h, c, hji, rfl⟩, rfl⟩
    exact ⟨i, j, h, φ c, hji, slMap_transvection φ h c⟩
  · rintro ⟨i, j, h, c, hji, rfl⟩
    refine ⟨_, ⟨i, j, h, φ.symm c, hji, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, slMap_transvection, φ.apply_symm_apply]

variable [CharP F 2] [CharP K 2]

theorem slMap_swapSL2 : specialLinearFieldEquiv φ (Fin 2) (swapSL2 F) = swapSL2 K := by
  ext a b
  rw [slMap_coe]
  fin_cases a <;> fin_cases b <;> simp [swapSL2]

theorem slMap_sY (i : Fin 3) : specialLinearFieldEquiv φ (Fin 4) (sY F i) = sY K i := by
  show specialLinearFieldEquiv φ (Fin (3 + 1)) (blockSL F (3 + 1) 2 i (by omega) (swapSL2 F)) =
    blockSL K (3 + 1) 2 i (by omega) (swapSL2 K)
  rw [slMap_blockSL, slMap_swapSL2]

variable [Finite F] [Finite K]

theorem slMap_sigmaSL (A : SL(4, F)) :
    specialLinearFieldEquiv φ (Fin 4) (sigmaSL F A) =
      sigmaSL K (specialLinearFieldEquiv φ (Fin 4) A) := by
  have h : (specialLinearFieldEquiv φ (Fin 4)).toMonoidHom.comp (sigmaSL F).toMonoidHom =
      (sigmaSL K).toMonoidHom.comp (specialLinearFieldEquiv φ (Fin 4)).toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense CFSG.LinearGroups.special_linear_elementary_generation ?_
    rintro _ ⟨a, b, hab, c, rfl⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [YamadaEnd.sigmaSL_transvection, slMap_transvection, slMap_transvection,
      YamadaEnd.sigmaSL_transvection, map_pow]
  exact DFunLike.congr_fun h A

theorem slMap_mem_msigma {A : SL(4, F)} :
    specialLinearFieldEquiv φ (Fin 4) A ∈ msigma K ↔ A ∈ msigma F := by
  show sigmaSL K _ = _ ↔ sigmaSL F A = A
  rw [← slMap_sigmaSL]
  exact (specialLinearFieldEquiv φ (Fin 4)).injective.eq_iff

@[expose] noncomputable def msigmaEquiv : msigma F ≃* msigma K where
  toFun A := ⟨specialLinearFieldEquiv φ (Fin 4) A, (slMap_mem_msigma φ).2 A.2⟩
  invFun B := ⟨(specialLinearFieldEquiv φ (Fin 4)).symm B, (slMap_mem_msigma φ).1 (by
    rw [MulEquiv.apply_symm_apply]
    exact B.2)⟩
  left_inv A := Subtype.ext ((specialLinearFieldEquiv φ (Fin 4)).symm_apply_apply (A : SL(4, F)))
  right_inv B := Subtype.ext ((specialLinearFieldEquiv φ (Fin 4)).apply_symm_apply (B : SL(4, K)))
  map_mul' A B := Subtype.ext
    (map_mul (specialLinearFieldEquiv φ (Fin 4)) (A : SL(4, F)) (B : SL(4, F)))

theorem coe_msigmaEquiv (A : msigma F) :
    (msigmaEquiv φ A : SL(4, K)) = specialLinearFieldEquiv φ (Fin 4) A := rfl

end Field

@[expose] noncomputable def fieldEquivF4 (F : Type) [Field F] [Finite F] (hF : Nat.card F = 4) :
    F ≃+* F4 :=
  letI := Fintype.ofFinite F
  FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hF, F4.card])

section Transfer

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46}
  {F : Type} [Field F]

theorem K₂_pair_of_field (φ : F ≃+* F4) : ∃ θ : SL(3, F) →* G, θ.range = sK₂ e ∧
    θ.ker = center SL(3, F) ∧ (B12 F).map θ = sX₁ e ⊔ conjR (sX₁ e) (sw e 0) ∧
    (B23 F).map θ = sX₂ e ⊔ conjR (sX₂ e) (sw e 1) := by
  refine ⟨(thetaG e).comp (specialLinearFieldEquiv φ (Fin 3)).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp,
      (MonoidHom.range_eq_top (f := (specialLinearFieldEquiv φ (Fin 3)).toMonoidHom)).2
        (specialLinearFieldEquiv φ (Fin 3)).surjective, ← MonoidHom.range_eq_map, range_thetaG]
  · rw [← MonoidHom.comap_ker, ker_thetaG, comap_center_field]
  · rw [← Subgroup.map_map, map_B12_field, map_B12_thetaG]
  · rw [← Subgroup.map_map, map_B23_field, map_B23_thetaG]

variable [CharP F 2] [Finite F]

theorem K₁_model_of_field (φ : F ≃+* F4) : ∃ χ : msigma F ≃* sK₁ e,
    (∀ A : msigma F, (A : SL(4, F)) = sY F 0 * sY F 2 → (χ A : G) = sw e 1) ∧
    (∀ A : msigma F, (A : SL(4, F)) = sY F 1 → (χ A : G) = sw e 2) ∧
    ∀ A : msigma F, (A : SL(4, F)) ∈ pstd F →
      (χ A : G) ∈ sS e ⊓ conjR (sS e) (sw e 0 * sw e 1 * sw e 2 * sw e 1 * sw e 0) := by
  obtain ⟨χ, h1, h2, h3⟩ := K₁_model_F4 (e := e)
  refine ⟨(msigmaEquiv φ).trans χ, fun A hA => h1 _ ?_, fun A hA => h2 _ ?_,
    fun A hA => h3 _ ?_⟩
  · show specialLinearFieldEquiv φ (Fin 4) (A : SL(4, F)) = _
    rw [hA, map_mul, slMap_sY, slMap_sY]
  · show specialLinearFieldEquiv φ (Fin 4) (A : SL(4, F)) = _
    rw [hA, slMap_sY]
  · show specialLinearFieldEquiv φ (Fin 4) (A : SL(4, F)) ∈ _
    rw [← map_pstd_field φ]
    exact ⟨A, hA, rfl⟩

end Transfer

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
