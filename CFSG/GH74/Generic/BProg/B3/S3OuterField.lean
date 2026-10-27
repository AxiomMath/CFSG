module

public import CFSG.GH74.Generic.BProg.B3.S3OuterCore
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LieType.Universal.SpecialLinear

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3OuterField

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  Subgroup S3OuterCore
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def d0 (F : Type) [Field F] : SL(3, F) := ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], by
  simp [Matrix.det_fin_three]⟩

@[simp] theorem d0_coe :
    ((d0 F : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] :=
  rfl

theorem d0_mul_self : d0 F * d0 F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, d0_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem d0_not_mem_scalars (h2 : (2 : F) ≠ 0) : d0 F ∉ scalars 3 F := by
  rintro ⟨l, -, hl⟩
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) hl
  have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 2 2) hl
  simp [Matrix.scalar_apply] at h00 h22
  exact h2 (by linear_combination h22 - h00)

@[expose] def b1 (F : Type) [Field F] : SL(3, F) := ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by
  simp [Matrix.det_fin_three]⟩

@[simp] theorem b1_coe :
    ((b1 F : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, -1, 0; 0, 0, -1] :=
  rfl

theorem b1_mul_self : b1 F * b1 F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, b1_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem b1_comm_d0 : b1 F * d0 F = d0 F * b1 F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, b1_coe, d0_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem b1_not_mem_scalars (h2 : (2 : F) ≠ 0) : b1 F ∉ scalars 3 F := by
  rintro ⟨l, -, hl⟩
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) hl
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 1) hl
  simp [Matrix.scalar_apply] at h00 h11
  exact h2 (by linear_combination h00 - h11)

theorem b1_mul_d0_not_mem_scalars (h2 : (2 : F) ≠ 0) : b1 F * d0 F ∉ scalars 3 F := by
  rintro ⟨l, -, hl⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, b1_coe, d0_coe] at hl
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) hl
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 1) hl
  simp [Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_three] at h00 h11
  exact h2 (by linear_combination h11 - h00)

theorem two_le_pRank_of_b1_d0 [Finite F] (h2 : (2 : F) ≠ 0) {N : Subgroup (projectiveSL 3 F)}
    (hb : proj 3 F (b1 F) ∈ N) (hd : proj 3 F (d0 F) ∈ N) : 2 ≤ pRank 2 ↥N := by
  refine two_le_pRank_of_invols (a := ⟨proj 3 F (b1 F), hb⟩) (b := ⟨proj 3 F (d0 F), hd⟩)
    ?_ ?_ ?_ ?_ ?_ ?_
  · apply Subtype.ext
    change proj 3 F (b1 F) * proj 3 F (d0 F) = proj 3 F (d0 F) * proj 3 F (b1 F)
    rw [← map_mul, ← map_mul, b1_comm_d0]
  · apply Subtype.ext
    change proj 3 F (b1 F) * proj 3 F (b1 F) = 1
    rw [← map_mul, b1_mul_self, map_one]
  · apply Subtype.ext
    change proj 3 F (d0 F) * proj 3 F (d0 F) = 1
    rw [← map_mul, d0_mul_self, map_one]
  · intro h
    exact b1_not_mem_scalars h2 (proj_eq_one_iff.1 (congrArg Subtype.val h))
  · intro h
    exact d0_not_mem_scalars h2 (proj_eq_one_iff.1 (congrArg Subtype.val h))
  · intro h
    have h1 : proj 3 F (b1 F) = proj 3 F (d0 F) := congrArg Subtype.val h
    have h3 : proj 3 F (b1 F * d0 F) = 1 := by
      rw [map_mul, h1, ← map_mul, d0_mul_self, map_one]
    exact b1_mul_d0_not_mem_scalars h2 (proj_eq_one_iff.1 h3)

theorem map_eq_self_iff (σ : F ≃+* F) (M : SL(3, F)) :
    SpecialLinearGroup.map σ.toRingHom M = M ↔ ∀ i j, σ (M i j) = M i j := by
  constructor
  · intro h i j
    have := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) i j) h
    simpa [SpecialLinearGroup.map_apply_coe] using this
  · intro h
    apply Subtype.ext
    ext i j
    simpa [SpecialLinearGroup.map_apply_coe] using h i j

@[expose] def kz (ζ : F) (h : ζ ≠ 0) : SL(3, F) := ⟨!![ζ, 0, 0; 0, ζ, 0; 0, 0, ζ⁻¹ * ζ⁻¹], by
  simp [Matrix.det_fin_three]
  field_simp⟩

@[simp] theorem kz_coe (ζ : F) (h : ζ ≠ 0) :
    ((kz ζ h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![ζ, 0, 0; 0, ζ, 0; 0, 0, ζ⁻¹ * ζ⁻¹] := rfl

theorem map_kz (σ : F ≃+* F) {ζ : F} (h : ζ ≠ 0) (hσ : σ ζ = -ζ) :
    SpecialLinearGroup.map σ.toRingHom (kz ζ h) = d0 F * kz ζ h := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, d0_coe, kz_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.mul_apply,
      Fin.sum_univ_three, hσ]

theorem outerCore_field [Finite F] (h2 : (2 : F) ≠ 0) {σ : F ≃+* F} (hσ : ∃ a, σ a ≠ a)
    (hσσ : ∀ a, σ (σ a) = a) : OuterCore (fieldAut 3 F σ) := by
  classical
  set K₀ : Subfield F := (σ : F →+* F).eqLocusField (RingHom.id F) with hK₀
  have hmem : ∀ a : F, a ∈ K₀ ↔ σ a = a := fun a => Iff.rfl
  set ι : SL(3, K₀) →* SL(3, F) := SpecialLinearGroup.map K₀.subtype with hι
  have hinj : Function.Injective ι := by
    intro g g' h
    apply Subtype.ext
    ext i j
    have := congrArg (fun M : SL(3, F) => (M : Matrix (Fin 3) (Fin 3) F) i j) h
    simpa [hι, SpecialLinearGroup.map_apply_coe] using this
  have hq0 : IsQuasisimple SL(3, K₀) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K₀ le_rfl
  set R : Subgroup SL(3, F) := ι.range with hR
  have hqR : IsQuasisimple ↥R :=
    LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hinj) hq0
  have hRmem : ∀ M : SL(3, F), M ∈ R ↔ ∀ i j, σ (M i j) = M i j := by
    intro M
    constructor
    · rintro ⟨g, rfl⟩ i j
      exact (hmem _).1 (g i j).2
    · intro hM
      have hdet : (Matrix.of fun i j => (⟨M i j, (hmem _).2 (hM i j)⟩ : K₀)).det = 1 := by
        apply K₀.subtype.injective
        have h1 := RingHom.map_det K₀.subtype
          (Matrix.of fun i j => (⟨M i j, (hmem _).2 (hM i j)⟩ : K₀))
        have h2' : K₀.subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, (hmem _).2 (hM i j)⟩ : K₀)) =
            (M : Matrix (Fin 3) (Fin 3) F) := by
          ext i j
          rfl
        rw [h1, h2', map_one]
        exact M.2
      refine ⟨⟨Matrix.of fun i j => (⟨M i j, (hmem _).2 (hM i j)⟩ : K₀), hdet⟩, ?_⟩
      apply Subtype.ext
      ext i j
      rfl
  have hd0R : d0 F ∈ R := by
    rw [hRmem]
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  have hb1R : b1 F ∈ R := by
    rw [hRmem]
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨R.map (proj 3 F), LocalCores.isQuasisimple_map hqR (proj 3 F) ?_, ?_, ?_, ?_,
    proj 3 F (d0 F), ⟨d0 F, hd0R, rfl⟩, ?_, ?_, ?_⟩
  · intro hle
    exact d0_not_mem_scalars h2 (by simpa using hle hd0R)
  · exact two_le_pRank_of_b1_d0 h2 ⟨b1 F, hb1R, rfl⟩ ⟨d0 F, hd0R, rfl⟩
  · rintro _ ⟨M, hM, rfl⟩
    rw [fieldAut_proj]
    congr 1
    exact (map_eq_self_iff σ M).2 ((hRmem M).1 hM)
  · intro x hx
    obtain ⟨xt, rfl⟩ := proj_surjective 3 F x
    rw [fieldAut_proj] at hx
    have hz := proj_eq_proj_iff.1 hx
    set z : SL(3, F) := (SpecialLinearGroup.map σ.toRingHom xt)⁻¹ * xt with hzdef
    have hzc : ∀ M : SL(3, F), M * z = z * M := fun M =>
      mem_center_iff.1 (scalars_le_center 3 F hz) M
    have hxσ : SpecialLinearGroup.map σ.toRingHom xt = xt * z⁻¹ := by
      rw [hzdef]
      group
    rintro _ ⟨M, hM, rfl⟩
    have hM' : M ∈ R := hM
    refine ⟨xt * M * xt⁻¹, SetLike.mem_coe.2 ?_, by simp⟩
    rw [hRmem, ← map_eq_self_iff σ]
    rw [map_mul, map_mul, map_inv, hxσ, (map_eq_self_iff σ M).2 ((hRmem M).1 hM')]
    have hzc' : ∀ M : SL(3, F), M * z⁻¹ = z⁻¹ * M := fun M => by
      have := hzc M
      calc M * z⁻¹ = z⁻¹ * (z * M) * z⁻¹ := by group
        _ = z⁻¹ * (M * z) * z⁻¹ := by rw [this]
        _ = z⁻¹ * M := by group
    calc xt * z⁻¹ * M * (xt * z⁻¹)⁻¹ = xt * (z⁻¹ * M * z) * xt⁻¹ := by group
      _ = xt * M * xt⁻¹ := by rw [← hzc' M]; group
  · rw [← map_mul, d0_mul_self, map_one]
  · intro h
    exact d0_not_mem_scalars h2 (proj_eq_one_iff.1 h)
  · obtain ⟨a, ha⟩ := hσ
    have hζ : a - σ a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
    have hσζ : σ (a - σ a) = -(a - σ a) := by rw [map_sub, hσσ]; ring
    refine ⟨proj 3 F (kz _ hζ), ?_⟩
    rw [fieldAut_proj, map_kz σ hζ hσζ, map_mul, mul_inv_cancel_right]

end S3OuterField

end CFSG.GH74.Generic.BProg.B3
