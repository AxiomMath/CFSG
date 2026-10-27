module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P47Fld

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Sub

variable {F : Type} [Field F]

@[expose] def fixField (σ : F ≃+* F) : Subfield F := σ.toRingHom.eqLocusField (RingHom.id F)

theorem map_map_fixField (σ : F ≃+* F) (N : SpecialLinearGroup (Fin 3) ↥(fixField σ)) :
    SpecialLinearGroup.map σ.toRingHom (SpecialLinearGroup.map (fixField σ).subtype N) =
      SpecialLinearGroup.map (fixField σ).subtype N := by
  ext i j
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact (N i j).2

theorem exists_preimage_of_fixed (σ : F ≃+* F) {T : SpecialLinearGroup (Fin 3) F}
    (hT : SpecialLinearGroup.map σ.toRingHom T = T) :
    ∃ N : SpecialLinearGroup (Fin 3) ↥(fixField σ),
      SpecialLinearGroup.map (fixField σ).subtype N = T := by
  have hentry : ∀ i j, σ ((T : Matrix (Fin 3) (Fin 3) F) i j) = (T : Matrix (Fin 3) (Fin 3) F) i j := by
    intro i j
    have := congrFun (congrFun (congrArg (fun g : SpecialLinearGroup (Fin 3) F =>
      (g : Matrix (Fin 3) (Fin 3) F)) hT) i) j
    simpa [SpecialLinearGroup.map_apply_coe] using this
  let N0 : Matrix (Fin 3) (Fin 3) ↥(fixField σ) :=
    Matrix.of fun i j => (⟨(T : Matrix (Fin 3) (Fin 3) F) i j, hentry i j⟩ : ↥(fixField σ))
  have hN0 : (fixField σ).subtype.mapMatrix N0 = (T : Matrix (Fin 3) (Fin 3) F) := by
    ext i j
    rfl
  have hdet : N0.det = 1 := by
    apply (fixField σ).subtype.injective
    rw [RingHom.map_det, hN0, T.2, map_one]
  let N : SpecialLinearGroup (Fin 3) ↥(fixField σ) := ⟨N0, hdet⟩
  refine ⟨N, ?_⟩
  ext i j
  simp only [SpecialLinearGroup.map_apply_coe]
  exact congrFun (congrFun hN0 i) j

end Sub

section Emb

variable {F : Type} [Field F] (F0 : Subfield F)

@[expose] noncomputable def subHom : SpecialLinearGroup (Fin 3) ↥F0 →* projectiveSL 3 F :=
  (proj 3 F).comp (SpecialLinearGroup.map F0.subtype)

theorem scalars_le_ker_subHom : scalars 3 ↥F0 ≤ (subHom F0).ker := by
  intro s hs
  obtain ⟨c, hc3, hcm⟩ := mem_scalars.1 hs
  rw [MonoidHom.mem_ker, subHom, MonoidHom.comp_apply, proj_eq_one_iff]
  refine mem_scalars.2 ⟨Units.map F0.subtype.toMonoidHom c, ?_, ?_⟩
  · rw [← map_pow, hc3, map_one]
  · ext i j
    have := congrFun (congrFun hcm i) j
    rw [SpecialLinearGroup.map_apply_coe]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [this]
    by_cases hij : i = j
    · subst hij; simp [Matrix.scalar_apply]
    · simp [Matrix.scalar_apply, hij]

@[expose] noncomputable def subEmb : projectiveSL 3 ↥F0 →* projectiveSL 3 F :=
  QuotientGroup.lift (scalars 3 ↥F0) (subHom F0) (scalars_le_ker_subHom F0)

theorem subEmb_proj (g : SpecialLinearGroup (Fin 3) ↥F0) :
    subEmb F0 (proj 3 ↥F0 g) = proj 3 F (SpecialLinearGroup.map F0.subtype g) := rfl

theorem subEmb_injective : Function.Injective (subEmb F0) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨g, rfl⟩ := proj_surjective 3 ↥F0 x
  rw [subEmb_proj, proj_eq_one_iff] at hx
  obtain ⟨c, hc3, hcm⟩ := mem_scalars.1 hx
  rw [proj_eq_one_iff]
  have hentry : ∀ i j, F0.subtype ((g : Matrix (Fin 3) (Fin 3) ↥F0) i j) =
      (scalar (Fin 3) (c : F)) i j := by
    intro i j
    have := congrFun (congrFun hcm i) j
    rw [SpecialLinearGroup.map_apply_coe] at this
    simpa using this
  have ha : F0.subtype ((g : Matrix (Fin 3) (Fin 3) ↥F0) 0 0) = (c : F) := by
    simpa using hentry 0 0
  have ha0 : (g : Matrix (Fin 3) (Fin 3) ↥F0) 0 0 ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact c.ne_zero ha.symm
  refine mem_scalars.2 ⟨Units.mk0 _ ha0, ?_, ?_⟩
  · apply Units.ext
    apply F0.subtype.injective
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, ha]
    have := congrArg Units.val hc3
    simpa using this
  · ext i j
    change F0.subtype ((g : Matrix (Fin 3) (Fin 3) ↥F0) i j) =
      F0.subtype ((scalar (Fin 3) ((Units.mk0 _ ha0 : (↥F0)ˣ) : ↥F0)) i j)
    rw [hentry i j]
    by_cases hij : i = j
    · subst hij; simp [Matrix.scalar_apply, ha]
    · simp [Matrix.scalar_apply, hij]

@[expose] noncomputable def subRange : Subgroup (projectiveSL 3 F) := (subEmb F0).range

theorem mem_subRange {q : projectiveSL 3 F} :
    q ∈ subRange F0 ↔
      ∃ N : SpecialLinearGroup (Fin 3) ↥F0, proj 3 F (SpecialLinearGroup.map F0.subtype N) = q := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective 3 ↥F0 y
    exact ⟨g, rfl⟩
  · rintro ⟨N, rfl⟩
    exact ⟨proj 3 ↥F0 N, rfl⟩

end Emb

section Norm

variable {F : Type} [Field F]

theorem fieldAut_fix_subRange (σ : F ≃+* F) {q : projectiveSL 3 F} (hq : q ∈ subRange (fixField σ)) :
    fieldAut 3 F σ q = q := by
  obtain ⟨N, rfl⟩ := (mem_subRange _).1 hq
  rw [fieldAut_proj, map_map_fixField]

theorem conj_mem_subRange (σ : F ≃+* F) {y : projectiveSL 3 F} (hy : fieldAut 3 F σ y = y)
    {q : projectiveSL 3 F} (hq : q ∈ subRange (fixField σ)) : y * q * y⁻¹ ∈ subRange (fixField σ) := by
  obtain ⟨M, rfl⟩ := proj_surjective 3 F y
  obtain ⟨N, rfl⟩ := (mem_subRange _).1 hq
  rw [fieldAut_proj] at hy
  have hs : M⁻¹ * SpecialLinearGroup.map σ.toRingHom M ∈ scalars 3 F := proj_eq_proj_iff.1 hy.symm
  have hcen : M⁻¹ * SpecialLinearGroup.map σ.toRingHom M ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) :=
    scalars_le_center 3 F hs
  set s := M⁻¹ * SpecialLinearGroup.map σ.toRingHom M with hsdef
  have hMs : SpecialLinearGroup.map σ.toRingHom M = M * s := by rw [hsdef]; group
  have hsN : s * SpecialLinearGroup.map (fixField σ).subtype N * s⁻¹ =
      SpecialLinearGroup.map (fixField σ).subtype N :=
    mul_inv_eq_iff_eq_mul.2 ((Subgroup.mem_center_iff.1 hcen _).symm)
  have hT : SpecialLinearGroup.map σ.toRingHom
      (M * SpecialLinearGroup.map (fixField σ).subtype N * M⁻¹) =
      M * SpecialLinearGroup.map (fixField σ).subtype N * M⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_map_fixField, hMs]
    calc M * s * SpecialLinearGroup.map (fixField σ).subtype N * (M * s)⁻¹
        = M * (s * SpecialLinearGroup.map (fixField σ).subtype N * s⁻¹) * M⁻¹ := by group
      _ = M * SpecialLinearGroup.map (fixField σ).subtype N * M⁻¹ := by rw [hsN]
  obtain ⟨N', hN'⟩ := exists_preimage_of_fixed σ hT
  refine (mem_subRange _).2 ⟨N', ?_⟩
  rw [hN', map_mul, map_mul, map_inv]

theorem mem_normalizer_subRange (σ : F ≃+* F) {y : projectiveSL 3 F} (hy : fieldAut 3 F σ y = y) :
    y ∈ normalizer (subRange (fixField σ) : Set (projectiveSL 3 F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  refine ⟨fun hq => conj_mem_subRange σ hy hq, fun hq => ?_⟩
  have hy' : fieldAut 3 F σ y⁻¹ = y⁻¹ := by rw [map_inv, hy]
  have := conj_mem_subRange σ hy' hq
  simpa [mul_assoc] using this

end Norm

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P47Fld
