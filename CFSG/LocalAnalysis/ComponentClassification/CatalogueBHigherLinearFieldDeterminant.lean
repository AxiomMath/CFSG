module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldFixed

public section

namespace CFSG.ComponentClassification.CatalogueBHigherLinearField

noncomputable section

open Matrix CatalogueBHigherLinearAction

universe u

theorem mk_mem_pslRange_iff_det_power (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) :
    ProjGenLinGroup.mk A ∈ pslRange n K ↔
      ∃ c : Kˣ, c ^ n = GeneralLinearGroup.det A := by
  rw [pslRange_eq_map]
  constructor
  · rintro ⟨B, hB, hBA⟩
    obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hBA
    have hdetB : GeneralLinearGroup.det B = 1 := by
      rw [CatalogueBGeneralLinear.specialLinearRange_eq_detKernel] at hB
      exact hB
    refine ⟨c, ?_⟩
    have hdet := congrArg GeneralLinearGroup.det hc
    simpa only [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin,
      hdetB, one_mul] using hdet
  · rintro ⟨c, hc⟩
    let B : GL (Fin n) K := A * GeneralLinearGroup.scalar (Fin n) c⁻¹
    have hdetB : GeneralLinearGroup.det B = 1 := by
      change GeneralLinearGroup.det (A * GeneralLinearGroup.scalar (Fin n) c⁻¹) = 1
      rw [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hc, inv_pow,
        mul_inv_cancel]
    refine ⟨B, ?_, ?_⟩
    · rw [CatalogueBGeneralLinear.specialLinearRange_eq_detKernel]
      exact hdetB
    · change ProjGenLinGroup.mk (A * GeneralLinearGroup.scalar (Fin n) c⁻¹) = _
      rw [map_mul, ProjGenLinGroup.mk_scalar, mul_one]

theorem subfield_projectivity_mem_pslRange_iff (n : ℕ) (K : Type u) [Field K]
    (S : Subfield K) (B : GL (Fin n) S) :
    subfieldPGLMap (Fin n) K S (ProjGenLinGroup.mk B) ∈ pslRange n K ↔
      ∃ c : Kˣ, c ^ n = Units.map S.subtype (GeneralLinearGroup.det B) := by
  rw [subfieldPGLMap_mk, mk_mem_pslRange_iff_det_power]
  rw [GeneralLinearGroup.map_det]

theorem mem_fixedT_iff_subfield_det_power
    (n : ℕ) [NeZero n] (K : Type u) [Field K] (sigma : K ≃+* K)
    (g : fixedPGL (Fin n) K sigma) :
    g ∈ fixedT n K sigma ↔
      ∃ B : GL (Fin n) (fixedField K sigma),
        subfieldPGLMap (Fin n) K (fixedField K sigma) (ProjGenLinGroup.mk B) = g.val ∧
          ∃ c : Kˣ, c ^ n = Units.map (fixedField K sigma).subtype
            (GeneralLinearGroup.det B) := by
  constructor
  · intro hg
    obtain ⟨b, hb⟩ := (subfieldPGLEquivFixed (Fin n) K sigma).surjective g
    obtain ⟨B, rfl⟩ := ProjGenLinGroup.mk_surjective b
    have hB : subfieldPGLMap (Fin n) K (fixedField K sigma)
        (ProjGenLinGroup.mk B) = g.val :=
      congrArg Subtype.val hb
    refine ⟨B, hB, ?_⟩
    apply (subfield_projectivity_mem_pslRange_iff n K (fixedField K sigma) B).mp
    rw [hB]
    exact hg
  · rintro ⟨B, hB, hdet⟩
    change g.val ∈ pslRange n K
    rw [← hB]
    exact (subfield_projectivity_mem_pslRange_iff n K (fixedField K sigma) B).mpr hdet

theorem fixed_psl_image_eq_subfield_det_set
    (n : ℕ) [NeZero n] (K : Type u) [Field K] (sigma : K ≃+* K) :
    ((fixedPSL n K sigma).map ProjectiveSpecialLinearGroup.toPGL :
      Set (ProjGenLinGroup (Fin n) K)) =
      {g | ∃ B : GL (Fin n) (fixedField K sigma),
        subfieldPGLMap (Fin n) K (fixedField K sigma) (ProjGenLinGroup.mk B) = g ∧
          ∃ c : Kˣ, c ^ n = Units.map (fixedField K sigma).subtype
            (GeneralLinearGroup.det B)} := by
  rw [fixedPSL_map_eq_intersection]
  ext g
  constructor
  · intro hg
    exact (mem_fixedT_iff_subfield_det_power n K sigma ⟨g, hg.2⟩).mp hg.1
  · rintro ⟨B, hB, hdet⟩
    have hfixed : g ∈ fixedPGL (Fin n) K sigma := by
      rw [← subfieldPGL_range_eq_fixedPGL, ← hB]
      exact ⟨ProjGenLinGroup.mk B, rfl⟩
    exact ⟨(mem_fixedT_iff_subfield_det_power n K sigma ⟨g, hfixed⟩).mpr
      ⟨B, hB, hdet⟩, hfixed⟩

theorem quadratic_fixed_projective_linear_group
    (n : ℕ) (hn : 2 ≤ n) (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    Nat.card K = Nat.card (fixedField K sigma) ^ 2 ∧
      Function.Injective (subfieldPGLMap (Fin n) K (fixedField K sigma)) ∧
      (subfieldPGLMap (Fin n) K (fixedField K sigma)).range = fixedPGL (Fin n) K sigma ∧
      (fixedT n K sigma).Normal ∧
      Nonempty (fixedPSL n K sigma ≃* fixedT n K sigma) ∧
      ((fixedPSL n K sigma).map ProjectiveSpecialLinearGroup.toPGL :
        Set (ProjGenLinGroup (Fin n) K)) =
        {g | ∃ B : GL (Fin n) (fixedField K sigma),
          subfieldPGLMap (Fin n) K (fixedField K sigma) (ProjGenLinGroup.mk B) = g ∧
            ∃ c : Kˣ, c ^ n = Units.map (fixedField K sigma).subtype
              (GeneralLinearGroup.det B)} := by
  let : NeZero n := ⟨by omega⟩
  exact ⟨fixedField_card_square K sigma hsigma hne,
    subfieldPGLMap_injective (Fin n) K (fixedField K sigma),
    subfieldPGL_range_eq_fixedPGL (Fin n) K sigma, inferInstance,
    ⟨fixedPSLEquivT n K sigma⟩, fixed_psl_image_eq_subfield_det_set n K sigma⟩

end

end CFSG.ComponentClassification.CatalogueBHigherLinearField
