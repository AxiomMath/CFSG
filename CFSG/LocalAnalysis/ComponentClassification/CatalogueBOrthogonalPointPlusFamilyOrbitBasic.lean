module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbitBasic

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit

open scoped Pointwise
open CatalogueBOrthogonalSmallFamilyOrbit

universe u

variable {G : Type u} [Group G]

@[expose] def borelCorrection (alpha : MulAut G) (g : G) : MulAut G :=
  MulAut.conj g⁻¹ * alpha

theorem borelCorrection_apply (alpha : MulAut G) (g x : G) :
    borelCorrection alpha g x = g⁻¹ * alpha x * g := by
  change (MulAut.conj g⁻¹) (alpha x) = _
  rw [MulAut.conj_apply, inv_inv]

theorem borelCorrection_symm_apply (alpha : MulAut G) (g x : G) :
    (borelCorrection alpha g).symm x = alpha.symm (g * x * g⁻¹) := by
  change alpha.symm ((MulAut.conj g⁻¹).symm x) = _
  rw [MulAut.conj_symm_apply, inv_inv]

theorem sylow_normalizer_image_conjugate {p : ℕ} [Fact p.Prime]
    [Finite (Sylow p G)] (P : Sylow p G) (alpha : MulAut G) :
    ∃ g : G,
      (Subgroup.normalizer (P : Set G)).map alpha.toMonoidHom =
        (Subgroup.normalizer (P : Set G)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P (alpha • P)
  have hP : (P : Subgroup G).map (MulAut.conj g).toMonoidHom =
      (P : Subgroup G).map alpha.toMonoidHom := by
    change ((g • P : Sylow p G) : Subgroup G) =
      ((alpha • P : Sylow p G) : Subgroup G)
    exact congrArg Sylow.toSubgroup hg
  refine ⟨g, ?_⟩
  calc
    _ = Subgroup.normalizer (((P : Subgroup G).map alpha.toMonoidHom) : Set G) :=
      Subgroup.map_equiv_normalizer_eq (P : Subgroup G) alpha
    _ = Subgroup.normalizer
        (((P : Subgroup G).map (MulAut.conj g).toMonoidHom) : Set G) :=
      congrArg (fun U : Subgroup G => Subgroup.normalizer (U : Set G)) hP.symm
    _ = _ := (Subgroup.map_equiv_normalizer_eq (P : Subgroup G) (MulAut.conj g)).symm

theorem borelCorrection_borel (B : Subgroup G) (alpha : MulAut G) (g : G)
    (hB : B.map alpha.toMonoidHom = B.map (MulAut.conj g).toMonoidHom) :
    B.map (borelCorrection alpha g).toMonoidHom = B := by
  change (MulAut.conj g⁻¹ * alpha) • B = B
  rw [mul_smul]
  change MulAut.conj g⁻¹ • (B.map alpha.toMonoidHom) = B
  rw [hB]
  change MulAut.conj g⁻¹ • (MulAut.conj g • B) = B
  rw [← mul_smul, ← map_mul]
  simp

theorem borelCorrection_overgroup (B D : Subgroup G) (hBD : B ≤ D)
    (alpha : MulAut G) (g : G)
    (hB : B.map alpha.toMonoidHom = B.map (MulAut.conj g).toMonoidHom) :
    B ≤ D.map (borelCorrection alpha g).toMonoidHom := by
  rw [← borelCorrection_borel B alpha g hB]
  exact Subgroup.map_mono hBD

theorem borelCorrection_isCoatom (D : Subgroup G) (hD : IsCoatom D)
    (alpha : MulAut G) (g : G) :
    IsCoatom (D.map (borelCorrection alpha g).toMonoidHom) :=
  (OrderIso.isCoatom_iff (borelCorrection alpha g).mapSubgroup D).2 hD

theorem borelCorrection_index (D : Subgroup G) (alpha : MulAut G) (g : G) :
    (D.map (borelCorrection alpha g).toMonoidHom).index = D.index :=
  Subgroup.index_map_equiv D (borelCorrection alpha g)

theorem borelCorrection_family (D : Subgroup G) (alpha : MulAut G) (g : G) :
    conjugacyFamily (D.map (borelCorrection alpha g).toMonoidHom) =
      alpha • conjugacyFamily D := by
  rw [← conjugacyFamily_covariance, borelCorrection, mul_smul,
    conjugacyFamily_covariance, conj_conjugacyFamily]

theorem exists_sylow_borel_corrected_overgroup {p : ℕ} [Fact p.Prime]
    [Finite (Sylow p G)] (P : Sylow p G) (D : Subgroup G)
    (hBD : Subgroup.normalizer (P : Set G) ≤ D) (hD : IsCoatom D)
    (alpha : MulAut G) :
    ∃ g : G,
      (Subgroup.normalizer (P : Set G)).map (borelCorrection alpha g).toMonoidHom =
          Subgroup.normalizer (P : Set G) ∧
        Subgroup.normalizer (P : Set G) ≤ D.map (borelCorrection alpha g).toMonoidHom ∧
        IsCoatom (D.map (borelCorrection alpha g).toMonoidHom) ∧
        (D.map (borelCorrection alpha g).toMonoidHom).index = D.index ∧
        conjugacyFamily (D.map (borelCorrection alpha g).toMonoidHom) =
          alpha • conjugacyFamily D := by
  obtain ⟨g, hg⟩ := sylow_normalizer_image_conjugate P alpha
  exact ⟨g, borelCorrection_borel _ alpha g hg,
    borelCorrection_overgroup _ D hBD alpha g hg,
    borelCorrection_isCoatom D hD alpha g, borelCorrection_index D alpha g,
    borelCorrection_family D alpha g⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
