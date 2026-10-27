module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagThreeCore
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLinBlock

public section

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Curtis.Coordinator.SPLCell CFSG.RankThree.PartOne.KCLinComm

namespace CFSG.HardMathSupport.Malle.E27Lie

variable {F : Type} [Field F]

theorem scalar_of_commute_matrix (A : GL (Fin 3) F) (c : Fˣ)
    (hc : A ^ 3 = GeneralLinearGroup.scalar (Fin 3) c)
    (hirr : Irreducible (X ^ 3 - C (c : F) : F[X]))
    (g : Matrix (Fin 3) (Fin 3) F) (hcomm : (A : Matrix (Fin 3) (Fin 3) F) * g = g * A)
    (hdet : g.det = 1) (a : F) (hg : g ^ 3 = Matrix.scalar (Fin 3) a) :
    ∃ s : F, g = Matrix.scalar (Fin 3) s := by
  have hf : Polynomial.aeval (Matrix.toLinAlgEquiv' (A : Matrix (Fin 3) (Fin 3) F))
      (X ^ 3 - C (c : F) : F[X]) = 0 := by
    have := aeval_linEnd_X_pow_sub_C (y := A) (p := 3) c hc
    rwa [linEnd, ← toLinAlgEquiv'_eq_toLin'] at this
  have hscal : ∀ b : F, Matrix.scalar (Fin 3) b = algebraMap F (Matrix (Fin 3) (Fin 3) F) b :=
    fun b => by simp [Matrix.scalar_apply, Matrix.algebraMap_eq_diagonal]
  obtain ⟨s, hs⟩ := scalar_of_commute_irreducible (F := F) (V := Fin 3 → F) (by simp)
    (Matrix.toLinAlgEquiv' (A : Matrix (Fin 3) (Fin 3) F)) (Matrix.toLinAlgEquiv' g) c a hirr hf
    (by
      show _ * _ = _ * _
      rw [← map_mul, ← map_mul, hcomm])
    (by rw [toLinAlgEquiv'_eq_toLin', LinearMap.det_toLin', hdet])
    (by
      rw [← map_pow, hg, hscal, AlgEquiv.commutes])
  refine ⟨s, ?_⟩
  apply Matrix.toLinAlgEquiv'.injective
  rw [hs, hscal, AlgEquiv.commutes]


open CFSG.ComponentClassification in
theorem card_le_three_of_fixed_exponent_three [Finite F] (A : GL (Fin 3) F) (c : Fˣ)
    (hc : A ^ 3 = GeneralLinearGroup.scalar (Fin 3) c) (hnp : ∀ b : F, b ^ 3 ≠ c)
    (T : Subgroup (projectiveSL 3 F)) (hfix : ∀ x ∈ T, conjAut 3 F A x = x)
    (hT3 : ∀ x ∈ T, x ^ 3 = 1) : Nat.card T ≤ 3 := by
  classical
  have hirr : Irreducible (X ^ 3 - C (c : F) : F[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_three hnp
  set slc := CatalogueBHigherLinearAction.slConjugation 3 F A with hslc
  have hmem : ∀ g : SpecialLinearGroup (Fin 3) F, proj 3 F g ∈ T →
      slc g * g⁻¹ ∈ scalars 3 F := by
    intro g hg
    have h1 : proj 3 F (slc g) = proj 3 F g := by
      rw [hslc, ← conjAut_proj]; exact hfix _ hg
    apply proj_eq_one_iff.1
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  let Tt : Subgroup (SpecialLinearGroup (Fin 3) F) := T.comap (proj 3 F)
  let Λ : Tt →* scalars 3 F :=
    { toFun := fun g => ⟨slc g * (g : SpecialLinearGroup (Fin 3) F)⁻¹, hmem g g.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro g h
        apply Subtype.ext
        have hz := Subgroup.mem_center_iff.1 (scalars_le_center 3 F (hmem h h.2))
        have e : slc g * (slc h * (h : SpecialLinearGroup (Fin 3) F)⁻¹ *
            (g : SpecialLinearGroup (Fin 3) F)⁻¹) =
            slc g * (g : SpecialLinearGroup (Fin 3) F)⁻¹ *
              (slc h * (h : SpecialLinearGroup (Fin 3) F)⁻¹) := by
          rw [← hz, mul_assoc]
        simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]
        rw [← e]
        group }
  let π : Tt →* T := (proj 3 F).subgroupComap T
  have hπ : Function.Surjective π :=
    MonoidHom.subgroupComap_surjective _ _ (proj_surjective 3 F)
  have hker1 : π.ker ≤ Λ.ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    have h1 : proj 3 F g = 1 := congrArg Subtype.val hg
    obtain ⟨d, -, hgd⟩ := proj_eq_one_iff.1 h1
    apply Subtype.ext
    show slc g * (g : SpecialLinearGroup (Fin 3) F)⁻¹ = 1
    rw [mul_inv_eq_one]
    apply Subtype.ext
    rw [hslc, CatalogueBHigherLinearAction.slConjugation_matrix, hgd,
      show Matrix.scalar (Fin 3) (d : F) = (d : F) • (1 : Matrix (Fin 3) (Fin 3) F) from by
        simp [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal],
      Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.mul_inv]
  have hker2 : Λ.ker ≤ π.ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    have h1 : slc g * (g : SpecialLinearGroup (Fin 3) F)⁻¹ = 1 := congrArg Subtype.val hg
    have hcomm_sl : slc g = g := mul_inv_eq_one.1 h1
    have e := CatalogueBHigherLinearAction.slConjugation_matrix 3 F A g
    rw [← hslc, hcomm_sl] at e
    have hcomm : (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
        (g : Matrix (Fin 3) (Fin 3) F) * A := by
      calc (A : Matrix (Fin 3) (Fin 3) F) * g
          = (A : Matrix (Fin 3) (Fin 3) F) * g * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
              * A := by rw [mul_assoc _ _ (A : Matrix (Fin 3) (Fin 3) F), Units.inv_mul, mul_one]
        _ = g * A := by rw [← e]
    have hg3 : (g : SpecialLinearGroup (Fin 3) F) ^ 3 ∈ scalars 3 F := by
      apply proj_eq_one_iff.1
      rw [map_pow]
      exact hT3 _ g.2
    obtain ⟨d, -, hgd⟩ := hg3
    obtain ⟨s, hs⟩ := scalar_of_commute_matrix A c hc hirr g hcomm g.1.2 (d : F)
      (hgd ▸ (Matrix.SpecialLinearGroup.coe_pow _ 3).symm)
    have hs3 : s ^ 3 = 1 := by
      have := (g : SpecialLinearGroup (Fin 3) F).2
      rw [hs] at this
      simpa [Matrix.scalar_apply, Matrix.det_diagonal] using this
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hs3
    apply Subtype.ext
    apply proj_eq_one_iff.2
    refine ⟨Units.mk0 s hs0, Units.ext (by simpa using hs3), hs⟩
  let Φ : T →* scalars 3 F := MonoidHom.liftOfSurjective π hπ ⟨Λ, hker1⟩
  have hΦ : ∀ g : Tt, Φ (π g) = Λ g := fun g =>
    π.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hπ) ⟨Λ, hker1⟩ g
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    obtain ⟨g, rfl⟩ := hπ t
    rw [hΦ] at ht
    exact hker2 ht
  have hsc : Nat.card (scalars 3 F) ≤ 3 := by
    rw [scalars_eq_center, Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (⟨0, by norm_num⟩ : Fin 3)).toEquiv,
      Fintype.card_fin]
    exact _root_.card_rootsOfUnity (k := 3) (R := F)
  exact (Nat.card_le_card_of_injective Φ hΦinj).trans hsc

end CFSG.HardMathSupport.Malle.E27Lie
