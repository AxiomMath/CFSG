module

public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModelsBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure

public section

namespace CFSG.QuasithinUnique

open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryModel
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External

variable {K : Type} [Field K]

@[expose] noncomputable def unitaryRootCenterHom [CharP K 2] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Multiplicative (unitaryCoverFixedField J) →* ProjectiveSpecialUnitaryMatrixGroup J :=
  ((hermitianUnipotentPSU J hJ).comp (unitaryCoverFirstCoord J).ker.subtype).comp
    (unitaryCoverZeroFirstEquiv J).symm.toMonoidHom

theorem unitaryRootCenterHom_apply [CharP K 2] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (w : Multiplicative (unitaryCoverFixedField J)) :
    unitaryRootCenterHom J hJ w =
      hermitianUnipotentPSU J hJ ((unitaryCoverZeroFirstEquiv J).symm w).1 := rfl

theorem unitaryRootCenterHom_injective [CharP K 2] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Function.Injective (unitaryRootCenterHom J hJ) :=
  ((CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ).comp
    Subtype.val_injective).comp
    (unitaryCoverZeroFirstEquiv J).symm.injective

theorem range_unitaryRootCenterHom [CharP K 2] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (unitaryRootCenterHom J hJ).range =
      (unitaryCoverFirstCoord J).ker.map (hermitianUnipotentPSU J hJ) := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, ((unitaryCoverZeroFirstEquiv J).symm w).2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(unitaryCoverZeroFirstEquiv J) ⟨z, hz⟩, by
      rw [unitaryRootCenterHom_apply, MulEquiv.symm_apply_apply]⟩


noncomputable def unitaryTorusScalar (J : HermitianForm 3 K) (k : Kˣ) :
    unitaryCoverFixedField J :=
  ⟨(J.conj (k : K))⁻¹ * (k : K)⁻¹, by
    change J.conj ((J.conj (k : K))⁻¹ * (k : K)⁻¹) = (J.conj (k : K))⁻¹ * (k : K)⁻¹
    rw [map_mul, map_inv₀, map_inv₀, J.conj_involutive, mul_comm]⟩

theorem unitaryTorusScalar_ne_zero (J : HermitianForm 3 K) (k : Kˣ) :
    unitaryTorusScalar J k ≠ 0 := fun h => by
  have h1 : (J.conj (k : K))⁻¹ * (k : K)⁻¹ = 0 := congrArg Subtype.val h
  have hk : (k : K) ≠ 0 := k.ne_zero
  have hc : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
  exact mul_ne_zero (inv_ne_zero hc) (inv_ne_zero hk) h1

theorem unitary_torus_conj_center [CharP K 2] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (k : Kˣ) (x : unitaryCoverFixedField J) :
    hermitianTorusPSU J hJ k * unitaryRootCenterHom J hJ (Multiplicative.ofAdd x) *
        (hermitianTorusPSU J hJ k)⁻¹ =
      unitaryRootCenterHom J hJ (Multiplicative.ofAdd (unitaryTorusScalar J k * x)) := by
  rw [unitaryRootCenterHom_apply, unitaryRootCenterHom_apply,
    unitaryCoverTorus_conj_root J hJ k]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · rw [hermitianTorusAction_fst]
    change _ * _ * _ = (0 : K)
    rw [show ((unitaryCoverZeroFirstEquiv J).symm (Multiplicative.ofAdd x)).1.1.1 = 0 from
      ((unitaryCoverZeroFirstEquiv J).symm (Multiplicative.ofAdd x)).2, zero_mul, zero_mul]
  · rw [hermitianTorusAction_snd]
    change ((x : K)) * (J.conj (k : K))⁻¹ * (k : K)⁻¹ = ((unitaryTorusScalar J k * x : _) : K)
    change ((x : K)) * (J.conj (k : K))⁻¹ * (k : K)⁻¹ =
      ((J.conj (k : K))⁻¹ * (k : K)⁻¹) * (x : K)
    ring


theorem unitary_hasFieldScalarStructure [Finite K] (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    HasFieldScalarStructure
      ((unitaryCoverFirstCoord J).ker.map (hermitianUnipotentPSU J hJ)) (2 ^ f) := by
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective _ Subtype.coe_injective
  have hfixcard : Nat.card (unitaryCoverFixedField J) = 2 ^ f := by
    let c : unitaryCoverFixedField J ≃ {x : K // J.conj x = x} :=
      { toFun := fun x => ⟨x, x.property⟩
        invFun := fun x => ⟨x, x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr c).trans hfixed
  obtain ⟨rho, -, -, -, -, -, -, -, hstab, -, -, -, -, -, -, -, hreg, -⟩ :=
    unitary_entire_root_point_structure J f hf hcard hfixed hJ
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (unitaryIsotropicPoints J) :=
    MulAction.compHom _ rho
  have hsup := root_sup_torus J f hf hcard hfixed hJ
  rw [range_torusPSU] at hsup
  have hstabα : MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J)
      (unitaryOuterIsotropicPoint J hJ 0 (by decide)) = unitaryCoordinateStabilizer J 0 :=
    (Subgroup.ext fun _ => Iff.rfl).trans hstab
  have h := hasFieldScalarStructure_of_regular_root
    (unitaryOuterIsotropicPoint J hJ 0 (by decide)) (hermitianUnipotentPSU J hJ).range
    (hermitianTorusPSU J hJ).range (unitaryCoverFixedField J) (unitaryRootCenterHom J hJ)
    (unitaryRootCenterHom_injective J hJ) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [range_unitaryRootCenterHom, hfixcard] at h
    exact h
  · rw [range_unitaryRootCenterHom]
    exact Subgroup.map_le_range _ _
  · rw [hstabα]
    exact unitary_entire_root_fixes_first_coordinate J hJ
  · intro ω u hu hω hfix
    have h1 := (hreg ω ω hω hω).unique (y₁ := ⟨u, hu⟩) (y₂ := 1) hfix (by simp)
    exact congrArg Subtype.val h1
  · rw [hstabα]
    exact hsup.ge
  · rintro _ ⟨w, rfl⟩ x
    rw [unitaryRootCenterHom_apply, mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul]
    congr 1
    exact (coord_mul_comm_of_fst_eq_zero J
      (((unitaryCoverZeroFirstEquiv J).symm (Multiplicative.ofAdd x)).2) w).symm
  · rintro _ ⟨k, rfl⟩
    exact ⟨Units.mk0 (unitaryTorusScalar J k) (unitaryTorusScalar_ne_zero J k),
      fun x => unitary_torus_conj_center J hJ k x⟩
  · intro c
    have hcne : ((c⁻¹ : (unitaryCoverFixedField J)ˣ) : unitaryCoverFixedField J) ≠ 0 :=
      (c⁻¹).ne_zero
    obtain ⟨b, hb0, hb⟩ := huppert_II_10_4_norm_surjective J (2 ^ f) hcard hfixed
      (((c⁻¹ : (unitaryCoverFixedField J)ˣ) : unitaryCoverFixedField J) : K)
      ((c⁻¹ : (unitaryCoverFixedField J)ˣ).1).2 (fun h => hcne (Subtype.ext h))
    refine ⟨hermitianTorusPSU J hJ (Units.mk0 b hb0), ⟨_, rfl⟩, fun x => ?_⟩
    have hs : unitaryTorusScalar J (Units.mk0 b hb0) = (c : unitaryCoverFixedField J) := by
      apply Subtype.ext
      change (J.conj b)⁻¹ * b⁻¹ = (((c : unitaryCoverFixedField J)) : K)
      have hb' : (((c : unitaryCoverFixedField J)) : K)⁻¹ = b * J.conj b := by
        rw [hb]
        simp
      rw [← mul_inv_rev, ← hb', inv_inv]
    rw [unitary_torus_conj_center, hs]

end CFSG.QuasithinUnique
