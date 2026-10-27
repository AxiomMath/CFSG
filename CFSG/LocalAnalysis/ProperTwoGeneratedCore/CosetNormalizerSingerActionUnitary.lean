module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSingerActionBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryModel

variable {K : Type} [Field K]

theorem card_unitaryCoverFixedField (J : HermitianForm 3 K) :
    Nat.card (unitaryCoverFixedField J) = Nat.card {x : K // J.conj x = x} :=
  Nat.card_congr
    { toFun := fun x => ⟨x, x.property⟩
      invFun := fun x => ⟨x, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

section CharTwo

variable [CharP K 2]

@[expose] def unitaryCenterCoord (J : HermitianForm 3 K) (b : unitaryCoverFixedField J) :
    hermitianUnipotentCoord J :=
  ⟨(0, b), by
    have hb : J.conj (b : K) = b := b.property
    simp [hb, CharTwo.add_self_eq_zero]⟩

@[expose] def unitaryCenterHom (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Multiplicative (unitaryCoverFixedField J) →* ProjectiveSpecialUnitaryMatrixGroup J where
  toFun b := hermitianUnipotentPSU J hJ (unitaryCenterCoord J (Multiplicative.toAdd b))
  map_one' := by
    rw [← map_one (hermitianUnipotentPSU J hJ)]
    rfl
  map_mul' b c := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · change (0 : K) = 0 + 0
      rw [add_zero]
    · change ((Multiplicative.toAdd (b * c) : unitaryCoverFixedField J) : K) =
        (Multiplicative.toAdd b : unitaryCoverFixedField J) +
          (Multiplicative.toAdd c : unitaryCoverFixedField J) - 0 * J.conj 0
      simp

theorem unitaryCenterHom_injective (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Function.Injective (unitaryCenterHom J hJ) := fun b c h => by
  have h1 := congrArg (fun z : hermitianUnipotentCoord J => z.1.2)
    (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ h)
  exact Multiplicative.toAdd.injective (Subtype.ext h1)

theorem involutionSubgroup_unitaryRoot (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    involutionSubgroup (hermitianUnipotentPSU J hJ).range = (unitaryCenterHom J hJ).range := by
  refine involutionSubgroup_eq fun x => ⟨?_, ?_⟩
  · rintro ⟨⟨z, rfl⟩, h2⟩
    obtain ⟨hz1, -⟩ := (unitary_projective_root_involution_iff J hJ z).1 h2
    have hz : J.conj z.1.2 = z.1.2 := by
      have h := z.2
      rw [hz1, zero_mul, add_zero] at h
      exact (CharTwo.add_eq_zero.1 h).symm
    refine ⟨⟨Multiplicative.ofAdd ⟨z.1.2, hz⟩, ?_⟩, fun h1 => ?_⟩
    · change hermitianUnipotentPSU J hJ (unitaryCenterCoord J ⟨z.1.2, hz⟩) = _
      congr 1
      exact Subtype.ext (Prod.ext hz1.symm rfl)
    · rw [h1, orderOf_one] at h2
      exact absurd h2 (by norm_num)
  · rintro ⟨⟨b, rfl⟩, h1⟩
    refine ⟨⟨_, rfl⟩, (unitary_projective_root_involution_iff J hJ _).2 ⟨rfl, fun hb => ?_⟩⟩
    apply h1
    have hb0 : b = 1 := Multiplicative.toAdd.injective (Subtype.ext hb)
    rw [hb0, map_one]

theorem unitaryRoot_le_rootScalarSubgroup (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (hermitianUnipotentPSU J hJ).range ≤ rootScalarSubgroup (unitaryCenterHom J hJ) := by
  rintro _ ⟨w, rfl⟩
  refine ⟨1, fun b => ?_⟩
  change hermitianUnipotentPSU J hJ w * hermitianUnipotentPSU J hJ (unitaryCenterCoord J b) *
      (hermitianUnipotentPSU J hJ w)⁻¹ =
    hermitianUnipotentPSU J hJ (unitaryCenterCoord J ((1 : (unitaryCoverFixedField J)ˣ) * b))
  rw [Units.val_one, one_mul, ← map_mul,
    ← coord_mul_comm_of_fst_eq_zero J (z := unitaryCenterCoord J b) rfl w, map_mul,
    mul_inv_cancel_right]

theorem hermitianTorusPSU_conj_unitaryCenterHom (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (k : Kˣ)
    (c : (unitaryCoverFixedField J)ˣ)
    (hc : ((c : unitaryCoverFixedField J) : K) = (J.conj (k : K))⁻¹ * (k : K)⁻¹)
    (b : unitaryCoverFixedField J) :
    hermitianTorusPSU J hJ k * unitaryCenterHom J hJ (Multiplicative.ofAdd b) *
        (hermitianTorusPSU J hJ k)⁻¹ =
      unitaryCenterHom J hJ (Multiplicative.ofAdd (c * b)) := by
  change hermitianTorusPSU J hJ k * hermitianUnipotentPSU J hJ (unitaryCenterCoord J b) *
      (hermitianTorusPSU J hJ k)⁻¹ =
    hermitianUnipotentPSU J hJ (unitaryCenterCoord J (c * b))
  rw [unitaryCoverTorus_conj_root]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · simp [unitaryCenterCoord]
  · simp only [hermitianTorusAction_snd, unitaryCenterCoord, MulMemClass.coe_mul, hc]
    ring

theorem unitaryTorus_le_rootScalarSubgroup (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (hermitianTorusPSU J hJ).range ≤ rootScalarSubgroup (unitaryCenterHom J hJ) := by
  rintro _ ⟨k, rfl⟩
  have hk : (k : K) ≠ 0 := k.ne_zero
  have hmem : (J.conj (k : K))⁻¹ * (k : K)⁻¹ ∈ unitaryCoverFixedField J := by
    change J.conj ((J.conj (k : K))⁻¹ * (k : K)⁻¹) = (J.conj (k : K))⁻¹ * (k : K)⁻¹
    rw [map_mul, map_inv₀, map_inv₀, J.conj_involutive, mul_comm]
  have hne : (⟨_, hmem⟩ : unitaryCoverFixedField J) ≠ 0 := fun h => by
    have h1 := congrArg Subtype.val h
    simp only [ZeroMemClass.coe_zero, mul_eq_zero, inv_eq_zero, map_eq_zero] at h1
    exact h1.elim hk hk
  exact ⟨Units.mk0 _ hne, hermitianTorusPSU_conj_unitaryCenterHom J hJ k _ rfl⟩

end CharTwo

variable [Finite K]

theorem exists_conj_mul_eq (J : HermitianForm 3 K) {q : ℕ} (hq : 1 < q)
    (hcard : Nat.card K = q ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (c : (unitaryCoverFixedField J)ˣ) :
    ∃ k : Kˣ, J.conj (k : K) * k = ((c : unitaryCoverFixedField J) : K) := by
  obtain ⟨k, hk⟩ := FiniteField.unitsMap_norm_surjective (unitaryCoverFixedField J) K c
  refine ⟨k, ?_⟩
  have h1 := FiniteField.algebraMap_norm_eq_pow (K := unitaryCoverFixedField J) (K' := K)
    (x := (k : K))
  have hexp : (q ^ 2 - 1) / (q - 1) = q + 1 := by
    rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.sq_sub_sq q 1]
    exact Nat.mul_div_cancel _ (by omega)
  rw [hcard, card_unitaryCoverFixedField, hfixed, hexp, pow_succ,
    ← huppert_II_10_4_conj_eq_frobenius J q hcard hfixed] at h1
  rw [← h1, ← hk]
  rfl

theorem isSingerAction_unitary (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    IsSingerAction (involutionSubgroup (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)))
      (2 ^ f) := by
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  obtain ⟨rho, S, -, -, -, hSR, -, -, hstab, -, -, -, -, -, -, -, hreg, -⟩ :=
    unitary_entire_root_point_structure J f hf hcard hfixed hJ
  set α := unitaryOuterIsotropicPoint J hJ 0 (by decide)
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have hZR : (unitaryCenterHom J hJ).range ≤ (hermitianUnipotentPSU J hJ).range := by
    rw [← involutionSubgroup_unitaryRoot J hJ]
    exact involutionSubgroup_le _
  have hfix : ∀ x ∈ (unitaryCenterHom J hJ).range, rho x α = α := fun x hx => by
    have h1 : x ∈ unitaryCoordinateStabilizer J 0 :=
      unitary_entire_root_fixes_first_coordinate J hJ (hZR hx)
    rw [← hstab] at h1
    exact h1
  have hne : (unitaryCenterHom J hJ).range ≠ ⊥ := by
    have h1 : (1 : unitaryCoverFixedField J) ≠ 0 := one_ne_zero
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨_, Multiplicative.ofAdd 1, rfl⟩, fun h2 => ?_⟩
    have h3 := unitaryCenterHom_injective J hJ
      ((congrArg Subtype.val h2).trans (map_one _).symm)
    exact h1 (Multiplicative.ofAdd.injective h3)
  have hN : Subgroup.normalizer ((unitaryCenterHom J hJ).range :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
        rootScalarSubgroup (unitaryCenterHom J hJ) := by
    intro g hg
    have hgB : g ∈ unitaryCoordinateStabilizer J 0 := by
      rw [← hstab]
      exact fixes_of_mem_normalizer rho hfix
        (fun x hx y hxy hyα => eq_one_of_regular rho hreg (hZR hx) hxy hyα) hne hg
    rw [← root_sup_torus J f hf hcard hfixed hJ, range_torusPSU] at hgB
    exact sup_le (unitaryRoot_le_rootScalarSubgroup J hJ)
      (unitaryTorus_le_rootScalarSubgroup J hJ) hgB
  have hT : ∀ c : (unitaryCoverFixedField J)ˣ, ∃ g : ProjectiveSpecialUnitaryMatrixGroup J,
      ∀ b : unitaryCoverFixedField J,
        g * unitaryCenterHom J hJ (Multiplicative.ofAdd b) * g⁻¹ =
          unitaryCenterHom J hJ (Multiplicative.ofAdd (c * b)) := fun c => by
    obtain ⟨k, hk⟩ := exists_conj_mul_eq J hq hcard hfixed c
    refine ⟨hermitianTorusPSU J hJ k⁻¹, hermitianTorusPSU_conj_unitaryCenterHom J hJ k⁻¹ c ?_⟩
    rw [← hk, Units.val_inv_eq_inv_val, map_inv₀, inv_inv, inv_inv]
  rw [← hfixed, ← card_unitaryCoverFixedField J]
  exact isSingerAction_sylow_of_range (unitaryCenterHom J hJ) (unitaryCenterHom_injective J hJ) S
    (by rw [hSR]; exact involutionSubgroup_unitaryRoot J hJ) hN hT Q

end CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger
