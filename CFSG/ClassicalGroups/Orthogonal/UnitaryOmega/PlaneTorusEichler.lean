module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorus
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.KLinearOmega
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open QuadraticMap CFSG.Timmesfeld.ClassicalOrders CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

theorem eichler_mem_normOmega {m : ℕ} (hm : 2 ≤ m) (u w : (F × F) × (Fin m → K)) :
    eichler (normHypForm E m) u w ∈ normOmega E m := by
  have : Finite F := Finite.of_injective _ (algebraMap F K).injective
  have : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  exact (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure
    (normHypForm_polarBilin_nondegenerate E m) (exists_totallySingular_three_hypSum E hm)).1.ge
    (eichler_mem_elementaryGroup _ u w)

theorem exists_twoSubgroup_normalized_of_apply_eq {m : ℕ} (hm : 2 ≤ m) :
    ∃ U : Subgroup (normOmega E m), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ g : normOmega E m,
        (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) ((1, 0), 0) = ((1, 0), 0) →
          g ∈ Subgroup.normalizer (U : Set (normOmega E m)) := by
  classical
  have : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  have he : normHypForm E m ((1, 0), 0) = 0 := by
    simp [normHypForm, hypSum_apply]
  have hO : ∀ g : normOmega E m,
      (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) ∈
        TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m) :=
    fun g => Subgroup.commutator_le_self _ g.2
  refine ⟨(rootGroup (normHypForm E m) ((1, 0), 0)).subgroupOf (normOmega E m), ?_, ?_, ?_⟩
  ·
    let i₀ : Fin m := ⟨0, by omega⟩
    let w : (F × F) × (Fin m → K) := ((0, 0), Pi.single i₀ 1)
    have hw : polar (normHypForm E m) ((1, 0), 0) w = 0 := by
      simp [normHypForm, polar_hypSum, w]
    intro hbot
    have hmem : (⟨eichler (normHypForm E m) ((1, 0), 0) w, eichler_mem_normOmega E hm _ w⟩ :
        normOmega E m) ∈ (rootGroup (normHypForm E m) ((1, 0), 0)).subgroupOf (normOmega E m) :=
      Subgroup.mem_subgroupOf.mpr (eichler_mem_rootGroup hw)
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : eichler (normHypForm E m) ((1, 0), 0) w = 1 := congrArg Subtype.val hmem
    have h2 : (eichler (normHypForm E m) ((1, 0), 0) w ((0, 1), 0)).2 i₀ = 0 := by
      rw [h1]
      rfl
    rw [eichler_apply he hw] at h2
    simp [normHypForm, polar_hypSum, w, i₀] at h2
  · intro g
    refine ⟨1, ?_⟩
    obtain ⟨w, hw, hwg⟩ := mem_rootGroup.mp (Subgroup.mem_subgroupOf.mp g.2)
    have hww : w + w = 0 := by
      rw [← two_smul F w, CharTwo.two_eq_zero, zero_smul]
    have hsq : eichler (normHypForm E m) ((1, 0), 0) w ^ 2 = 1 := by
      rw [pow_two, eichler_mul hw hw, hww, eichler_zero_right]
    apply Subtype.ext
    apply Subtype.ext
    simpa [← hwg] using hsq
  · intro g hg
    have hg' : (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) ((1, 0), 0) =
        (1 : F) • ((1, 0), 0) := by
      rw [one_smul]
      exact hg
    have hginv : ((g⁻¹ : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) ((1, 0), 0) =
          (1 : F) • ((1, 0), 0) := by
      rw [one_smul]
      exact (LinearEquiv.symm_apply_eq _).mpr hg.symm
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    constructor
    · intro hh
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        conj_mem_rootGroup_of_apply_eq_smul (hO g) hg' hh
    · intro hh
      simpa [mul_assoc] using conj_mem_rootGroup_of_apply_eq_smul (hO g⁻¹) hginv hh

theorem exists_twoSubgroup_normalized_normPlaneTorus {m p : ℕ} (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) (χ : Multiplicative (ZMod p) →* Kˣ) :
    ∃ U : Subgroup (normOmega E m), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ t, normPlaneTorus E hm hpq χ t ∈ Subgroup.normalizer (U : Set (normOmega E m)) := by
  obtain ⟨U, hU1, hU2, hUN⟩ := exists_twoSubgroup_normalized_of_apply_eq E hm
  refine ⟨U, hU1, hU2, fun t => hUN _ ?_⟩
  rw [normPlaneTorus_apply]
  exact Prod.ext rfl (funext fun _ => mul_zero _)

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
