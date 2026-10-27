module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF4

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)

section AEmpty


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ : Y}

theorem coreAt_subgroupOf_mem_fFam (b : Y) (K : Subgroup Y) :
    (coreAt b K).subgroupOf (Subgroup.centralizer ({b} : Set Y)) ∈ fFam b K :=
  ⟨coreAt b K, ⟨1, Subgroup.one_mem _, by rw [conjSub_eq_self_of_mem (Subgroup.one_mem K)]⟩,
    TwinADescent.coreAt_le_centralizer b K, rfl⟩

theorem omegaStarNbr_fFam_subset (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂)
    (h11 : (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) =
      Subgroup.zpowers t) {b : Y} (hbS : b ∈ (S₁ : Subgroup Y)) (hb2 : b * b = 1)
    (hF₁ : IsFAut R₁ b) :
    omegaStarNbr (fFam b (tightCore R))
        ((coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y))) ⊆
      omegaNbr (fFam b (tightCore R))
        ((coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y))) := by
  classical
  have hbase := fBase_of_isFAut hr hP hyp hbS hF₁
  have hΛ := hbase.hypOmegaGen_fFam
  have hM₀ := coreAt_subgroupOf_mem_fFam b (tightCore R)
  have htC : t ∈ Subgroup.centralizer ({b} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hbase.comm
  rintro N ⟨hNΛ, hNne, U, hU, hUN, hUnorm⟩
  have hNΛ' := hNΛ
  obtain ⟨L, ⟨c, hc, rfl⟩, hLC, hNeq⟩ := hNΛ'
  subst hNeq
  obtain ⟨hJ, hz, hzm⟩ := hbase.memberData hc
  have hzN : IsUniqueInvolution (coreAt b (conjSub c (tightCore R))) (c * t * c⁻¹) :=
    isUniqueInvolution_mono hz (TwinADescent.coreAt_le_left b _) hzm
  have hzC : c * t * c⁻¹ ∈ Subgroup.centralizer ({b} : Set Y) :=
    TwinADescent.coreAt_le_centralizer b _ hzm
  have hzN' : IsUniqueInvolution ((coreAt b (conjSub c (tightCore R))).subgroupOf
      (Subgroup.centralizer ({b} : Set Y))) (⟨c * t * c⁻¹, hzC⟩ : Subgroup.centralizer ({b} : Set Y)) :=
    isUniqueInvolution_subgroupOf hzN (TwinADescent.coreAt_le_centralizer b _)
  obtain ⟨R', -, J, hJΛ, hR'J, hUR', -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΛ hU
  have hU2 : IsPGroup 2 ↥U := Sec6Gen.isPGroup_of_mem_USet hΛ hU
  have hzNU : (⟨c * t * c⁻¹, hzC⟩ : Subgroup.centralizer ({b} : Set Y)) ∈ U :=
    hzN'.mem_of_le hUN hU2 (by omega)
  have hznorm : c * t * c⁻¹ ∈ Subgroup.normalizer
      ((coreAt b (tightCore R) : Subgroup Y) : Set Y) :=
    (mem_normalizer_subgroupOf_iff (TwinADescent.coreAt_le_centralizer b (tightCore R))
      (y := ⟨c * t * c⁻¹, hzC⟩)).mpr (hUnorm hzNU)
  by_cases hzt : c * t * c⁻¹ = t
  · have hzK₀ : IsUniqueInvolution ((coreAt b (tightCore R)).subgroupOf
        (Subgroup.centralizer ({b} : Set Y))) (⟨t, htC⟩ : Subgroup.centralizer ({b} : Set Y)) :=
      isUniqueInvolution_subgroupOf hbase.inv_core (TwinADescent.coreAt_le_centralizer b _)
    have hzeq : (⟨c * t * c⁻¹, hzC⟩ : Subgroup.centralizer ({b} : Set Y)) = ⟨t, htC⟩ :=
      Subtype.ext hzt
    rw [hzeq] at hzN'
    exact Q3CL.T3.twin_mem_omegaNbr hΛ hM₀ hNΛ hNne hzK₀ hzN'
  · exact (false_of_normalizes_fcore hr hP hyp h11 hbS hb2 hF₁ hzC hz.sq hzt ⟨c, rfl⟩ hznorm).elim

theorem aEmpty_fFam (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂)
    (h11 : (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) =
      Subgroup.zpowers t) {b : Y} (hbS : b ∈ (S₁ : Subgroup Y)) (hb2 : b * b = 1)
    (hF₁ : IsFAut R₁ b) :
    ∀ M ∈ fFam b (tightCore R), AEmpty (fFam b (tightCore R)) M := by
  have hbase := fBase_of_isFAut hr hP hyp hbS hF₁
  have hΛ := hbase.hypOmegaGen_fFam
  have hA₀ : AEmpty (fFam b (tightCore R))
      ((coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y))) := by
    intro J hJ hJn zK zJ hzK hzJ
    exact absurd (omegaStarNbr_fFam_subset hr hP hyp h11 hbS hb2 hF₁ hJ) hJn
  rintro M ⟨L, ⟨c, hc, rfl⟩, hLC, rfl⟩
  have e : (coreAt b (conjSub c (tightCore R))).subgroupOf (Subgroup.centralizer ({b} : Set Y)) =
      conjSub (⟨c, hc⟩ : Subgroup.centralizer ({b} : Set Y))
        ((coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y))) := by
    rw [Generic.conjSub_subgroupOf, TwinADescent.conjSub_coreAt hc]
  rw [e]
  exact aEmpty_conj hΛ.conjInvariant hA₀ _

end AEmpty

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
