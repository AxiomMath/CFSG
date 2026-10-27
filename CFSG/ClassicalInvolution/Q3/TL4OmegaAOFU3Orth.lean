module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFU4Bur

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.U3

open Matrix CFSG.ClassicalInvolution.Q3.Q3MFOU4 CFSG.ClassicalInvolution.Q3.Q3PP
  CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalInvolution.Balance CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Q3.TL4.U4 (ufd9 map_bar_eq map_barEq_eq conj_injective_stated)
open scoped MatrixGroups

section Centre

theorem mem_center_of_scalar_three {z : Su F9 3 1 3} {c : F9}
    (hz : suMat z = c • (1 : Matrix (Fin 3) (Fin 3) F9)) :
    z ∈ Subgroup.center (Su F9 3 1 3) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply suMat_injective
  rw [suMat_mul, suMat_mul, hz, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem scalar_of_mem_center_three {z : Su F9 3 1 3} (hz : z ∈ Subgroup.center (Su F9 3 1 3)) :
    ∃ u : F9, u ≠ 0 ∧ suMat z = u • (1 : Matrix (Fin 3) (Fin 3) F9) := by
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center isUnitaryInvolution_σ9 (by norm_num : 3 ≤ 3) hz
  refine ⟨u, u.ne_zero, ?_⟩
  show ((z : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) = _
  rw [hu, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

end Centre

section Model

@[expose] noncomputable def suStated : Su F9 3 1 3 ≃* StatedSU 3 (3 ^ 1) F9 :=
  MulEquiv.subgroupCongr (SUid_eq_statedSU card_F9 3)

theorem map_center_suStated :
    (Subgroup.center (Su F9 3 1 3)).map (suStated : Su F9 3 1 3 →* StatedSU 3 (3 ^ 1) F9) =
      (StatedScalars (Fin 3) F9).subgroupOf (StatedSU 3 (3 ^ 1) F9) := by
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨u, hu0, hu⟩ := scalar_of_mem_center_three hz
    rw [Subgroup.mem_subgroupOf]
    refine ⟨Units.mk0 u hu0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    exact hu.symm
  · intro hg
    rw [Subgroup.mem_subgroupOf] at hg
    obtain ⟨c, hc⟩ := hg
    refine ⟨suStated.symm g, mem_center_of_scalar_three (c := (c : F9)) ?_,
      suStated.apply_symm_apply g⟩
    show ((g : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) = _
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]

@[expose] noncomputable def psuStated :
    Su F9 3 1 3 ⧸ Subgroup.center (Su F9 3 1 3) ≃* StatedProj (StatedSU 3 (3 ^ 1) F9) :=
  QuotientGroup.congr _ _ suStated map_center_suStated

theorem psuStated_mk (x : Su F9 3 1 3) :
    psuStated (QuotientGroup.mk x) = projH _ (suStated x) := rfl

@[expose] noncomputable def uOf {G Gi : Matrix (Fin 3) (Fin 3) F9} (hGiG : Gi * G = 1)
    (hgu : (G.map σ9)ᵀ * G = 1) : uU ufd9 3 :=
  ⟨⟨G, Gi, mul_eq_one_comm.mp hGiG, hGiG⟩, (mem_uU ufd9).2 (by
    show (G.map ufd9.bar)ᵀ * G = 1
    rw [map_bar_eq]
    exact hgu)⟩

theorem congr_psuStated (ρ : MulAut (Su F9 3 1 3 ⧸ Subgroup.center (Su F9 3 1 3)))
    (α : Su F9 3 1 3 →* Su F9 3 1 3)
    (hρmk : ∀ x : Su F9 3 1 3, ρ (QuotientGroup.mk x) = QuotientGroup.mk (α x))
    (A : uU ufd9 3) (φ : F9 ≃+* F9)
    (hα : ∀ x, suMat (α x) = ((A : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) * (suMat x).map φ *
      (((A : GL (Fin 3) F9)⁻¹ : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9)) :
    MulAut.congr psuStated ρ = uConjAut ufd9 (by norm_num) A * uFieldAut ufd9 (by norm_num) φ := by
  ext y
  obtain ⟨x, rfl⟩ := (psuStated.surjective.comp QuotientGroup.mk_surjective) y
  rw [Function.comp_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, hρmk, psuStated_mk, psuStated_mk, uLift_proj]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [coe_uLift]
  exact hα x

theorem oddCoreIn_fixed_of_psuStated (ρ : MulAut (Su F9 3 1 3 ⧸ Subgroup.center (Su F9 3 1 3)))
    (h : oddCoreIn (fixedSubgroup (MulAut.congr psuStated ρ)) = ⊥) :
    oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  have h1 := Q3NM.oddCoreIn_fixed_congr_eq_bot' psuStated.symm _ h
  have h2 : MulAut.congr psuStated.symm (MulAut.congr psuStated ρ) = ρ := by
    ext x
    simp [MulAut.congr_apply]
  rwa [h2] at h1

end Model

section Orth

theorem oddCoreIn_fixed_orth (ρ : MulAut (Su F9 3 1 3 ⧸ Subgroup.center (Su F9 3 1 3)))
    (α : Su F9 3 1 3 →* Su F9 3 1 3)
    (hρmk : ∀ x : Su F9 3 1 3, ρ (QuotientGroup.mk x) = QuotientGroup.mk (α x))
    {G Gi : Matrix (Fin 3) (Fin 3) F9} (hGiG : Gi * G = 1)
    (hα : ∀ x, suMat (α x) = G * σ9.mapMatrix (suMat x) * Gi) (hgu : (G.map σ9)ᵀ * G = 1)
    (hGG : G * G.map σ9 = 1) : oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  have hA := congr_psuStated ρ α hρmk (uOf hGiG hgu) (barEq ufd9) fun x => by
    rw [hα x, RingEquiv.mapMatrix_apply, ← map_barEq_eq]
    rfl
  have hinj := conj_injective_stated (by norm_num : 3 ≤ 3)
  have hAc : (((uOf hGiG hgu : uU ufd9 3) : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) *
      (((uOf hGiG hgu : uU ufd9 3) : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9).map ufd9.bar =
        (1 : F9) • 1 := by
    show G * G.map ufd9.bar = (1 : F9) • 1
    rw [map_bar_eq, hGG, one_smul]
  have key := TL4.oddCoreIn_fixed_eq_bot_of_inn hinj _
    (graph_oddCoreIn_eq_bot ufd9 (by norm_num) (by norm_num) hinj le_rfl hAc)
  rw [← hA] at key
  exact oddCoreIn_fixed_of_psuStated ρ key

end Orth

end CFSG.ClassicalInvolution.Q3.TL4.U3
