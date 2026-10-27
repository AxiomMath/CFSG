module

public import CFSG.ClassicalInvolution.Phan.StandardPair

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

private theorem embPair_rot_commutator_ne {F : Type*} [Field F] :
    (embPair 2 (rotMat : Matrix (Fin 2) (Fin 2) F) * embPair 0 rotMat *
        embPair 2 rotMatInv * embPair 0 rotMatInv) * embPair 0 rotMat ≠
      embPair 0 rotMat * (embPair 2 rotMat * embPair 0 rotMat *
        embPair 2 rotMatInv * embPair 0 rotMatInv) := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [embPair, rotMat, rotMatInv, Matrix.mul_apply, Fin.sum_univ_three] at h01

private theorem coe_rotSU_inv {F : Type*} [Field F] (σ : F ≃+* F) :
    ((((rotSU σ)⁻¹ : SUid σ 2) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = rotMatInv := rfl

private theorem rotSU_commutator_not_commute {F : Type*} [Field F] (σ : F ≃+* F) :
    (embSUid σ 2 (rotSU σ) * embSUid σ 0 (rotSU σ) * (embSUid σ 2 (rotSU σ))⁻¹ *
        (embSUid σ 0 (rotSU σ))⁻¹) * embSUid σ 0 (rotSU σ) ≠
      embSUid σ 0 (rotSU σ) * (embSUid σ 2 (rotSU σ) * embSUid σ 0 (rotSU σ) *
        (embSUid σ 2 (rotSU σ))⁻¹ * (embSUid σ 0 (rotSU σ))⁻¹) := by
  intro h
  have h'' : (embSUid σ 2 (rotSU σ) * embSUid σ 0 (rotSU σ) *
        embSUid σ 2 ((rotSU σ)⁻¹) * embSUid σ 0 ((rotSU σ)⁻¹)) * embSUid σ 0 (rotSU σ) =
      embSUid σ 0 (rotSU σ) * (embSUid σ 2 (rotSU σ) * embSUid σ 0 (rotSU σ) *
        embSUid σ 2 ((rotSU σ)⁻¹) * embSUid σ 0 ((rotSU σ)⁻¹)) := by
    simpa only [map_inv] using h
  have h' := congrArg (fun g : SUid σ 3 =>
    (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))) h''
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, coe_rotSU_inv] at h'
  exact embPair_rot_commutator_ne h'

theorem UnitaryBlockStandardPair.exists_not_commute {X : Type} [Group X] {W U V : Subgroup X}
    (h : UnitaryBlockStandardPair K p f W U V) : ∃ x ∈ U, ∃ y ∈ V, x * y ≠ y * x := by
  obtain ⟨θ, -, hker, hU, hV⟩ := pair_normalize h
  refine ⟨θ (embSUid (unitaryInvolution K p f) 2 (rotSU (unitaryInvolution K p f))), ?_,
    θ (embSUid (unitaryInvolution K p f) 0 (rotSU (unitaryInvolution K p f))), ?_, ?_⟩
  · rw [← hU]
    exact Subgroup.mem_map_of_mem θ ⟨rotSU (unitaryInvolution K p f), rfl⟩
  · rw [← hV]
    exact Subgroup.mem_map_of_mem θ ⟨rotSU (unitaryInvolution K p f), rfl⟩
  · intro hxy
    have hc : embSUid (unitaryInvolution K p f) 2 (rotSU (unitaryInvolution K p f)) *
          embSUid (unitaryInvolution K p f) 0 (rotSU (unitaryInvolution K p f)) *
          (embSUid (unitaryInvolution K p f) 2 (rotSU (unitaryInvolution K p f)))⁻¹ *
          (embSUid (unitaryInvolution K p f) 0 (rotSU (unitaryInvolution K p f)))⁻¹ ∈
        θ.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hxy]
      group
    exact rotSU_commutator_not_commute (unitaryInvolution K p f) (Subgroup.mem_center_iff.mp
      (hker hc) (embSUid (unitaryInvolution K p f) 0 (rotSU (unitaryInvolution K p f)))).symm

end CFSG.ClassicalInvolution.Phan

end
