module

public import Certificates.Certificate12622
public import Certificates.Certificate12638
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSpor
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier CFSG.CosetTable
  CFSG.Blueprint CFSG.RankThree.PartTwo.Sec21


theorem j3tG_valid : validA 6156 j3tG = true := by
  have h := j3t_derived_check.2.2.2.2
  simp only [detOK, Bool.and_eq_true] at h
  exact h.1.1.1

theorem j3P_involution_inverting :
    ∃ τ ∈ j3P, τ ^ 2 = 1 ∧ τ * j3tXA * τ⁻¹ = j3tXA ^ 2 := by
  have hRG : Rep 6156 j3tG j3tGPerm := rep_of_validA j3tG_valid
  have hRX : Rep 6156 j3tReps[0]! j3tXA := rep_of_validA (j3tReps_spec (c := 0) (by norm_num)).1
  have hD : validA 6156 j3tDGens[0]! = true := j3tDGens_valid 0 (by simp [j3tDGens])
  have hRD : Rep 6156 j3tDGens[0]! (j3tD 0) := rep_of_validA hD
  have hc := Certificates.certificate12622
  have hcomm := (allLt_spec Certificates.certificate12638 (show 0 < 2 by norm_num))
  have e1 : j3tGPerm * j3tXA = (j3tXA * j3tXA) * j3tGPerm :=
    (eqA_iff (rep_compA hRG hRX) (rep_compA (rep_compA hRX hRX) hRG)).1 hc.1
  have e2 : (j3tGPerm * j3tD 0) * (j3tGPerm * j3tD 0) = 1 :=
    (eqA_iff (rep_compA (rep_compA hRG hRD) (rep_compA hRG hRD)) rep_idA).1 hc.2
  have e3 : j3tXA * j3tD 0 = j3tD 0 * j3tXA :=
    (eqA_iff (rep_compA hRX hRD) (rep_compA hRD hRX)).1 hcomm
  refine ⟨j3tGPerm * j3tD 0, Subgroup.mul_mem _ j3tGPerm_mem (j3tD_mem 0), ?_, ?_⟩
  · rw [pow_two]; exact e2
  · have h1 : j3tXA * j3tD 0 * (j3tD 0)⁻¹ = j3tXA := mul_inv_cancel_right _ _
    calc j3tGPerm * j3tD 0 * j3tXA * (j3tGPerm * j3tD 0)⁻¹
        = j3tGPerm * (j3tD 0 * j3tXA * (j3tD 0)⁻¹) * j3tGPerm⁻¹ := by group
      _ = j3tGPerm * (j3tXA * j3tD 0 * (j3tD 0)⁻¹) * j3tGPerm⁻¹ := by rw [← e3]
      _ = j3tGPerm * j3tXA * j3tGPerm⁻¹ := by rw [h1]
      _ = (j3tXA * j3tXA) * j3tGPerm * j3tGPerm⁻¹ := by rw [e1]
      _ = j3tXA ^ 2 := by rw [pow_two]; group

theorem exists_involution_inverting {Q : Type*} [Group Q] (e : Q ≃* NativeSporadic.J3) {x : Q}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hC : Nat.card (centralizer ({x} : Set Q)) = 1080) :
    ∃ τ : Q, τ ^ 2 = 1 ∧ τ * x * τ⁻¹ = x⁻¹ := by
  set ψ : Q ≃* ↥j3P := e.trans Item228CensusProof.j3CarrierEquiv with hψ
  have hcard2 := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv ψ x
  obtain ⟨y, hyy⟩ : ∃ y : Equiv.Perm (Fin 6156), y = (ψ x : Equiv.Perm (Fin 6156)) := ⟨_, rfl⟩
  have hyj : y ∈ j3P := hyy ▸ (ψ x).2
  have hy3 : orderOf y = 3 := by
    have h3 : y ^ 3 = 1 := by
      have := congrArg (fun z : ↥j3P => (z : Equiv.Perm (Fin 6156)))
        (show ψ x ^ 3 = 1 from
          (map_pow ψ x 3).symm.trans ((congrArg ψ hx3).trans (map_one _)))
      rw [hyy]
      simpa using this
    have h1 : y ≠ 1 := by
      intro h
      apply hx1
      have : ψ x = 1 := Subtype.ext (hyy ▸ h)
      exact (map_eq_one_iff _ ψ.injective).1 this
    exact orderOf_eq_prime h3 h1
  obtain ⟨k0, hk0, c, hc, e', he', hyeq⟩ := j3t_fusion hyj hy3
  rcases hc with rfl | rfl
  · obtain ⟨τ0, hτ0, hτ02, hτ0x⟩ := j3P_involution_inverting
    have hA3 : j3tXA ^ 3 = 1 := (j3tReps_spec (c := 0) (by norm_num)).2
    refine ⟨ψ.symm ⟨k0 * τ0 * k0⁻¹, ?_⟩, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk0 hτ0) (Subgroup.inv_mem _ hk0)
    · apply ψ.injective
      rw [map_pow, MulEquiv.apply_symm_apply, map_one]
      apply Subtype.ext
      show (k0 * τ0 * k0⁻¹) ^ 2 = 1
      rw [conj_pow, hτ02]
      group
    · apply ψ.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hyy]
      have hτpow : τ0 * j3tXA ^ e' * τ0⁻¹ = (j3tXA ^ e') ^ 2 := by
        have : τ0 * j3tXA ^ e' * τ0⁻¹ = (τ0 * j3tXA * τ0⁻¹) ^ e' := by
          rw [← conj_pow]
        rw [this, hτ0x, ← pow_mul, ← pow_mul, mul_comm]
      have hinv : ((j3tXA ^ e') ^ 2) = (j3tXA ^ e')⁻¹ := by
        have h3 : (j3tXA ^ e') ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hA3, one_pow]
        rw [eq_inv_iff_mul_eq_one, ← pow_succ]
        exact h3
      rw [hyeq]
      calc k0 * τ0 * k0⁻¹ * (k0 * j3tXA ^ e' * k0⁻¹) * (k0 * τ0 * k0⁻¹)⁻¹
          = k0 * (τ0 * j3tXA ^ e' * τ0⁻¹) * k0⁻¹ := by group
        _ = k0 * (j3tXA ^ e')⁻¹ * k0⁻¹ := by rw [hτpow, hinv]
        _ = (k0 * j3tXA ^ e' * k0⁻¹)⁻¹ := by group
  · exfalso
    have hB3 : j3tXB ^ 3 = 1 := (j3tReps_spec (c := 1) (by norm_num)).2
    have hcard : Nat.card (centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156))) = 243 := by
      rw [hyeq, CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_conj hk0 hB3 he',
        ← j3t_caseB.1, j3t_caseB.2]
    rw [hcard2, ← hyy, hcard] at hC
    omega

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
