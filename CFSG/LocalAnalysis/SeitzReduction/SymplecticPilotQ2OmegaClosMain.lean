module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaSiegInputs
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaClosRad

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)

variable {K : Type} [Field K] {N j : ℕ}

section Explicit

theorem spARepMat_one_eq (hN : 2 ≤ N) {i0 : Fin N} (hi0 : i0.val = 0) :
    (spARepMat N 1 : Matrix (Fin N) (Fin N) K) =
      vecMulVec (Pi.single i0 1) (Pi.single (spAPar i0) 1) +
        vecMulVec (Pi.single (spAPar i0) 1) (Pi.single i0 1) := by
  obtain rfl : i0 = ⟨0, Nat.lt_of_lt_of_le two_pos hN⟩ := Fin.ext hi0
  have hp0 : spAPar (⟨0, by omega⟩ : Fin N) = ⟨1, by omega⟩ := by
    apply Fin.ext
    rw [spAPar_val (j := 1) (by omega) (by simp)]
    simp
  have hp1 : spAPar (⟨1, by omega⟩ : Fin N) = ⟨0, by omega⟩ := by
    apply Fin.ext
    rw [spAPar_val (j := 1) (by omega) (by simp)]
    simp
  rw [hp0]
  ext m l
  rw [spARepMat_apply (j := 1) (by omega), Matrix.add_apply, vecMulVec_apply, vecMulVec_apply]
  simp only [Pi.single_apply]
  rcases Nat.lt_or_ge l.val 2 with hl | hl
  · rcases Nat.lt_or_ge l.val 1 with hl1 | hl1
    · have e : l = ⟨0, by omega⟩ := Fin.ext (show l.val = 0 by omega)
      rw [e, hp0]
      simp [Fin.ext_iff]
    · have e : l = ⟨1, by omega⟩ := Fin.ext (show l.val = 1 by omega)
      rw [e, hp1]
      simp [Fin.ext_iff]
  · have h1 : l ≠ ⟨0, by omega⟩ := fun h => by rw [h] at hl; simp at hl
    have h2 : l ≠ ⟨1, by omega⟩ := fun h => by rw [h] at hl; simp at hl
    rw [ite_eq_right (fun h => by omega), ite_eq_right h1, ite_eq_right h2, mul_zero, mul_zero,
      add_zero]

variable [CharP K 2]

omit [CharP K 2] in
theorem lagSqZero_conj_spARepMat {x y : Fin N → K}
    (hy : ((spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ y) ⬝ᵥ y = 0) :
    (1 + vecMulVec x y) * (spARepMat N j : Matrix (Fin N) (Fin N) K) *
        (1 + vecMulVec x y)ᵀ =
      spARepMat N j + (vecMulVec x ((spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ y) +
        vecMulVec ((spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ y) x) := by
  rw [lagSqZero_conj _ _ (spARepMat_transpose N j), hy, zero_smul, add_zero]

end Explicit

theorem spTwoLagClosureInput_holds : SpTwoLagClosureInput := by
  intro N j K _ _ _ hK hj3 hjN H _ Φ₁ Φ₂ h₁ h₂ ha hC
  have haC : spARep N j ∈ centralizer ({spARep N j} : Set (StatedSp N K)) :=
    mem_centralizer_singleton_iff.2 rfl
  let e₁ := Subgroup.equivMapOfInjective (centralizer ({spARep N j} : Set (StatedSp N K))) Φ₁ h₁
  let e₂ := Subgroup.equivMapOfInjective (centralizer ({spARep N j} : Set (StatedSp N K))) Φ₂ h₂
  let ψ := e₂.trans ((MulEquiv.subgroupCongr hC.symm).trans e₁.symm)
  have hψ : ∀ g : centralizer ({spARep N j} : Set (StatedSp N K)),
      Φ₁ (ψ g : StatedSp N K) = Φ₂ (g : StatedSp N K) := by
    intro g
    have h1 : ((e₁ (ψ g) : _) : H) = Φ₁ (ψ g : StatedSp N K) :=
      Subgroup.coe_equivMapOfInjective_apply _ _ _ _
    have h2 : e₁ (ψ g) = MulEquiv.subgroupCongr hC.symm (e₂ g) := e₁.apply_symm_apply _
    rw [← h1, h2]
    rfl
  have hψa : ψ ⟨spARep N j, haC⟩ = ⟨spARep N j, haC⟩ :=
    Subtype.ext (h₁ ((hψ _).trans ha.symm))
  obtain ⟨s, hs⟩ := exists_spLagProj_map_eq_conj hjN hK hj3 ψ
  set ι := spLagIncl (K := K) hjN s with hι
  let θ := ψ.trans (MulAut.conj ι⁻¹)
  have hθ : ∀ g, θ g = ι⁻¹ * ψ g * ι := fun g => by
    show MulAut.conj ι⁻¹ (ψ g) = _
    rw [MulAut.conj_apply, inv_inv]
  have hθπ : ∀ g, spLagProj hjN (θ g) = spLagProj hjN g := by
    intro g
    rw [hθ, map_mul, map_mul, map_inv, hs, hι, spLagProj_spLagIncl]
    group
  have hιa : ι * ⟨spARep N j, haC⟩ = ⟨spARep N j, haC⟩ * ι :=
    Subtype.ext (mem_centralizer_singleton_iff.1 ι.2)
  have hθa : θ ⟨spARep N j, haC⟩ = ⟨spARep N j, haC⟩ := by
    rw [hθ, hψa, mul_assoc, ← hιa, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin N, i0.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i2, hi2⟩ : ∃ i2 : Fin N, i2.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  have hp0 : (spAPar i0).val = 1 := by
    rw [spAPar_val hjN.le (by omega), hi0]
    rfl
  have hi01 : i0 ≠ spAPar i0 := (spAPar_ne_lag hjN i0).symm
  have hi02 : i0 ≠ i2 := fun h => by have := congrArg Fin.val h; omega
  have hi12 : spAPar i0 ≠ i2 := fun h => by have := congrArg Fin.val h; omega
  have hp02 : spAPar i2 ≠ spAPar i0 := fun h =>
    hi02 (by rw [← spAPar_spAPar_lag hjN i0, ← h, spAPar_spAPar_lag hjN])
  have he0 : (Pi.single i0 (1 : K) : Fin N → K) (spAPar i0) = 0 :=
    Pi.single_eq_of_ne (Ne.symm hi01) 1
  have he2 : (Pi.single i2 (1 : K) : Fin N → K) (spAPar i0) = 0 := Pi.single_eq_of_ne hi12 1
  have hR₀t : (vecMulVec (Pi.single i0 (1 : K)) (Pi.single i2 1) +
      vecMulVec (Pi.single i2 1) (Pi.single i0 1))ᵀ =
      vecMulVec (Pi.single i0 (1 : K)) (Pi.single i2 1) +
        vecMulVec (Pi.single i2 1) (Pi.single i0 1) := by
    rw [transpose_add, transpose_vecMulVec, transpose_vecMulVec, add_comm]
  have hθR := lagTheta_upperUnipotentSp_plane θ hjN hθπ hK hθa i0 he0 he2 hR₀t
  have hSR : (spARepMat N j + (vecMulVec (Pi.single i0 (1 : K)) (Pi.single i2 1) +
      vecMulVec (Pi.single i2 1) (Pi.single i0 1)))ᵀ =
      spARepMat N j + (vecMulVec (Pi.single i0 (1 : K)) (Pi.single i2 1) +
        vecMulVec (Pi.single i2 1) (Pi.single i0 1)) := by
    rw [transpose_add, spARepMat_transpose, hR₀t]
  have hu : spARep N j * upperUnipotentSp N K hR₀t = upperUnipotentSp N K hSR :=
    upperUnipotentSp_mul (spARepMat_transpose N j) hR₀t
  have huC := upperUnipotentSp_mem_centralizer_spARep (j := j) hSR
  have hθu : θ ⟨upperUnipotentSp N K hSR, huC⟩ = ⟨upperUnipotentSp N K hSR, huC⟩ := by
    have e : (⟨upperUnipotentSp N K hSR, huC⟩ : centralizer ({spARep N j} : Set (StatedSp N K))) =
        ⟨spARep N j, haC⟩ *
          ⟨upperUnipotentSp N K hR₀t, upperUnipotentSp_mem_centralizer_spARep hR₀t⟩ :=
      Subtype.ext hu.symm
    rw [e, map_mul, hθa, hθR]
  have hψu : ψ ⟨upperUnipotentSp N K hSR, huC⟩ = ι * ⟨upperUnipotentSp N K hSR, huC⟩ * ι⁻¹ := by
    have h := hθ ⟨upperUnipotentSp N K hSR, huC⟩
    rw [hθu] at h
    calc ψ _ = ι * (ι⁻¹ * ψ ⟨upperUnipotentSp N K hSR, huC⟩ * ι) * ι⁻¹ := by group
      _ = _ := by rw [← h]
  have h21 : (Pi.single (spAPar i0) (1 : K) : Fin N → K) ⬝ᵥ Pi.single i2 1 = 0 := by
    rw [dotProduct_single_one]
    exact Pi.single_eq_of_ne (Ne.symm hi12) 1
  have hSe1 : (spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ Pi.single (spAPar i0) 1 =
      Pi.single i0 1 := by
    rw [spARepMat_mulVec_single_lag hjN, spAPar_spAPar_lag hjN]
  have hPS : ((lagSqZeroUnit (Pi.single i2 1) (Pi.single (spAPar i0) 1) h21 : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) * spARepMat N j *
        ((lagSqZeroUnit (Pi.single i2 1) (Pi.single (spAPar i0) 1) h21 : GL (Fin N) K) :
          Matrix (Fin N) (Fin N) K)ᵀ =
      spARepMat N j + (vecMulVec (Pi.single i0 (1 : K)) (Pi.single i2 1) +
        vecMulVec (Pi.single i2 1) (Pi.single i0 1)) := by
    rw [coe_lagSqZeroUnit,
      lagSqZero_conj_spARepMat (by rw [hSe1, dotProduct_single_one]; exact he0),
      hSe1, add_comm (vecMulVec (Pi.single i2 1) _)]
  have hca : leviEmbedGL K N (lagSqZeroUnit (Pi.single i2 1) (Pi.single (spAPar i0) 1) h21) *
      spARep N j *
        (leviEmbedGL K N (lagSqZeroUnit (Pi.single i2 1) (Pi.single (spAPar i0) 1) h21))⁻¹ =
      upperUnipotentSp N K hSR := by
    rw [spARep, leviEmbedGL_conj_upperUnipotentSp]
    exact upperUnipotentSp_congr _ _ hPS
  have h12 : (Pi.single i2 (1 : K) : Fin N → K) ⬝ᵥ Pi.single (spAPar i0) 1 = 0 := by
    rw [dotProduct_single_one]
    exact he2
  set Q : GL (Fin N) K := lagSqZeroUnit (Pi.single (spAPar i0) 1) (Pi.single i2 1) h12 *
    lagSqZeroUnit (Pi.single i2 1) (Pi.single (spAPar i0) 1) h21 with hQ
  have hQv : ∀ v : Fin N → K, (Q : Matrix (Fin N) (Fin N) K) *ᵥ v =
      (1 + vecMulVec (Pi.single (spAPar i0) 1) (Pi.single i2 1)) *ᵥ
        ((1 + vecMulVec (Pi.single i2 1) (Pi.single (spAPar i0) 1)) *ᵥ v) := by
    intro v
    rw [hQ, Units.val_mul, coe_lagSqZeroUnit, coe_lagSqZeroUnit, ← Matrix.mulVec_mulVec]
  have hQ0 : (Q : Matrix (Fin N) (Fin N) K) *ᵥ Pi.single i0 1 = Pi.single i0 1 := by
    have hin : (1 + vecMulVec (Pi.single i2 1) (Pi.single (spAPar i0) 1)) *ᵥ Pi.single i0 1 =
        (Pi.single i0 1 : Fin N → K) := by
      rw [lagSqZero_mulVec, dotProduct_single_one, Pi.single_eq_of_ne hi01 1, zero_smul, add_zero]
    have hout : (1 + vecMulVec (Pi.single (spAPar i0) 1) (Pi.single i2 1)) *ᵥ Pi.single i0 1 =
        (Pi.single i0 1 : Fin N → K) := by
      rw [lagSqZero_mulVec, dotProduct_single_one, Pi.single_eq_of_ne hi02 1, zero_smul, add_zero]
    rw [hQv, hin, hout]
  have hQ1 : (Q : Matrix (Fin N) (Fin N) K) *ᵥ Pi.single (spAPar i0) 1 = Pi.single i2 1 := by
    have hin : (1 + vecMulVec (Pi.single i2 1) (Pi.single (spAPar i0) 1)) *ᵥ
        Pi.single (spAPar i0) 1 = (Pi.single (spAPar i0) 1 + Pi.single i2 1 : Fin N → K) := by
      rw [lagSqZero_mulVec, dotProduct_single_one, Pi.single_eq_same, one_smul]
    have hout : (1 + vecMulVec (Pi.single (spAPar i0) 1) (Pi.single i2 1)) *ᵥ
        (Pi.single (spAPar i0) 1 + Pi.single i2 1) = (Pi.single i2 1 : Fin N → K) := by
      rw [lagSqZero_mulVec, dotProduct_add, dotProduct_single_one, dotProduct_single_one, he2,
        Pi.single_eq_same, zero_add, one_smul, add_comm (Pi.single (spAPar i0) 1), add_assoc,
        lagVec_add_self, add_zero]
    rw [hQv, hin, hout]
  have hQC : (Q : Matrix (Fin N) (Fin N) K) * spARepMat N 1 * (Q : Matrix (Fin N) (Fin N) K)ᵀ =
      vecMulVec (Pi.single i0 (1 : K)) (Pi.single i2 1) +
        vecMulVec (Pi.single i2 1) (Pi.single i0 1) := by
    rw [spARepMat_one_eq (by omega) hi0, Matrix.mul_add, Matrix.add_mul,
      mul_vecMulVec_mul_transpose_lag, mul_vecMulVec_mul_transpose_lag, hQ0, hQ1]
  have hda : leviEmbedGL K N Q * spARep N 1 * (leviEmbedGL K N Q)⁻¹ =
      upperUnipotentSp N K hR₀t := by
    rw [spARep, leviEmbedGL_conj_upperUnipotentSp]
    exact upperUnipotentSp_congr _ _ hQC
  refine ⟨leviEmbedGL K N (lagSqZeroUnit (Pi.single i2 1) (Pi.single (spAPar i0) 1) h21),
    (ι : StatedSp N K) * leviEmbedGL K N Q,
    ⟨leviEmbedGL K N (lagTvUnit hjN (Pi.single (spAPar i0) 1)),
      leviEmbedGL_mem_centralizer_spARep (lagTv_conj_spARepMat hjN _), ?_⟩, ?_⟩
  ·
    intro hmem
    set c := leviEmbedGL K N (lagSqZeroUnit (Pi.single i2 1) (Pi.single (spAPar i0) 1) h21) with hc
    set y := leviEmbedGL K N (lagTvUnit hjN (Pi.single (spAPar i0) (1 : K))) with hy
    have hcinv : c⁻¹ = c := by rw [hc, ← map_inv, lagSqZeroUnit_inv]
    have h1 : Commute (c * y * c⁻¹) (spARep N j) := mem_centralizer_singleton_iff.1 hmem
    have h2 : Commute y (c⁻¹ * spARep N j * c) := by
      rw [← Commute.conj_iff c]
      have e : c * (c⁻¹ * spARep N j * c) * c⁻¹ = spARep N j := by group
      rw [e]
      exact h1
    have h3 : c⁻¹ * spARep N j * c = upperUnipotentSp N K hSR := by
      rw [← hca, hcinv]
    rw [h3] at h2
    have h4 : y * upperUnipotentSp N K hSR * y⁻¹ = upperUnipotentSp N K hSR := by
      rw [h2.eq, mul_inv_cancel_right]
    rw [hy, leviEmbedGL_conj_upperUnipotentSp] at h4
    have h5 := upperUnipotentSp_inj_lag _ _ h4
    rw [coe_lagTvUnit, Matrix.mul_add, Matrix.add_mul, lagTv_conj_spARepMat hjN, Matrix.mul_add,
      Matrix.add_mul, mul_vecMulVec_mul_transpose_lag, mul_vecMulVec_mul_transpose_lag,
      lagTvMat_mulVec_single hjN, lagTvMat_mulVec_single hjN, Pi.single_eq_same,
      Pi.single_eq_of_ne hp02 1, one_smul, zero_smul, add_zero] at h5
    have h6 := congrFun (congrFun h5 (spAPar i0)) i2
    have f3 : (Pi.single i0 (1 : K) : Fin N → K) i2 = 0 := Pi.single_eq_of_ne (Ne.symm hi02) 1
    have f4 : (Pi.single (spAPar i0) (1 : K) : Fin N → K) i2 = 0 :=
      Pi.single_eq_of_ne (Ne.symm hi12) 1
    simp only [Matrix.add_apply, vecMulVec_apply, Pi.add_apply, Pi.single_eq_same, he0, he2, f3,
      f4, mul_one, mul_zero, add_zero, zero_add] at h6
    exact one_ne_zero (add_left_cancel (h6.trans (add_zero _).symm))
  ·
    rw [hca]
    have h1 : Φ₂ (upperUnipotentSp N K hSR) =
        Φ₁ ((ι : StatedSp N K) * upperUnipotentSp N K hSR * (ι : StatedSp N K)⁻¹) := by
      rw [← hψ ⟨upperUnipotentSp N K hSR, huC⟩, hψu]
      rfl
    rw [h1, ← map_mul]
    congr 1
    have hιa' : (ι : StatedSp N K) * spARep N j = spARep N j * (ι : StatedSp N K) :=
      mem_centralizer_singleton_iff.1 ι.2
    have hau : spARep N j * upperUnipotentSp N K hSR = upperUnipotentSp N K hR₀t := by
      rw [spARep, upperUnipotentSp_mul]
      exact upperUnipotentSp_congr _ _ (by rw [← add_assoc, lagMat_add_self, zero_add])
    rw [← mul_assoc, ← mul_assoc, ← hιa', mul_assoc (ι : StatedSp N K), hau, ← hda]
    group

end CFSG.SeitzReduction.SymplecticPilot
