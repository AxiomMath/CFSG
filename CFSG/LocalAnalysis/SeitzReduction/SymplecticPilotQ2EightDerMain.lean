module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightDerRad
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightDerCore
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightSiegInputs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)
open scoped commutatorElement

section Transport

variable {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2)

theorem sp8dMap_symm_transpose (Y : Matrix (Fin 4) (Fin 4) K) :
    (sp8dMap hK).symm Yᵀ = ((sp8dMap hK).symm Y)ᵀ := rfl

theorem sp8dMap_transpose_of {X : Sp8dMat} (hX : Xᵀ = X) : (sp8dMap hK X)ᵀ = sp8dMap hK X := by
  rw [← sp8dMap_transpose, hX]

end Transport

theorem spTwoLagDerivedClosureAt_four_two : SpTwoLagDerivedClosureAt 4 2 := by
  intro K _ _ _ hK H _ Φ₁ Φ₂ h₁ h₂ ha hC
  set F₂ : Sp8dMat → Sp8dMat := fun X => (sp8dMap hK).symm (sp8dF Φ₁ Φ₂ (sp8dMap hK X))
    with hF₂
  have hMF : ∀ X, sp8dMap hK (F₂ X) = sp8dF Φ₁ Φ₂ (sp8dMap hK X) :=
    fun X => (sp8dMap hK).apply_symm_apply _
  have hsym₂ : ∀ X, Sp8dIsQ5 X → (F₂ X)ᵀ = F₂ X := by
    intro X hX
    simp only [hF₂]
    rw [← sp8dMap_symm_transpose, sp8dF_transpose hK h₁ hC (sp8dMap_transpose_of hK hX.1)]
  have hadd₂ : ∀ X Y, Sp8dIsQ5 X → Sp8dIsQ5 Y → F₂ (X + Y) = F₂ X + F₂ Y := by
    intro X Y hX hY
    simp only [hF₂]
    rw [map_add, sp8dF_add hK h₁ hC (sp8dMap_transpose_of hK hX.1)
      (sp8dMap_transpose_of hK hY.1), map_add]
  have hinj₂ : ∀ X Y, Sp8dIsQ5 X → Sp8dIsQ5 Y → F₂ X = F₂ Y → X = Y := by
    intro X Y hX hY h
    have h' : sp8dF Φ₁ Φ₂ (sp8dMap hK X) = sp8dF Φ₁ Φ₂ (sp8dMap hK Y) := by
      rw [← hMF, ← hMF, h]
    exact (sp8dMap hK).injective (sp8dF_injective hK h₁ hC h₂ (sp8dMap_transpose_of hK hX.1)
      (sp8dMap_transpose_of hK hY.1) h')
  have hS₂ : F₂ sp8dS = sp8dS := by
    simp only [hF₂]
    rw [sp8dMap_S, sp8dF_S hK h₁ hC ha, ← sp8dMap_S hK, (sp8dMap hK).symm_apply_apply]
  have htw : ∀ (Bm : Sp8dMat) (BG : GL (Fin 4) K),
      (BG : Matrix (Fin 4) (Fin 4) K) = sp8dMap hK Bm →
      leviEmbedGL K 4 BG ∈ ⁅centralizer ({spARep 4 2} : Set (StatedSp 4 K)),
        centralizer ({spARep 4 2} : Set (StatedSp 4 K))⁆ → Sp8dTwisted F₂ Bm := by
    intro Bm BG hBG hmem
    obtain ⟨c, hc, ec⟩ := sp8d_exists_of_map_eq hC hmem
    have hcC := sp8d_derived_le hc
    have hbC := sp8d_derived_le hmem
    refine ⟨(sp8dMap hK).symm (sp8dLam c), ?_, fun Z hZ => ?_⟩
    · apply (sp8dMap hK).injective
      rw [map_mul, map_mul, sp8dMap_transpose, (sp8dMap hK).apply_symm_apply, sp8dMap_S]
      exact sp8dLam_transpose_mul hcC
    · apply (sp8dMap hK).injective
      have hlb : sp8dLam (leviEmbedGL K 4 BG) = sp8dMap hK Bm := by
        rw [sp8dLam_leviEmbedGL, hBG]
      rw [map_mul, map_mul, sp8dMap_transpose, hMF, hMF, ← hlb, map_mul, map_mul,
        sp8dMap_transpose, (sp8dMap hK).apply_symm_apply]
      exact sp8dF_twisted hK h₁ hC hbC hcC ec.symm (sp8dMap_transpose_of hK hZ.1)
  obtain ⟨hb1, hg1, hh1⟩ := sp8d_levi_gens_mem (K := K) hK
  obtain ⟨X, hX, hFX⟩ := sp8d_exists_mem_O15 F₂ hsym₂ hadd₂ hinj₂ hS₂
    (htw _ _ (coe_sp8dB1GL hK) hb1) (htw _ _ (coe_sp8dGGL hK) hg1)
    (htw _ _ (coe_sp8dHGL hK) hh1)
  obtain ⟨A, A', hAA', hA'A, hAX, hAB⟩ := sp8dTabA_spec hX
  obtain ⟨B, B', hBB', hB'B, hBX⟩ := sp8dTabB_spec hFX
  have hXsym : (sp8dMap hK X)ᵀ = sp8dMap hK X :=
    sp8dMap_transpose_of hK (sp8dO15_isQ5 hX).1
  have hca : leviEmbedGL K 4 (sp8dGL hK A A' hAA' hA'A) * spARep 4 2 *
      (leviEmbedGL K 4 (sp8dGL hK A A' hAA' hA'A))⁻¹ = upperUnipotentSp 4 K hXsym := by
    rw [spARep, leviEmbedGL_conj_upperUnipotentSp]
    refine upperUnipotentSp_congr _ _ ?_
    rw [coe_sp8dGL, ← sp8dMap_S hK, ← sp8dMap_transpose, ← map_mul, ← map_mul, hAX]
  refine ⟨leviEmbedGL K 4 (sp8dGL hK A A' hAA' hA'A), leviEmbedGL K 4 (sp8dGL hK B B' hBB' hB'B),
    ⟨leviEmbedGL K 4 (sp8dB1GL hK), hb1, ?_⟩, ?_⟩
  ·
    intro hmem
    set c := leviEmbedGL K 4 (sp8dGL hK A A' hAA' hA'A) with hc
    set y := leviEmbedGL K 4 (sp8dB1GL hK) with hy
    have h1 : c * y * c⁻¹ * spARep 4 2 = spARep 4 2 * (c * y * c⁻¹) :=
      mem_centralizer_singleton_iff.1 (sp8d_derived_le hmem)
    have hSt : sp8dSᵀ = sp8dS := by decide
    have hY : (sp8dMap hK (A' * sp8dS * A'ᵀ))ᵀ = sp8dMap hK (A' * sp8dS * A'ᵀ) :=
      sp8dMap_transpose_of hK (by rw [transpose_mul, transpose_mul, transpose_transpose, hSt,
        Matrix.mul_assoc])
    have hcinv : c⁻¹ * spARep 4 2 * c = upperUnipotentSp 4 K hY := by
      have h := leviEmbedGL_conj_upperUnipotentSp ((sp8dGL hK A A' hAA' hA'A)⁻¹)
        (spARepMat_transpose (K := K) 4 2)
      rw [map_inv, inv_inv] at h
      rw [hc, spARep, h]
      refine upperUnipotentSp_congr _ _ ?_
      rw [coe_sp8dGL_inv, ← sp8dMap_S hK, ← sp8dMap_transpose, ← map_mul, ← map_mul]
    have h2 : y * upperUnipotentSp 4 K hY * y⁻¹ = upperUnipotentSp 4 K hY := by
      rw [← hcinv]
      calc y * (c⁻¹ * spARep 4 2 * c) * y⁻¹ =
            c⁻¹ * (c * y * c⁻¹ * spARep 4 2) * c * y⁻¹ := by group
        _ = c⁻¹ * (spARep 4 2 * (c * y * c⁻¹)) * c * y⁻¹ := by rw [h1]
        _ = c⁻¹ * spARep 4 2 * c := by group
    rw [hy, leviEmbedGL_conj_upperUnipotentSp] at h2
    have h3 := upperUnipotentSp_inj_lag _ _ h2
    rw [coe_sp8dB1GL, ← sp8dMap_transpose, ← map_mul, ← map_mul] at h3
    exact hAB ((sp8dMap hK).injective h3)
  ·
    rw [hca, sp8dF_eq hK h₁ hC hXsym, ← map_mul]
    congr 1
    have hSF : (sp8dS + F₂ X)ᵀ = sp8dS + F₂ X := (sp8dIsQ5_S.add (sp8dO15_isQ5 hFX)).1
    have hda : leviEmbedGL K 4 (sp8dGL hK B B' hBB' hB'B) * spARep 4 1 *
        (leviEmbedGL K 4 (sp8dGL hK B B' hBB' hB'B))⁻¹ =
        upperUnipotentSp 4 K (sp8dMap_transpose_of hK hSF) := by
      rw [spARep, leviEmbedGL_conj_upperUnipotentSp]
      refine upperUnipotentSp_congr _ _ ?_
      rw [coe_sp8dGL, ← sp8dMap_C1 hK, ← sp8dMap_transpose, ← map_mul, ← map_mul, hBX]
    rw [hda, spARep, upperUnipotentSp_mul]
    refine upperUnipotentSp_congr _ _ ?_
    rw [map_add, sp8dMap_S, hMF]

end CFSG.SeitzReduction.SymplecticPilot
