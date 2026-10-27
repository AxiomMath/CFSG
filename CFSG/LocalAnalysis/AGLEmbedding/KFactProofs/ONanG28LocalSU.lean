module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28SUInput
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28SUGroup
public import Certificates.Certificate9559

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Item434G28 CFSG.AGLEmbedding.KFactProofs.G28.SU
  CFSG.Assembly.LowTwoRank
open scoped Matrix

section Main


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

namespace SU

theorem suW_eq : suW = hW := rfl

theorem conj_mul (P Pi a b : Matrix (Fin 6) (Fin 6) GF8) (hP : P * Pi = 1) :
    (Pi * a * P) * (Pi * b * P) = Pi * (a * b) * P := by
  calc (Pi * a * P) * (Pi * b * P) = Pi * a * (P * Pi) * b * P := by simp only [mul_assoc]
    _ = Pi * (a * b) * P := by rw [hP]; simp only [mul_assoc, mul_one]

theorem hElt_mem_VX (h : SUHyp M) (k : Fin 7) : hElt M k ∈ VX M := by
  rw [h.2]
  exact Subgroup.subset_closure ⟨k, rfl⟩

theorem zE_mem_VX' : zE M ∈ VX M := by
  rw [VX, Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]

end SU

theorem su_struct (_hK : Nat.card K = 8) (h : SUHyp M) : SUStruct M := by
  obtain ⟨hP, hPi, hZ, hgens, htr⟩ : suOK := Certificates.certificate9559
  have : Finite ↥(adjointGroup .G2 K) := Subtype.finite
  have hρh : ∀ k : Fin 7, M.rho (hElt M k) = decode (wordCode suW[k.val]!) := by
    intro k
    rw [SU.suW_eq]
    exact rho_hElt M k.val
  have hρz : mPi * M.rho (zE M) * mP = rbM := by rw [rho_zE]; exact hZ
  have hS : ∀ s ∈ Set.range (fun k : Fin 7 => hElt M k), ∃ G : Matrix (Fin 3) (Fin 3) F64,
      blockMat G = mPi * M.rho s * mP ∧ G.det = 1 ∧ (blockMat G)ᵀ * jbM * blockMat G = jbM := by
    rintro s ⟨k, rfl⟩
    have hA : mPi * M.rho (hElt M k) * mP = aMat k := by rw [hρh k]; rfl
    have hcomm : M.rho (hElt M k) * M.rho (zE M) = M.rho (zE M) * M.rho (hElt M k) := by
      rw [← map_mul, ← map_mul]
      have := (Subgroup.mem_centralizer_iff.1 (SU.hElt_mem_VX M h k)) (zE M) rfl
      rw [this]
    have hcomm' : aMat k * rbM = rbM * aMat k := by
      rw [← hA, ← hρz, SU.conj_mul mP mPi _ _ hP, SU.conj_mul mP mPi _ _ hP, hcomm]
    obtain ⟨G, hG⟩ := blockMat_surj_of_comm (A := aMat k) hcomm'
    refine ⟨G, by rw [hG, hA], ?_, by rw [hG]; exact (hgens k).1⟩
    apply rhoL_injective
    rw [rhoL_det, hG, (hgens k).2, map_one]
  have hcard : Nat.card (Subgroup.closure (Set.range (fun k : Fin 7 => hElt M k))) = 16547328 := by
    rw [← h.2]
    exact h.1
  obtain ⟨Θ0, hΘ0⟩ := exists_equiv_statedSU M.rho M.rho_injective mP mPi hP hPi
    (Set.range (fun k : Fin 7 => hElt M k)) hcard hS
  let Θ : ↥(VX M) ≃* StatedSU 3 8 F64 := (MulEquiv.subgroupCongr h.2).trans Θ0
  have hΘ : ∀ g : ↥(VX M),
      blockMat (((Θ g : StatedSU 3 8 F64) : Matrix.GeneralLinearGroup (Fin 3) F64) :
        Matrix (Fin 3) (Fin 3) F64) = mPi * M.rho g * mP := fun g => hΘ0 _
  let zv : ↥(VX M) := ⟨zE M, SU.zE_mem_VX' M⟩
  have hz : (((Θ zv : StatedSU 3 8 F64) : Matrix.GeneralLinearGroup (Fin 3) F64) :
      Matrix (Fin 3) (Fin 3) F64) = omegaMat := by
    apply blockMat_injective
    rw [hΘ zv, blockMat_omegaMat]
    exact hρz
  have hQ : CFSG.IsQuasisimple ↥(VX M) :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv Θ.symm su_quasi.1
  have hcen : Subgroup.center ↥(VX M) ≤ Subgroup.zpowers zv := center_le_zpowers Θ zv hz
  have hzp : ∀ w : ↥(VX M), w ∈ Subgroup.zpowers zv → (w : adjointGroup .G2 K) ∈
      Subgroup.zpowers (zE M) := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact ⟨k, by simp [zv]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    have := hQ.1
    exact Subgroup.isPerfect_iff.mp this
  ·
    intro W hWV hVW
    have hn : (W.subgroupOf (VX M)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWV).2 hVW
    rcases normal_le_center_or_eq_top hQ (W.subgroupOf (VX M)) with hc | ht
    · right
      left
      intro w hw
      exact hzp ⟨w, hWV hw⟩ (hcen (hc (Subgroup.mem_subgroupOf.2 hw)))
    · right
      right
      apply le_antisymm hWV
      intro v hv
      have : (⟨v, hv⟩ : ↥(VX M)) ∈ W.subgroupOf (VX M) := by rw [ht]; trivial
      exact Subgroup.mem_subgroupOf.1 this
  ·
    rintro g ⟨hg, hgc⟩
    have : (⟨g, hg⟩ : ↥(VX M)) ∈ Subgroup.center ↥(VX M) := by
      rw [Subgroup.mem_center_iff]
      intro v
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hgc) v.1 v.2)
    exact hzp _ (hcen this)
  ·
    obtain ⟨d, ψ, hd, hψ⟩ := exists_surj Θ
    exact ⟨d, ψ, hd, hψ⟩
  ·
    refine ⟨hElt M ((5 : Fin 7) : ℕ), SU.hElt_mem_VX M h 5, ?_⟩
    have htr' : Matrix.trace (M.rho (hElt M ((5 : Fin 7) : ℕ))) = GF8.ofNat' 6 := by
      rw [hρh 5]
      exact htr
    rw [htr']
    decide

end Main

end CFSG.AGLEmbedding.KFactProofs.G28
