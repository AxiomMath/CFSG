module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenSmallA6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenSmallU33
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenLatCertTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoAssembly

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.L246C127 CFSG.QuasithinUnique.Bridge.Over
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem twoPar_alt_six :
    ∃ T P₁ P₂ : Subgroup ↥(alternatingGroup (Fin 6)), TwoPar ↥(alternatingGroup (Fin 6)) T P₁ P₂ := by
  refine ⟨_, _, _, (twoParLat_of_latCert Even6.cert Even6.closure_mGens Even6.D_le Even6.cert_check
    Even6.L1 Even6.L2 Even6.L3 rfl 8 24 360 rfl rfl 3 (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (even6_closure_le _ (by decide +kernel)) (even6_closure_le _ (by decide +kernel))
    3 (by decide +kernel) (by decide +kernel)
    ⟨![0, 0, 0, 0, 1, 1], by decide +kernel,
      permOf 6 [[2, 4], [3, 5]], by decide +kernel, 2, by decide +kernel⟩
    Even6.isSylow_D fun Y hY => Even6.overgroups Y hY).toTwoPar⟩

theorem twoPar_u33 :
    ∃ T P₁ P₂ : Subgroup ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup,
      TwoPar ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup T P₁ P₂ := by
  have hAmem : ∀ w : List ℕ, evalW CertU33.mGens w ∈
      CFSG.GH74.KGroups.U33.QP.originalSubgroup := fun w => by
    rw [← CertU33.closure_mGens]; exact evalW_mem_closure _ _
  have hDA : ∀ g ∈ CertU33.tGens, g ∈ CFSG.GH74.KGroups.U33.QP.originalSubgroup := fun g hg =>
    CertU33.D_le (Subgroup.subset_closure hg)
  have hL1 : Subgroup.closure {g | g ∈ CertU33.L1} ≤
      CFSG.GH74.KGroups.U33.QP.originalSubgroup := by
    rw [Subgroup.closure_le]
    intro g hg
    have hg' : g ∈ CertU33.tGens ++ [CertU33.L1.getD 2 1] := by simpa [CertU33.L1, CertU33.tGens] using hg
    rcases List.mem_append.1 hg' with h | h
    · exact hDA g h
    · have : CertU33.L1.getD 2 1 = evalW CertU33.mGens
          [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0] := by decide +kernel
      rw [List.mem_singleton] at h
      rw [h, this]
      exact hAmem _
  have hL2 : Subgroup.closure {g | g ∈ CertU33.L2} ≤
      CFSG.GH74.KGroups.U33.QP.originalSubgroup := by
    rw [Subgroup.closure_le]
    intro g hg
    have hg' : g ∈ CertU33.tGens ++ [CertU33.L2.getD 2 1] := by simpa [CertU33.L2, CertU33.tGens] using hg
    rcases List.mem_append.1 hg' with h | h
    · exact hDA g h
    · have : CertU33.L2.getD 2 1 = evalW CertU33.mGens
          [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] := by decide +kernel
      rw [List.mem_singleton] at h
      rw [h, this]
      exact hAmem _
  refine ⟨_, _, _, (twoParLat_of_latCert CertU33.cert CertU33.closure_mGens CertU33.D_le
    CertU33.cert_check CertU33.L1 CertU33.L2 CertU33.L3 rfl 32 96 6048 rfl rfl 3 (by norm_num)
    (by decide) (by norm_num) (by norm_num) u33_hT1 u33_hT2 hL1 hL2 3 u33_hexp1 u33_hexp2
    ⟨fun i => if i.val ∈ [0, 1, 2, 3, 4, 7, 10, 13, 16, 19, 22, 25] then 0 else 1,
      u33_hcol1, CertU33.L1.getD 2 1, by simp [CertU33.L1], 4, u33_hcol2⟩
    CertU33.isSylow_D fun Y hY => by
      by_cases h : Y = ⊤
      · exact Or.inl h
      · exact Or.inr (CertU33.overgroups _ Y CertU33.isSylow_D hY h)).toTwoPar⟩

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
