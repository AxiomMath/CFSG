module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenLatCert

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open Equiv CFSG.QuasithinUnique.Bridge.Over CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem u33_hT1 : ∀ g ∈ CertU33.cert.tGens, g ∈ CertU33.L1 := by
  intro g hg
  change g ∈ CertU33.tGens at hg
  simp only [CertU33.tGens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem u33_hT2 : ∀ g ∈ CertU33.cert.tGens, g ∈ CertU33.L2 := by
  intro g hg
  change g ∈ CertU33.tGens at hg
  simp only [CertU33.tGens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem u33_hexp1 : ∀ g ∈ CertU33.L1, g ^ 2 ^ 3 = 1 := by
  intro g hg
  simp only [CertU33.L1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> decide +kernel

theorem u33_hexp2 : ∀ g ∈ CertU33.L2, g ^ 2 ^ 3 = 1 := by
  intro g hg
  simp only [CertU33.L2, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> decide +kernel

theorem u33_hcol1 : ∀ t ∈ CertU33.L2, ∀ p, (fun i : Fin 28 => if i.val ∈ [0, 1, 2, 3, 4, 7, 10, 13, 16, 19, 22, 25] then 0 else 1) (t p) = (fun i : Fin 28 => if i.val ∈ [0, 1, 2, 3, 4, 7, 10, 13, 16, 19, 22, 25] then 0 else 1) p := by
  intro t ht
  simp only [CertU33.L2, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> decide +kernel

theorem u33_hcol2 : (fun i : Fin 28 => if i.val ∈ [0, 1, 2, 3, 4, 7, 10, 13, 16, 19, 22, 25] then 0 else 1) (CertU33.L1.getD 2 1 (4 : Fin 28)) ≠ (fun i : Fin 28 => if i.val ∈ [0, 1, 2, 3, 4, 7, 10, 13, 16, 19, 22, 25] then 0 else 1) (4 : Fin 28) := by decide +kernel

theorem yData_u33 :
    YData ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup
      (CertU33.D.subgroupOf CFSG.GH74.KGroups.U33.QP.originalSubgroup) := by
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
  refine yData_of_latCert CertU33.cert CertU33.closure_mGens CertU33.D_le CertU33.cert_check
    CertU33.L1 CertU33.L2 CertU33.L3 rfl 32 96 6048 rfl rfl 3 (by norm_num) (by decide)
    (by norm_num) (by norm_num) u33_hT1 u33_hT2 hL1 hL2
    3 u33_hexp1 u33_hexp2 ?_ ?_ ?_
  · exact ⟨fun i => if i.val ∈ [0, 1, 2, 3, 4, 7, 10, 13, 16, 19, 22, 25] then 0 else 1,
      u33_hcol1, CertU33.L1.getD 2 1, by simp [CertU33.L1], 4, u33_hcol2⟩
  · refine ⟨evalW CertU33.L1 [0, 2, 1], evalW_mem_closure _ _, evalW CertU33.L1 [2],
      evalW_mem_closure _ _, ?_, by decide +kernel⟩
    refine orderOf_eq_prime ?_ (by decide +kernel)
    show evalW CertU33.L1 [0, 2, 1] ^ 3 = 1
    decide +kernel
  · refine ⟨evalW CertU33.L2 [0, 2], evalW_mem_closure _ _, evalW CertU33.L2 [0],
      evalW_mem_closure _ _, ?_, by decide +kernel⟩
    refine orderOf_eq_prime ?_ (by decide +kernel)
    show evalW CertU33.L2 [0, 2] ^ 3 = 1
    decide +kernel

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
