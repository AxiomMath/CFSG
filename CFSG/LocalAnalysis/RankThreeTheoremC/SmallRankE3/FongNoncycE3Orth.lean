module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncycE3Torus
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.OrthRot

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncyc

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.SectionRank.ClassicalEven
open CFSG.SectionRank.ClassicalEven.OrthRot

theorem four_planes_le_pRank_three {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] [CharP K 2] {Q : (ι → K) → K} {P₀ P₁ P₂ P₃ : Plane Q} (h₀₁ : P₀.Orth P₁)
    (h₀₂ : P₀.Orth P₂) (h₀₃ : P₀.Orth P₃) (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃)
    (h₂₃ : P₂.Orth P₃) :
    4 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega Q))) := by
  refine four_le_pRank_statedProj P₀.rot_mem P₁.rot_mem P₂.rot_mem P₃.rot_mem
    P₀.rot_pow_three P₁.rot_pow_three P₂.rot_pow_three P₃.rot_pow_three
    (Plane.rot_commute h₀₁) (Plane.rot_commute h₀₂) (Plane.rot_commute h₀₃)
    (Plane.rot_commute h₁₂) (Plane.rot_commute h₁₃) (Plane.rot_commute h₂₃)
    (fun hc => ?_) (fun m c hc h => ?_) (fun m k c hc h => ?_) (fun m k l c hc h => ?_)
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    exact P₀.b_ne_smul_a u (P₀.rot_a.symm.trans (hu P₀.a))
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    refine P₁.b_ne_smul_a u ?_
    rw [← P₁.rot_a, ← h, OrthRot.mul_mulVec, hu, mulVec_smul,
      OrthRot.pow_mulVec_of_fix (P₀.rot_fix h₀₁.f_a h₀₁.g_a)]
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    refine P₂.b_ne_smul_a u ?_
    rw [← P₂.rot_a, ← h]
    simp only [OrthRot.mul_mulVec, hu, mulVec_smul,
      OrthRot.pow_mulVec_of_fix (P₁.rot_fix h₁₂.f_a h₁₂.g_a),
      OrthRot.pow_mulVec_of_fix (P₀.rot_fix h₀₂.f_a h₀₂.g_a)]
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    refine P₃.b_ne_smul_a u ?_
    rw [← P₃.rot_a, ← h]
    simp only [OrthRot.mul_mulVec, hu, mulVec_smul,
      OrthRot.pow_mulVec_of_fix (P₂.rot_fix h₂₃.f_a h₂₃.g_a),
      OrthRot.pow_mulVec_of_fix (P₁.rot_fix h₁₃.f_a h₁₃.g_a),
      OrthRot.pow_mulVec_of_fix (P₀.rot_fix h₀₃.f_a h₀₃.g_a)]

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncyc
