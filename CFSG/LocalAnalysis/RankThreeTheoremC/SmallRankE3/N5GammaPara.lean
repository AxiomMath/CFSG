module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGStep5

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

variable {A : Type} [Group A] [Finite A] {p : ℕ} {Kb Sb Bb Mb : Subgroup A} {z : A}

theorem n5_B_le_normalizer_inf (c : KQCfg A p Kb Sb Bb Mb z) :
    Bb ≤ normalizer ((Kb ⊓ Mb : Subgroup A) : Set A) := by
  intro b hb
  rw [mem_normalizer_iff]
  intro h
  have hbK := mem_normalizer_iff.mp (c.B_le_K hb) h
  have hbM : b ∈ Mb := KGQ.B_le_M c hb
  constructor
  · rintro ⟨hK, hM⟩
    exact ⟨hbK.mp hK, Mb.mul_mem (Mb.mul_mem hbM hM) (Mb.inv_mem hbM)⟩
  · rintro ⟨hK, hM⟩
    refine ⟨hbK.mpr hK, ?_⟩
    have e : h = b⁻¹ * (b * h * b⁻¹) * b := by group
    rw [e]
    exact Mb.mul_mem (Mb.mul_mem (Mb.inv_mem hbM) hM) hbM

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
