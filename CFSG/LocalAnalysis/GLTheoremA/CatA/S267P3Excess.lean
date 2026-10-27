module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Base

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

variable {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem P3Hyp.twoLocalRank_le (H : P3Hyp q S B) : GLATwoLocalRank 3 Ω ≤ 4 := by
  have h := H.twoLocal
  rw [H.card] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
