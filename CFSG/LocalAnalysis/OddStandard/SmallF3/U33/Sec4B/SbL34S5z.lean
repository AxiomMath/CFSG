module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5i
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5m1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5m2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5m3

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open CFSG.OddStandard.SmallF3.HarrisU33.L34

theorem l34_s5 : L34S5Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau _ _ ha hQn
  obtain ⟨B, ω, hB⟩ := exists_BData ha hQn
  have hc := ha.toCtx4L.toCtx4Q
  by_cases hωt : ω = t
  · exact (case_t ha hB hωt).elim
  · rcases omega_cases_B ha hB with hE | hΩ
    · exact (case_elem ha hB hωt hE).elim
    · refine ⟨ω, ?_, case_non ha hB hΩ⟩
      rcases (mem_T_iff hc).mp hB.ω_mem with h1 | h1 | h1 | h1
      · exact absurd h1 hB.ω_ne
      · exact absurd h1 hωt
      · exact Or.inl h1
      · exact Or.inr h1

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
