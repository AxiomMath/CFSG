module

public import CFSG.GH74.GLS.Stage1.Thm4.L97b
public import CFSG.GH74.GLS.Stage1.Thm4.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec5

theorem lemma9_7_thm : Lemma9_7 := by
  intro G _ _ Lh _ z t S K h
  ext K'
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hK'
    obtain ⟨n, hn8, -, hLn⟩ := h.cover
    exact L97.rigid_unique h.std.rank.2 hn8 hLn hK' h.K_rigid
  · intro hK'
    rw [hK']
    exact h.K_rigid

end CFSG.GH74.GLS.Stage1.Thm4
