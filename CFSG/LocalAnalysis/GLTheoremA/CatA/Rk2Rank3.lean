module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Inn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Arith2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Rigid
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB


theorem rankThreeLabelAt_of_tables (hInn : Rk2InnRankOn rk2SmallTag) (G : Type)
    [Group G] [Finite G] : RankThreeLabelAt G := by
  intro p hp hp2 B K lab hB hBK hcard hLab
  obtain ⟨lab₁, hLab₁, -, hr⟩ := rk2_inn_bound_on hInn hp hp2 3 hB hBK hcard
  have hmpos := rk2Ord_pos hp hp2 lab₁.n
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_⟩
  · have h1 := rk2_rigid hLab₁ hLab (Or.inl ht)
    have := rk2Mult_le_two_of_small h1 hmpos
    have := hr h1
    omega
  · have h1 := rk2_rigid hLab₁ hLab (Or.inr (Or.inl ht))
    have := rk2Mult_le_two_of_small h1 hmpos
    have := hr h1
    omega
  · have h1 := rk2_rigid hLab₁ hLab (Or.inr (Or.inr ht))
    have := rk2Mult_le_two_of_small h1 hmpos
    have := hr h1
    omega

end CFSG.LocalAnalysis.GLTheoremA
