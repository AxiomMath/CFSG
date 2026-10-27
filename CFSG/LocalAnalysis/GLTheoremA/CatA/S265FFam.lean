module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FTits
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FL2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def QUFamDU3 : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω), QUNL p S B T x b → p = 3 →
    catalogIs (PSimple p (Ipart p S b)) tyU38 → QUConcl p S B x b

section Sz


theorem quFamE : QUFamE := by
  intro p Ω _ _ S B T x b hN hp5 hE
  rcases tyE_split hE with hSz | hTits
  · exact (s265f_false_of_sz32 hN.cfg hp5 hSz).elim
  · exact (s265f_false_of_tits hN.cfg hp5 hTits).elim

end Sz

section L2


theorem quFamD_of_u3 (h : QUFamDU3) : QUFamD := by
  intro p Ω _ _ S B T x b hN hp3 hD
  rcases tyD_split hD with hL | hU
  · exact (s265f_false_of_l28 hN.cfg hp3 hL).elim
  · exact h p Ω S B T x b hN hp3 hU

end L2

end CFSG.LocalAnalysis.GLTheoremA.S265

end
