module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1U0
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1UTabs
public import CFSG.Sporadic.SmallOddCore.CheckSpec

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M

open CFSG.Monster.B.Co2 CFSG.LieType.Multipliers.U43 CFSG.ComponentClassification.HarrisLit.P1.U43

theorem rep_tabC {A : GL (Fin 4) F9} {k : ℕ} (hA : (A : Matrix (Fin 4) (Fin 4) F9) = matN9 k) :
    Rep 820 (tabC k) (perm820 A) :=
  CFSG.Sporadic.SmallOddCore.co2Rep_natArr_iff.mpr (rep_tu_false hA)

theorem rep_r0 : Rep 820 (r0A ()) r0P := rep_tabC rfl

theorem rep_u0 : Rep 820 (u0A ()) u0P := rep_tabC rfl

theorem rep_v0 : Rep 820 (v0A ()) v0P := rep_tabC rfl

theorem rep_u1 : Rep 820 (u1A ()) u1P := rep_tabC rfl

theorem rep_v1 : Rep 820 (v1A ()) v1P := rep_tabC rfl

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M
