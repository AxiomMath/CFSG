module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPDich

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section Indep


theorem fieldCentIndepAt_holds (G : Type) [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : FieldCentIndepAt G p :=
  FP.fieldCentIndepAt_holds G hp hp2

end Indep

section FieldN


theorem fieldNAt_holds (G : Type) [Group G] [Finite G] (p : ℕ) : FieldNAt G p :=
  FP.fieldNAt_holds G p

theorem fieldDichotomyAt_of_noTriality {G : Type} [Group G] [Finite G] (hNT : FP.NoTrialityAt G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : FieldDichotomyAt G p :=
  FP.fieldDichotomyAt_of_noTriality hNT hp hp2

end FieldN

end CFSG.LocalAnalysis.GLTheoremA
