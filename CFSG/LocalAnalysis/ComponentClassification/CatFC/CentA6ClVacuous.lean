module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Classify

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem oddA6Shape_twistedB2 : OddA6Shape .twistedB2 := by
  intro _ _ _ _ _ _ _ hp2 hadm
  exact absurd hadm.2.2.2.1 hp2

theorem oddA6Shape_twistedF4 : OddA6Shape .twistedF4 := by
  intro _ _ _ _ _ _ _ hp2 hadm
  exact absurd hadm.2.2.2.1 hp2

theorem oddA6Shape_Tits : OddA6Shape .Tits := by
  intro _ _ _ _ _ _ _ hp2 hadm
  exact absurd hadm.2.2.2.1 hp2

theorem oddA6Small_twistedB2 : OddA6Small .twistedB2 := by
  intro _ _ _ _ _ _ _ hp2 hadm
  exact absurd hadm.2.2.2.1 hp2

theorem oddA6Small_twistedF4 : OddA6Small .twistedF4 := by
  intro _ _ _ _ _ _ _ hp2 hadm
  exact absurd hadm.2.2.2.1 hp2

theorem oddA6Small_Tits : OddA6Small .Tits := by
  intro _ _ _ _ _ _ _ hp2 hadm
  exact absurd hadm.2.2.2.1 hp2

end CFSG.ComponentClassification.CatFC
