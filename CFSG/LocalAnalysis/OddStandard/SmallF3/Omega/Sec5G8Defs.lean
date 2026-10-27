module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5SH8Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def Sec5G8Outcome {X : Type} [Group X] (Tb : Subgroup X) : Prop :=
  ∃ P : Sylow 2 (Sec5GBar Tb), (P : Subgroup (Sec5GBar Tb)) = Sec5GImg Tb ∧
    Nonempty (↥P ≃* DihedralGroup 4) ∧ CFSG.oddCore (Sec5GBar Tb) = ⊥ ∧
    normalClosure ((P : Subgroup (Sec5GBar Tb)) : Set (Sec5GBar Tb)) = ⊤ ∧ Sec5SH8Shape P

end CFSG.OddStandard.SmallF3.Omega
