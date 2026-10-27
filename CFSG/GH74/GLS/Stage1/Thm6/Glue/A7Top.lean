module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.A7Main
public import CFSG.GH74.GLS.Stage1.Thm6.Assembly
public import CFSG.GH74.GLS.Stage1.Thm6.Adapters
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.K1Basic
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.Asc03
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.Struct
public import CFSG.GH74.GLS.Stage12.Interface
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] [Finite G]

@[expose] def IV3SylowLeafA7 (x : G) (Kb : Subgroup (CentralizerBar x)) : Prop :=
  Conf12B G x Kb → IsA7Model ↥Kb → ∀ [Kb.Normal] (S : Subgroup G), IsSylow2In S ⊤ →
    IsSylow2In (S ⊓ Cx x) (Cx x) → IV3_12_8c_sylow_nn x S (S ⊓ Cx x) (Pg x Kb (S ⊓ Cx x))

end CFSG.GH74.GLS.Stage1.Thm6.Glue

