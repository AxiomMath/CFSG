module

public import CFSG.Quasithin.Recognition.G23TypeDefs

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G23Type
open scoped MatrixGroups

variable {G : Type*} [Group G]

noncomputable def g23QuotMap {M : Subgroup G} (hM : G23Two M) : ↥M →* SL(3, ZMod 2) :=
  hM.quot.choose

theorem g23QuotMap_surjective {M : Subgroup G} (hM : G23Two M) :
    Function.Surjective (g23QuotMap hM) :=
  hM.quot.choose_spec.1

theorem g23QuotMap_ker {M : Subgroup G} (hM : G23Two M) :
    (g23QuotMap hM).ker = (quasithinGenFitting M).subgroupOf M :=
  hM.quot.choose_spec.2

end CFSG.GH74.QTGen4.Recog.G23
