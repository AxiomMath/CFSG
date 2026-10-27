module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpW
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveJ4

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem noFiveOver_altSporadic_leaf
    : ∀ (W : Type) [Group W] [Finite W], (Ch1.AltList W ∨ Ch1.SporadicList W) →
      FiveNorm.NoFiveOver W :=
  fun _ _ _ hW => hW.elim noFiveOver_altList614
    (noFiveOver_sporadicList614 FiveNorm.J4F.fiveRigid_J4.2.2)

theorem kg614FiveSpor_leaf
    : KG614FiveSpor :=
  kg614FiveSpor_of_noFiveOver noFiveOver_altSporadic_leaf

end CFSG.GH74.QTGen4.Leaves
