module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.A3Structure314Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Model
public import CFSG.Quasithin.H13.KGFactA314J4
public import CFSG.Quasithin.H13.NQCatA314A7
public import CFSG.Quasithin.H13.NQCatA314HS
public import CFSG.Quasithin.H13.NQCatA314J1
public import CFSG.Quasithin.H13.NQCatA314J2
public import CFSG.Quasithin.H13.NQCatA314L3
public import CFSG.Quasithin.H13.NQCatA314Lie
public import CFSG.Quasithin.H13.NQCatA314M23
public import CFSG.Quasithin.H13.NQCatA314Ru

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique

theorem a314Facts_holds_F4 :
    A314Facts_F4 :=
  ⟨CFSG.QuasithinUnique.A5.G3.a314ModelFacts,
    ⟨(fun G _ _ => desc_lie G), (fun G _ _ => desc_alt7 G), (fun G _ _ => desc_sl3five G),
      (fun G _ _ => desc_l3five G), (fun G _ _ => desc_mathieu G), (fun G _ _ => desc_j1 G),
      (fun G _ _ => desc_j2 G), (fun G _ _ => CFSG.Quasithin.H13.KGA314J4.a314j4_holds G),
      (fun G _ _ => desc_hs G), (fun G _ _ => desc_ru G)⟩⟩

end CFSG.Quasithin.H13.NQCat.A314D
