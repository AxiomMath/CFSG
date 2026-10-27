module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamL43Aux
public import CFSG.GH74.GLS.C3.Layer1.St1EndNL43Mat

public section

namespace CFSG.GH74.GLS

open Blueprint

theorem lem711_l43 :
    Lem711Empty (fun X _ => LieModel X .PSL 4 3 1) :=
  lem711_l43_aux C3.Layer1.EndN.L43.zStar C3.Layer1.EndN.L43.orderOf_zStar
    C3.Layer1.EndN.L43.l43_witness

theorem lem711_l4 (p f : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Lem711Empty (fun X _ => LieModel X .PSL 4 p f) :=
  lem711_l4_of_three lem711_l43 p f hp hp2 hf

end CFSG.GH74.GLS
