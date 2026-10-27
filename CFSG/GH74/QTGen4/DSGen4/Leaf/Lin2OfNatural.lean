module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.Lin2OfNaturalD
public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4

theorem leafLin2OfNatural : LeafLin2OfNatural := by
  intro G _ _ L hq hc he hn hnat
  exact CFSG.GH74.QTGen4.DSGen4.Lin2D.isLin2Type_of_natural hq hc he hn hnat

end CFSG.GH74.QTGen4.DSGen4
