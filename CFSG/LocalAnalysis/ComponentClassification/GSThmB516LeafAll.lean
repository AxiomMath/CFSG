module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafEven
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafSp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOrth
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10TwMain
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafAlt
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafMain

public section

namespace CFSG.ComponentClassification.GSThmB

theorem cf516PumpLeaf_of_sporRow
    (hSpor : CF516SporRow) : CF516PumpLeaf :=
  cf516PumpLeaf_of_rows cf516EvenRow cf516LinRow cf516SpRow cf516OrthRow
      (cf516ExcRow_of Burgoyne.X10.e7TwistedA7P_model Burgoyne.X10.twE6TwentyP_model
          Burgoyne.X10.twE6A5P_model)
    cf516AltRow hSpor

theorem cf516PumpUpInv_of_sporRow
    (hSpor : CF516SporRow) : CF516PumpUpInv :=
  cf516PumpUpInv_of_leaf (cf516PumpLeaf_of_sporRow hSpor)

end CFSG.ComponentClassification.GSThmB
