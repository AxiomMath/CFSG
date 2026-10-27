module

public import CFSG.Fischer.Classification.Assembly
public import CFSG.Fischer.Classification.PartII.O3.Input
public import CFSG.Fischer.Classification.PartII.O2Input
public import CFSG.Fischer.Classification.PartII.O2G.Section
public import CFSG.Fischer.Classification.PartIII.Final

public section

namespace CFSG.Fischer.Classification

theorem statement_of_twinFour
    (h : O2TwinFourInput) : Statement :=
  statement_of_remaining o3InputI (o2InputI_of_twins o2_O1_input h) classicalPartIIIInputI

end CFSG.Fischer.Classification
