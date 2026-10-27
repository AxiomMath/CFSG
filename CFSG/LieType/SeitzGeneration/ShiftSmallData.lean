module

public import CFSG.LieType.SeitzGeneration.HeisSmallData5
public import CFSG.LieType.SeitzGeneration.HeisSmallData8
public import CFSG.LieType.SeitzGeneration.HeisSmallData11
public import Certificates.Data.HuppertShift.Data5
public import Certificates.Data.HuppertShift.Data8
public import Certificates.Data.HuppertShift.Data11
public import CFSG.LieType.SeitzGeneration.OuterSmallCheck

public section

namespace CFSG.LieType.SeitzGeneration.HeisSmall

@[expose] def shiftTable5 : List (OuterEntry Q5) :=
  shiftRaw5.map fun r => ⟨dec5 r.1, r.2.1.map mat5, r.2.2⟩

@[expose] def shiftTable8 : List (OuterEntry Q8) :=
  shiftRaw8.map fun r => ⟨dec8 r.1, r.2.1.map mat8, r.2.2⟩

@[expose] def shiftTable11 : List (OuterEntry Q11) :=
  shiftRaw11.map fun r => ⟨dec11 r.1, r.2.1.map mat11, r.2.2⟩

end CFSG.LieType.SeitzGeneration.HeisSmall
