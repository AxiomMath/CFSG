module

public import CFSG.LieType.Chevalley.AllRootWeylSignsData

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem pinnedSignTable_E8
    : pinnedSignTable .E8 =
    (List.range (Tag.witnesses .E8).roots.length).map (pinnedSignW .E8) := by
  decide +kernel

theorem witnessCertTable_E8 : witnessCertTable .E8 =
    (List.range (Tag.witnesses .E8).roots.length).map (witnessCertPos .E8) := by
  decide +kernel

theorem certWitnessTable_E8 : certWitnessTable .E8 =
    (List.range (Tag.rootCertificate .E8).roots.length).map (certWitnessPos .E8) := by
  decide +kernel

theorem allRootWeylSigns_E8_row0 : (allRootWeylSigns .E8).getD 0 [] =
    (List.range (Tag.witnesses .E8).roots.length).map (weylSignT .E8 ⟨0, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E8_row1 : (allRootWeylSigns .E8).getD 1 [] =
    (List.range (Tag.witnesses .E8).roots.length).map (weylSignT .E8 ⟨1, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E8_row2 : (allRootWeylSigns .E8).getD 2 [] =
    (List.range (Tag.witnesses .E8).roots.length).map (weylSignT .E8 ⟨2, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E8_row3 : (allRootWeylSigns .E8).getD 3 [] =
    (List.range (Tag.witnesses .E8).roots.length).map (weylSignT .E8 ⟨3, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E8_row4 : (allRootWeylSigns .E8).getD 4 [] =
    (List.range (Tag.witnesses .E8).roots.length).map (weylSignT .E8 ⟨4, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E8_row5 : (allRootWeylSigns .E8).getD 5 [] =
    (List.range (Tag.witnesses .E8).roots.length).map (weylSignT .E8 ⟨5, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E8_row6 : (allRootWeylSigns .E8).getD 6 [] =
    (List.range (Tag.witnesses .E8).roots.length).map (weylSignT .E8 ⟨6, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E8_row7 : (allRootWeylSigns .E8).getD 7 [] =
    (List.range (Tag.witnesses .E8).roots.length).map (weylSignT .E8 ⟨7, by decide⟩) := by
  decide +kernel

end CFSG.LieType.Chevalley
