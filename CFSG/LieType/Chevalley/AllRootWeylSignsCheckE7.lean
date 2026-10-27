module

public import CFSG.LieType.Chevalley.AllRootWeylSignsData

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem pinnedSignTable_E7
    : pinnedSignTable .E7 =
    (List.range (Tag.witnesses .E7).roots.length).map (pinnedSignW .E7) := by
  decide +kernel

theorem witnessCertTable_E7 : witnessCertTable .E7 =
    (List.range (Tag.witnesses .E7).roots.length).map (witnessCertPos .E7) := by
  decide +kernel

theorem certWitnessTable_E7 : certWitnessTable .E7 =
    (List.range (Tag.rootCertificate .E7).roots.length).map (certWitnessPos .E7) := by
  decide +kernel

theorem allRootWeylSigns_E7_row0 : (allRootWeylSigns .E7).getD 0 [] =
    (List.range (Tag.witnesses .E7).roots.length).map (weylSignT .E7 ⟨0, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E7_row1 : (allRootWeylSigns .E7).getD 1 [] =
    (List.range (Tag.witnesses .E7).roots.length).map (weylSignT .E7 ⟨1, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E7_row2 : (allRootWeylSigns .E7).getD 2 [] =
    (List.range (Tag.witnesses .E7).roots.length).map (weylSignT .E7 ⟨2, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E7_row3 : (allRootWeylSigns .E7).getD 3 [] =
    (List.range (Tag.witnesses .E7).roots.length).map (weylSignT .E7 ⟨3, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E7_row4 : (allRootWeylSigns .E7).getD 4 [] =
    (List.range (Tag.witnesses .E7).roots.length).map (weylSignT .E7 ⟨4, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E7_row5 : (allRootWeylSigns .E7).getD 5 [] =
    (List.range (Tag.witnesses .E7).roots.length).map (weylSignT .E7 ⟨5, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E7_row6 : (allRootWeylSigns .E7).getD 6 [] =
    (List.range (Tag.witnesses .E7).roots.length).map (weylSignT .E7 ⟨6, by decide⟩) := by
  decide +kernel

end CFSG.LieType.Chevalley
