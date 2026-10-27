module

public import CFSG.LieType.Chevalley.AllRootWeylSignsData

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem pinnedSignTable_G2
    : pinnedSignTable .G2 =
    (List.range (Tag.witnesses .G2).roots.length).map (pinnedSignW .G2) := by
  decide +kernel

theorem witnessCertTable_G2 : witnessCertTable .G2 =
    (List.range (Tag.witnesses .G2).roots.length).map (witnessCertPos .G2) := by
  decide +kernel

theorem certWitnessTable_G2 : certWitnessTable .G2 =
    (List.range (Tag.rootCertificate .G2).roots.length).map (certWitnessPos .G2) := by
  decide +kernel

theorem allRootWeylSigns_G2_row0 : (allRootWeylSigns .G2).getD 0 [] =
    (List.range (Tag.witnesses .G2).roots.length).map (weylSignT .G2 ⟨0, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_G2_row1 : (allRootWeylSigns .G2).getD 1 [] =
    (List.range (Tag.witnesses .G2).roots.length).map (weylSignT .G2 ⟨1, by decide⟩) := by
  decide +kernel

theorem pinnedSignTable_F4
    : pinnedSignTable .F4 =
    (List.range (Tag.witnesses .F4).roots.length).map (pinnedSignW .F4) := by
  decide +kernel

theorem witnessCertTable_F4 : witnessCertTable .F4 =
    (List.range (Tag.witnesses .F4).roots.length).map (witnessCertPos .F4) := by
  decide +kernel

theorem certWitnessTable_F4 : certWitnessTable .F4 =
    (List.range (Tag.rootCertificate .F4).roots.length).map (certWitnessPos .F4) := by
  decide +kernel

theorem allRootWeylSigns_F4_row0 : (allRootWeylSigns .F4).getD 0 [] =
    (List.range (Tag.witnesses .F4).roots.length).map (weylSignT .F4 ⟨0, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_F4_row1 : (allRootWeylSigns .F4).getD 1 [] =
    (List.range (Tag.witnesses .F4).roots.length).map (weylSignT .F4 ⟨1, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_F4_row2 : (allRootWeylSigns .F4).getD 2 [] =
    (List.range (Tag.witnesses .F4).roots.length).map (weylSignT .F4 ⟨2, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_F4_row3 : (allRootWeylSigns .F4).getD 3 [] =
    (List.range (Tag.witnesses .F4).roots.length).map (weylSignT .F4 ⟨3, by decide⟩) := by
  decide +kernel

theorem pinnedSignTable_D4
    : pinnedSignTable .D4 =
    (List.range (Tag.witnesses .D4).roots.length).map (pinnedSignW .D4) := by
  decide +kernel

theorem witnessCertTable_D4 : witnessCertTable .D4 =
    (List.range (Tag.witnesses .D4).roots.length).map (witnessCertPos .D4) := by
  decide +kernel

theorem certWitnessTable_D4 : certWitnessTable .D4 =
    (List.range (Tag.rootCertificate .D4).roots.length).map (certWitnessPos .D4) := by
  decide +kernel

theorem allRootWeylSigns_D4_row0 : (allRootWeylSigns .D4).getD 0 [] =
    (List.range (Tag.witnesses .D4).roots.length).map (weylSignT .D4 ⟨0, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_D4_row1 : (allRootWeylSigns .D4).getD 1 [] =
    (List.range (Tag.witnesses .D4).roots.length).map (weylSignT .D4 ⟨1, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_D4_row2 : (allRootWeylSigns .D4).getD 2 [] =
    (List.range (Tag.witnesses .D4).roots.length).map (weylSignT .D4 ⟨2, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_D4_row3 : (allRootWeylSigns .D4).getD 3 [] =
    (List.range (Tag.witnesses .D4).roots.length).map (weylSignT .D4 ⟨3, by decide⟩) := by
  decide +kernel

theorem pinnedSignTable_E6
    : pinnedSignTable .E6 =
    (List.range (Tag.witnesses .E6).roots.length).map (pinnedSignW .E6) := by
  decide +kernel

theorem witnessCertTable_E6 : witnessCertTable .E6 =
    (List.range (Tag.witnesses .E6).roots.length).map (witnessCertPos .E6) := by
  decide +kernel

theorem certWitnessTable_E6 : certWitnessTable .E6 =
    (List.range (Tag.rootCertificate .E6).roots.length).map (certWitnessPos .E6) := by
  decide +kernel

theorem allRootWeylSigns_E6_row0 : (allRootWeylSigns .E6).getD 0 [] =
    (List.range (Tag.witnesses .E6).roots.length).map (weylSignT .E6 ⟨0, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E6_row1 : (allRootWeylSigns .E6).getD 1 [] =
    (List.range (Tag.witnesses .E6).roots.length).map (weylSignT .E6 ⟨1, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E6_row2 : (allRootWeylSigns .E6).getD 2 [] =
    (List.range (Tag.witnesses .E6).roots.length).map (weylSignT .E6 ⟨2, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E6_row3 : (allRootWeylSigns .E6).getD 3 [] =
    (List.range (Tag.witnesses .E6).roots.length).map (weylSignT .E6 ⟨3, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E6_row4 : (allRootWeylSigns .E6).getD 4 [] =
    (List.range (Tag.witnesses .E6).roots.length).map (weylSignT .E6 ⟨4, by decide⟩) := by
  decide +kernel

theorem allRootWeylSigns_E6_row5 : (allRootWeylSigns .E6).getD 5 [] =
    (List.range (Tag.witnesses .E6).roots.length).map (weylSignT .E6 ⟨5, by decide⟩) := by
  decide +kernel

end CFSG.LieType.Chevalley
