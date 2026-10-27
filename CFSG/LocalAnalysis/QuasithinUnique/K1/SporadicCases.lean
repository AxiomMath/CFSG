module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicSimple
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ1Model
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public import CFSG.Sporadic.J2
public import CFSG.Walter.Models

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.Blueprint.NativeSporadic

theorem k1_sporadic_cases
    (hJ4s : IsSimpleGroup (Carrier .J4))
    (hJ4 : NoStronglyClosedElemAbelian (Carrier .J4)) :
    K1FamilyRecognition SporadicFamilyCat := by
  intro G _ _ H S U L h hfam w hwU _ hnc hchar
  exfalso
  obtain ⟨s, hs, ⟨e⟩⟩ := hfam
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : IsSimpleGroup (Carrier .M11) := CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
    exact false_of_simple_of_noStronglyClosed h e SporadicPerm.m11_noStronglyClosedElemAbelian hwU
      hnc
  · have : IsSimpleGroup (Carrier .M12) := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    exact false_of_simple_of_noStronglyClosed h e SporadicPerm.m12_noStronglyClosedElemAbelian hwU
      hnc
  · have : IsSimpleGroup (Carrier .M22) := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    exact false_of_simple_of_noStronglyClosed h e SporadicPerm.m22_noStronglyClosedElemAbelian hwU
      hnc
  · have : IsSimpleGroup (Carrier .M23) := CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
    exact false_of_simple_of_noStronglyClosed h e SporadicPerm.m23_noStronglyClosedElemAbelian hwU
      hnc
  · have : IsSimpleGroup (Carrier .M24) := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    exact false_of_simple_of_noStronglyClosed h e SporadicPerm.m24_noStronglyClosedElemAbelian hwU
      hnc
  · exact false_of_J1_component h (e.trans (CFSG.Walter.walterJ1EquivNative.symm)) hwU hnc hchar
  · have : IsSimpleGroup (Carrier .J2) := CFSG.Sporadic.J2.fam_j2_simplicity.2.2
    exact false_of_simple_of_noStronglyClosed h e SporadicPerm.j2_noStronglyClosedElemAbelian hwU
      hnc
  · have : IsSimpleGroup (Carrier .J4) := hJ4s
    exact false_of_simple_of_noStronglyClosed h e hJ4 hwU hnc
  · have : IsSimpleGroup (Carrier .HS) := CFSG.Sporadic.HS.fam_hs_simplicity.2.2
    exact false_of_simple_of_noStronglyClosed h e SporadicPerm.hs_noStronglyClosedElemAbelian hwU
      hnc
  · have : IsSimpleGroup (Carrier .He) := CFSG.Sporadic.He.fam_he_simplicity.2.2
    exact false_of_simple_of_noStronglyClosed h e SporadicPerm.he_noStronglyClosedElemAbelian hwU
      hnc
  · have : IsSimpleGroup (Carrier .Ru) := CFSG.Sporadic.Ru.fam_ru_simplicity.2.2
    exact false_of_simple_of_noStronglyClosed h e SporadicPerm.ru_noStronglyClosedElemAbelian hwU
      hnc

end CFSG.QuasithinUnique.K1
