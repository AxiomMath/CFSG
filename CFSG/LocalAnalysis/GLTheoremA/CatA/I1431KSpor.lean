module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431KDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZCo1

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd)

open CFSG.Blueprint.NativeSporadic (Carrier)

section KSporCerts

private theorem i1431K_carrier_isKGroup
    {T : Type} [Group T] (hT : CFSG.Open.IsKGroup T)
    {s : TauCeti.SporadicName} (e : T ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    CFSG.Open.IsKGroup (Carrier s) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  exact hT.of_surjective (e.trans b.symm).toMonoidHom (e.trans b.symm).surjective

theorem i1431SporSK_holds
    : I1431SporSK := by
  intro S _ _ s e hK β hβ3 hβ1 J hJ hJU
  by_contra hne
  obtain ⟨e'⟩ := e
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hcard : Nat.card S = sporOrd s :=
    (Nat.card_congr e'.toEquiv).trans (CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s)
  have hdvd : 25920 ∣ sporOrd s := hcard ▸ i1431_card_dvd hJU
  rcases i1431_names_of_dvd s hdvd with hs | hs
  · exact hne hs
  simp only [i1431SporNames, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact I1431Z.row_j3 hOut hbr S ⟨e'⟩ β hβ3 hβ1 J hJ hJU
  · exact I1431Z.row_mcl hOut hbr S ⟨e'⟩ β hβ3 hβ1 J hJ hJU
  · exact I1431Z.row_suz hOut hbr S ⟨e'⟩ β hβ3 hβ1 J hJ hJU
  · exact I1431Z.row_on hOut hbr S ⟨e'⟩ β hβ3 hβ1 J hJ hJU
  · exact I1431Z.row_co3 hOut hbr S ⟨e'⟩ β hβ3 hβ1 J hJ hJU
  · exact I1431Z.row_fi22 hOut hbr S ⟨e'⟩ β hβ3 hβ1 J hJ hJU
  · exact I1431Z.row_hn hOut S ⟨e'⟩ β hβ3 hβ1 J hJ hJU
  · exact I1431Z.row_ly hOut hbr S ⟨e'⟩ β hβ3 hβ1 J hJ hJU
  · exact I1431Z.row_th hOut hbr S ⟨e'⟩ β hβ3 hβ1 J hJ hJU
  · exact I1431Z.row_fi23 hOut hbr S ⟨e'⟩ β hβ3 hβ1 J hJ hJU
  · exact I1431Z.row_co1 hOut hbr S ⟨e'⟩ β hβ3 hβ1 J hJ hJU
  · exact I1431Z.row_fi24 hOut hbr S ⟨e'⟩ β hβ3 hβ1 J hJ hJU
  · exact I1431Z.row_B_of_kGroup hOut (i1431K_carrier_isKGroup hK e') S ⟨e'⟩ β hβ3 hβ1 J hJ hJU
  · exact I1431Z.row_M_of_kGroup hOut (i1431K_carrier_isKGroup hK e') S ⟨e'⟩ β hβ3 hβ1 J hJ hJU

end KSporCerts

end CFSG.LocalAnalysis.GLTheoremA

end
