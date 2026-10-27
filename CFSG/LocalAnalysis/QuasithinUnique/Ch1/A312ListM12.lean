module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLatAlt
public import CFSG.Blueprint.NativeSporadic
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM12Inputs
public import Certificates.Certificate4079
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

namespace M12Lat

open Equiv PermLat

theorem cert_check : cert.check RN.enc = true :=
  Certificates.certificate4079

theorem mGens_closure :
    Subgroup.closure {g | g ∈ cert.mGens} = CFSG.Blueprint.NativeSporadic.M12 := by
  unfold CFSG.Blueprint.NativeSporadic.M12
  congr 1
  ext g
  simp [cert, mGens]

theorem a312For_M12_closure (hq : CFSG.IsQuasisimple ↥(Subgroup.closure {g | g ∈ cert.mGens})) :
    A312For ↥(Subgroup.closure {g | g ∈ cert.mGens}) := by
  have hck := cert_check
  have hU := cert.isSylowTwoOf_top (rawIsEnc 12) hck (k := 6) (m := 1485) (by decide) (by decide)
    (by omega)
  refine A312For.of_solvable_overgroups hq _ hU fun Y hUY hYtop => ?_
  obtain ⟨L, hL, hLM, hYL, hcardL⟩ := cert.overgroup_cases (rawIsEnc 12) hck Y hUY
  have hsz : Nat.card (Subgroup.closure {g | g ∈ L}) = 64 ∨
      Nat.card (Subgroup.closure {g | g ∈ L}) = 95040 ∨
      Nat.card (Subgroup.closure {g | g ∈ L}) = 192 := by
    have h : Nat.card (Subgroup.closure {g | g ∈ L}) ∈ [64, 95040, 192, 192] := hcardL
    simpa using h
  rcases hsz with h64 | h95 | h192
  · rw [hYL]
    exact solvable_subgroupOf_two_three hLM (a := 6) (b := 0) (by rw [h64]; norm_num)
  · exfalso
    apply hYtop
    have hM : Nat.card (Subgroup.closure {g | g ∈ cert.mGens}) = 95040 :=
      cert.card_m (rawIsEnc 12) (LatCert.closedOK_of_check hck) (LatCert.sizesOK_of_check hck)
    have heq : Subgroup.closure {g | g ∈ L} = Subgroup.closure {g | g ∈ cert.mGens} :=
      Subgroup.eq_of_le_of_card_ge hLM (by rw [h95, hM])
    rw [hYL, heq, Subgroup.subgroupOf_self]
  · rw [hYL]
    exact solvable_subgroupOf_two_three hLM (a := 6) (b := 1) (by rw [h192]; norm_num)

theorem a312For_M12 (hq : CFSG.IsQuasisimple ↥CFSG.Blueprint.NativeSporadic.M12) :
    A312For ↥CFSG.Blueprint.NativeSporadic.M12 := by
  let e : ↥CFSG.Blueprint.NativeSporadic.M12 ≃* ↥(Subgroup.closure {g | g ∈ cert.mGens}) :=
    (MulEquiv.subgroupCongr mGens_closure).symm
  exact A312For.of_mulEquiv e
    (a312For_M12_closure (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq))

end M12Lat

theorem m12 : FamM12 := by
  intro X _ _ hq hX
  obtain ⟨e⟩ := hX
  let e' : X ≃* ↥CFSG.Blueprint.NativeSporadic.M12 := e
  exact A312For.of_mulEquiv e'
    (M12Lat.a312For_M12 (CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq))

end CFSG.QuasithinUnique.Vol2Native.A312L
