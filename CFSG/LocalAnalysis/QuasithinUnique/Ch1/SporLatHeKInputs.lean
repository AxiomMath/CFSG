module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificateInputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHeInputs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.He
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113

#kc_repo #kc_json_gz CFSG.QuasithinUnique.Ch1.SporLat.He.HeK
  "CFSG/LocalAnalysis/QuasithinUnique/Ch1/data/heLatK.json.gz" 403056 8911501554168263455
  (Om : List (List (List Nat) × List (List Nat) × List Nat × List Nat))
  (Ot : List (List (List (List Nat)) × List (List Nat) × List Nat × List Nat))

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.He

open CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def omK {Lab : Type} (x : List Lab × List (List Nat) × List Nat × List Nat) :
    OmegaData Lab :=
  ⟨x.1.toArray, (x.2.1.map List.toArray).toArray, x.2.2.1.toArray, x.2.2.2.toArray⟩

@[expose] def heMemW : LatData (List Nat) where
  O := default
  F := default
  sTabs := heSTabsC
  mw := heMwLit
  mt := heMwLit.map fun ws => ws.map (wordTabA #[heTa, heTb] 8330)
  Om := #[]
  atoms := #[]
  joins := []

@[expose] noncomputable def heLatK : LatData (List Nat) :=
  { heMemW with
    O := ⟨Array.replicate 3935925 [], #[], #[], #[]⟩
    Om := #[omK (HeK.Om.getD 0 default), omK (HeK.Om.getD 1 default),
      omK (HeK.Om.getD 2 default), omK (HeK.Om.getD 3 default), omK (HeK.Om.getD 4 default),
      omK (HeK.Om.getD 5 default), omK (HeK.Om.getD 6 default), omK (HeK.Om.getD 7 default),
      omK (HeK.Om.getD 8 default), omK (HeK.Om.getD 9 default), omK (HeK.Om.getD 10 default)] }

@[expose] noncomputable def heSgK : List CFSG.Sporadic.He.J :=
  heQp.map fun p => (slpElts CFSG.Sporadic.He.a CFSG.Sporadic.He.b heProg).getD p.1 1

@[expose] noncomputable def heOtK : Array (OmegaData (List (List Nat))) :=
  #[omK (HeK.Ot.getD 0 default), omK (HeK.Ot.getD 1 default), omK (HeK.Ot.getD 2 default),
    omK (HeK.Ot.getD 3 default), omK (HeK.Ot.getD 4 default), omK (HeK.Ot.getD 5 default),
    omK (HeK.Ot.getD 6 default), omK (HeK.Ot.getD 7 default), omK (HeK.Ot.getD 8 default),
    omK (HeK.Ot.getD 9 default), omK (HeK.Ot.getD 10 default)]

end CFSG.QuasithinUnique.Ch1.SporLat.He

end
