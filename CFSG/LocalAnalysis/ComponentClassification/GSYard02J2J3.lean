module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Simple
public import Certificates.Certificate320201
public import Certificates.Certificate320202
public import CFSG.Sporadic.Schreier.PairJ3Faithful

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup CFSG.Sporadic.Schreier

theorem sylowFourJoined_j2P :
    SylowFourJoined ↥j2P :=
  Certificates.certificate320201

theorem leafJ2_holds :
    LeafSporadic .J2 := by
  intro X _ _ _ _ hX
  obtain ⟨e⟩ := hX
  exact SylowFourJoined.of_mulEquiv (e.trans CFSG.Sporadic.Schreier.j2PermEquiv).symm
    sylowFourJoined_j2P

theorem sylowFourJoined_j3P :
    SylowFourJoined ↥j3P :=
  Certificates.certificate320202

theorem leafJ3_holds :
    LeafSporadic .J3 := by
  intro X _ _ _ _ hX
  obtain ⟨e⟩ := hX
  exact SylowFourJoined.of_mulEquiv (e.trans CFSG.Sporadic.Schreier.j3PermEquiv).symm
    sylowFourJoined_j3P

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
