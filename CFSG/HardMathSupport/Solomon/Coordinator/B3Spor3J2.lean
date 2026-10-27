module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Kit
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Model
public import CFSG.Sporadic.Schreier.PairJ2Faithful
public import Certificates.Certificate13513
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3
  CFSG.Sporadic.Schreier

theorem b3Phi_j2 :
    ∀ x : ↥j2P, orderOf x = 3 → B3Phi 3 (Subgroup.centralizer ({x} : Set _)) := by
  have h := Certificates.certificate13513
  obtain ⟨hvA, hvB⟩ := check_valid h
  exact b3Phi_centralizer_of_perm _
    (check_sound j2S3Data (CFSG.RankThree.Native.rep_of_validA hvA) (CFSG.RankThree.Native.rep_of_validA hvB) h)

theorem b3SporPair_J2_three
    (hbr : SporadicBridges)
    (hOut : SporadicOuterLeTwo) : B3SporPair .J2 3 :=
  b3SporPair_of_model hOut ↥j2P ⟨j2PermEquiv.symm.trans (hbr .J2).some⟩ b3Phi_j2

end CFSG.HardMathSupport.Solomon.Coordinator
