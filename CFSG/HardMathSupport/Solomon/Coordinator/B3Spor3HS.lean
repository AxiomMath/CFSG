module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Kit
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Model
public import CFSG.Sporadic.Schreier.PairHSFaithful
public import Certificates.Certificate13514
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3
  CFSG.Sporadic.Schreier

theorem b3Phi_hs :
    ∀ x : ↥hsP, orderOf x = 3 → B3Phi 3 (Subgroup.centralizer ({x} : Set _)) := by
  have h := Certificates.certificate13514
  obtain ⟨hvA, hvB⟩ := check_valid h
  exact b3Phi_centralizer_of_perm _
    (check_sound hsS3Data (CFSG.RankThree.Native.rep_of_validA hvA)
      (CFSG.RankThree.Native.rep_of_validA hvB) h)

theorem b3SporPair_HS_three
    (hbr : SporadicBridges)
    (hOut : SporadicOuterLeTwo) : B3SporPair .HS 3 :=
  b3SporPair_of_model hOut ↥hsP ⟨hsPermEquiv.symm.trans (hbr .HS).some⟩ b3Phi_hs

end CFSG.HardMathSupport.Solomon.Coordinator
