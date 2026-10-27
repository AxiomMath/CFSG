module

public import CFSG.LieType.Chevalley.RootOps.Cert.G2Comm
public import CFSG.LieType.Chevalley.RootOps.Cert.F4Comm
public import CFSG.LieType.Chevalley.RootOps.Cert.D4Comm
public import CFSG.LieType.Chevalley.RootOps.Cert.E6Comm
public import CFSG.LieType.Chevalley.RootOps.Cert.E7Comm
public import CFSG.LieType.Chevalley.RootOps.Cert.E8Comm
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.BorelTits RootOps

@[expose] def RootOps.repsOf : Tag → List (ℕ × ℕ × List Factor)
  | .G2 => g2Reps
  | .F4 => f4Reps
  | .D4 => d4Reps
  | .E6 => e6Reps
  | .E7 => e7Reps
  | .E8 => e8Reps

@[expose] def RootOps.coverOf : Tag → List ℕ
  | .G2 => g2Cover
  | .F4 => f4Cover
  | .D4 => d4Cover
  | .E6 => e6Cover
  | .E7 => e7Cover
  | .E8 => e8Cover

theorem RootOps.repsCheck_repsOf : ∀ τ : Tag, repsCheck τ (repsOf τ) = true
  | .G2 => g2_repsCheck
  | .F4 => f4_repsCheck
  | .D4 => d4_repsCheck
  | .E6 => e6_repsCheck
  | .E7 => e7_repsCheck
  | .E8 => e8_repsCheck

theorem RootOps.coverCheck_coverOf : ∀ τ : Tag, coverCheck τ (repsOf τ) (coverOf τ) = true
  | .G2 => g2_coverCheck
  | .F4 => f4_coverCheck
  | .D4 => d4_coverCheck
  | .E6 => e6_coverCheck
  | .E7 => e7_coverCheck
  | .E8 => e8_coverCheck

theorem commContained_simpleRoot (τ : Tag) (K : Type) [Field K] (i : Fin τ.rank) (β : Root τ)
    (hβ : 0 < height β.1) (hne : β ≠ simpleRoot τ i) :
    (rootOperatorFamily τ).CommContained K (simpleRoot τ i) β :=
  commContained_of_checks K (RootOps.dataChecks τ).valid (RootOps.dataChecks τ).tab
    (repsCheck_repsOf τ) (coverCheck_coverOf τ) i β hβ hne

theorem holds_adjointGroup_tag (τ : Tag) (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] : Holds (adjointGroup τ K) p :=
  (rootOperatorFamily τ).holds_adjointGroup_of_family K
    (fun i β hβ hne => commContained_simpleRoot τ K i β hβ hne) p

end CFSG.LieType.Chevalley
