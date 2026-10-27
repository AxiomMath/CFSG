module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLData
public import Certificates.Data.CFSGNative.Co3Schreier.Orbit
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLCheckInputs
public import Certificates.Certificate9314
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLData
public meta import Certificates.Data.CFSGNative.Co3Schreier.Orbit
public meta import Certificates.Data.CFSGNative.Schreier.SetOrbit
public import Mathlib

public section

namespace CFSG.ClassicalInvolution

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native
  CFSG.ClassicalInvolution.McLData

namespace McLProof

theorem tables_check :
    permOK 275 Ta = true ∧ permOK 275 Tb = true ∧ involOK 275 Ta = true ∧
      invOK 275 Ta (invT 275 Ta) = true := by
  exact Certificates.certificate9314.1

theorem kgens_check :
    Nat.card (genOf 275 kgens) = 40320 ∧ kgens.all (permOK 275) = true ∧
      kgens.all (fun g => invOK 275 g (invT 275 g)) = true ∧
      kgens.all (fun g => commTT 275 g Ta) = true ∧ kgens.length = 2 ∧
      (tblEq 275 Ta (wordTbl 275 kgens [1, 1, 1, 1, 1, 1, 1]) = true ∧
        permOK 275 (wordTbl 275 kgens [1, 1, 1, 1, 1, 1, 1]) = true) := by
  exact Certificates.certificate9314.2.1

theorem words_check :
    (∀ w ∈ kWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) ∧ (∀ w ∈ sWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) ∧
      (∀ w ∈ conjWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) ∧
      (∀ p ∈ repData, (∀ l ∈ p.1, 1 ≤ l ∧ l ≤ 2) ∧ ∀ cw ∈ p.2, ∀ l ∈ cw, 1 ≤ l ∧ l ≤ 2) ∧
      sgens.all (permOK 275) = true ∧ repTbls.all (permOK 275) = true ∧
      (conjWords.map (wordTbl 275 abT)).all (fun c => permOK 275 c && invOK 275 c (invT 275 c)) =
        true ∧
      (repData.all fun p => p.2.all fun cw => permOK 275 (wordTbl 275 kgens cw) &&
        invOK 275 (wordTbl 275 kgens cw) (invT 275 (wordTbl 275 kgens cw))) = true ∧
      (repGens.all fun gs => gs.all (permOK 275)) = true := by
  exact Certificates.certificate9314.2.2.1

theorem sylow_check :
    enumOK 275 capK 128 sgens = true ∧ sylowCoverOK = true := by
  exact Certificates.certificate9314.2.2.2.1

theorem orbit_check :
    translatesOK abArr fixZ orbZ.1 orbZ.2.1 orbZ.2.2 = true ∧ keysSortedOK orbZ.1 = true ∧
      orbZ.1.size = 22275 := by
  exact Certificates.certificate9314.2.2.2.2.1

theorem cover_check :
    ∀ x ∈ genOf 275 kgens, x = 1 ∨ x = tp 275 Ta ∨
      ∃ r ∈ repTbls.map (tp 275), ∃ c ∈ genOf 275 kgens, x = c * r * c⁻¹ := by
  exact Certificates.certificate9314.2.2.2.2.2.1

theorem gen_check :
    ∀ gs ∈ repGens, genOf 275 kgens ≤ genOf 275 gs := by
  exact Certificates.certificate9314.2.2.2.2.2.2.1

theorem comm_check : commOK = true ∧ kx ∈ kgens ∧ ky ∈ kgens := by
  exact Certificates.certificate9314.2.2.2.2.2.2.2

end McLProof

end CFSG.ClassicalInvolution
