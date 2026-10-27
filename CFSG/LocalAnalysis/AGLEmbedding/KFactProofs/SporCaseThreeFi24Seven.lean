module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCubic
public import CFSG.Sporadic.Fi24.Simple
public import Certificates.Certificate9508

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding.SporCubic


theorem sporCaseThreePrimeData_Fi24_seven [Finite (NativeSporadic.Carrier .Fi24Prime)]
    [Fact (Nat.Prime 7)] : SporCaseThreePrimeData (NativeSporadic.Carrier .Fi24Prime) 7 := by
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ :=
    (spec3 781).cubic_of_check fi24Sylow7HData Certificates.certificate9508
  exact sporCaseThreePrimeData_of_cubic (X := NativeSporadic.Fi24prime) hx hy hz hzx hzy hQ
    (by rw [CFSG.Sporadic.Fi24.card_Fi24prime]; norm_num) hhx hhy hhz (by decide +revert)

end CFSG.AGLEmbedding
