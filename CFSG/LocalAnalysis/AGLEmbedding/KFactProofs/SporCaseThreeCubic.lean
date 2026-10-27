module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import CFSG.Sporadic.ON
public import Certificates.Certificate9416
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.AGLEmbedding

open CFSG.RankThree.PartOne.StrongP CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.AGLEmbedding.SporCubic
open scoped commutatorElement

theorem sporCaseThreePrimeData_of_cubic {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {x y h : X} (hxp : x ^ p = 1) (hyp : y ^ p = 1) (hz1 : ⁅x, y⁆ ≠ 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hQ : Nat.card (Subgroup.closure ({x, y} : Set X)) = p ^ 3) (hS : ¬ p ^ 4 ∣ Nat.card X)
    {a b c d k l μ : ℕ} (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l) (hhz : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ μ)
    (hdet : ((μ : ZMod p) * a - 1) * ((μ : ZMod p) * d - 1) - (μ : ZMod p) ^ 2 * b * c ≠ 0) :
    SporCaseThreePrimeData X p :=
  sporCaseThreePrimeData_of_noncomm hS
    (CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Fact.out hxp hyp hz1 hQ)
    (kernelTrivialAt_of_cubic hxp hyp hz1 hzx hzy hQ hS hhx hhy hhz hdet)

section McL


theorem sporCaseThreePrimeData_McL_five [Finite (NativeSporadic.Carrier .McL)]
    [Fact (Nat.Prime 5)] : SporCaseThreePrimeData (NativeSporadic.Carrier .McL) 5 := by
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ :=
    (spec3 21).cubic_of_check mclSylow5HData Certificates.certificate9416.1
  exact sporCaseThreePrimeData_of_cubic (X := NativeSporadic.McL) hx hy hz hzx hzy hQ
    (by rw [CFSG.Sporadic.McL.card_McL]; norm_num) hhx hhy hhz (by decide +revert)

end McL

section Co2


theorem sporCaseThreePrimeData_Co2_five [Finite (NativeSporadic.Carrier .Co2)]
    [Fact (Nat.Prime 5)] : SporCaseThreePrimeData (NativeSporadic.Carrier .Co2) 5 := by
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ :=
    (spec2 22).cubic_of_check co2Sylow5HData Certificates.certificate9416.2.1
  exact sporCaseThreePrimeData_of_cubic (X := NativeSporadic.Co2) hx hy hz hzx hzy hQ
    (by rw [CFSG.Sporadic.Co2.card_Co2]; norm_num) hhx hhy hhz (by decide +revert)

end Co2

section Co3


theorem sporCaseThreePrimeData_Co3_five [Finite (NativeSporadic.Carrier .Co3)]
    [Fact (Nat.Prime 5)] : SporCaseThreePrimeData (NativeSporadic.Carrier .Co3) 5 := by
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ :=
    (spec2 22).cubic_of_check co3Sylow5HData Certificates.certificate9416.2.2.1
  exact sporCaseThreePrimeData_of_cubic (X := NativeSporadic.Co3) hx hy hz hzx hzy hQ
    (by rw [CFSG.Sporadic.Co3.card_Co3]; norm_num) hhx hhy hhz (by decide +revert)

end Co3

section Th


theorem sporCaseThreePrimeData_Th_five [Finite (NativeSporadic.Carrier .Th)] [Fact (Nat.Prime 5)] :
    SporCaseThreePrimeData (NativeSporadic.Carrier .Th) 5 := by
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ :=
    (spec2 248).cubic_of_check thSylow5HData Certificates.certificate9416.2.2.2.1
  exact sporCaseThreePrimeData_of_cubic (X := NativeSporadic.Th) hx hy hz hzx hzy hQ
    (by rw [CFSG.RankThree.PartOne.CTP.card_Th]; norm_num) hhx hhy hhz (by decide +revert)

end Th

section ON


theorem sporCaseThreePrimeData_ON_seven [Finite (NativeSporadic.Carrier .ONan)]
    [Fact (Nat.Prime 7)] : SporCaseThreePrimeData (NativeSporadic.Carrier .ONan) 7 := by
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ :=
    (spec3 154).cubic_of_check onSylow7HData Certificates.certificate9416.2.2.2.2
  exact sporCaseThreePrimeData_of_cubic (X := NativeSporadic.ON) hx hy hz hzx hzy hQ
    (by rw [CFSG.Sporadic.ON.card_ON]; norm_num) hhx hhy hhz (by decide +revert)

end ON

end CFSG.AGLEmbedding
