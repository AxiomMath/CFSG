module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporCore
import all CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall3
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import CFSG.Sporadic.ON
public import Certificates.Certificate9416

public section

namespace CFSG.AGLEmbedding

open CFSG.RankThree.PartOne.StrongP CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.AGLEmbedding.SporCubic
open scoped commutatorElement

theorem sporMidAt_of_cubic {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {x y h : X} (hxp : x ^ p = 1) (hyp : y ^ p = 1) (hz1 : ⁅x, y⁆ ≠ 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hQ : Nat.card (Subgroup.closure ({x, y} : Set X)) = p ^ 3) (hS : ¬ p ^ 4 ∣ Nat.card X)
    {a b c d k l μ : ℕ} (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l) (hhz : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ μ)
    (hdet : ((μ : ZMod p) * a - 1) * ((μ : ZMod p) * d - 1) - (μ : ZMod p) ^ 2 * b * c ≠ 0) :
    SporMidAt X p :=
  sporMidAt_of_noncomm hS
    (CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Fact.out hxp hyp hz1 hQ)
    (kernelTrivialAt_of_cubic hxp hyp hz1 hzx hzy hQ hS hhx hhy hhz hdet)

theorem sporMidAt_M12_three :
    SporMidAt (NativeSporadic.Carrier .M12) 3 := by
  have hc : Nat.card (NativeSporadic.Carrier .M12) = 95040 := CFSG.Sporadic.Mathieu.card_M12
  exact sporMidAt_of_noncomm (by rw [hc]; norm_num) hasNoncommPair_three_M12
    (kernelTrivialAt_of_odd (by norm_num) fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.M12_perfect_odd_cover_trivial π hπ hC hodd)

theorem sporMidAt_M24_three :
    SporMidAt (NativeSporadic.Carrier .M24) 3 := by
  have hc : Nat.card (NativeSporadic.Carrier .M24) = 244823040 := CFSG.Sporadic.Mathieu.card_M24
  exact sporMidAt_of_noncomm (by rw [hc]; norm_num) hasNoncommPair_three_M24
    (kernelTrivialAt_of_odd (by norm_num) fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.M24_perfect_odd_cover_trivial π hπ hC hodd)

theorem sporMidAt_J2_three :
    SporMidAt (NativeSporadic.Carrier .J2) 3 := by
  have hc : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
  exact sporMidAt_of_noncomm (by rw [hc]; norm_num) hasNoncommPair_three_J2
    (kernelTrivialAt_of_odd (by norm_num) fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.J2_perfect_odd_cover_trivial π hπ hC hodd)

theorem sporMidAt_J4_three :
    SporMidAt (NativeSporadic.Carrier .J4) 3 := by
  have hc : Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 :=
    CFSG.Sporadic.J4.card_J4
  exact sporMidAt_of_noncomm (by rw [hc]; norm_num) hasNoncommPair_three_J4
    (kernelTrivialAt_of_odd (by norm_num) fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.J4_perfect_odd_cover_trivial (dvd_of_eq CFSG.Sporadic.J4.card_J4) π hπ hC
        hodd)

theorem sporMidAt_J4_eleven :
    SporMidAt (NativeSporadic.Carrier .J4) 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hc : Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 :=
    CFSG.Sporadic.J4.card_J4
  exact sporMidAt_of_noncomm (by rw [hc]; norm_num) CFSG.RankThree.PartOne.CTP.hasNoncommPair_J4
    (kernelTrivialAt_of_odd (by norm_num) fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.J4_perfect_odd_cover_trivial (dvd_of_eq CFSG.Sporadic.J4.card_J4) π hπ hC
        hodd)

theorem sporMidAt_HS_five :
    SporMidAt (NativeSporadic.Carrier .HS) 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : Nat.card (NativeSporadic.Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
  exact sporMidAt_of_noncomm (by rw [hc]; norm_num) CFSG.RankThree.PartOne.CTP.hasNoncommPair_HS
    (kernelTrivialAt_of_odd (by norm_num) fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.HS_perfect_odd_cover_trivial π hπ hC hodd)

theorem sporMidAt_He_three :
    SporMidAt (NativeSporadic.Carrier .He) 3 := by
  have hc : Nat.card (NativeSporadic.Carrier .He) = 4030387200 := CFSG.Sporadic.He.card_He
  exact sporMidAt_of_noncomm (by rw [hc]; norm_num) hasNoncommPair_three_He
    (kernelTrivialAt_of_odd (by norm_num) fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.He_perfect_odd_cover_trivial π hπ hC hodd)

theorem sporMidAt_He_seven :
    SporMidAt (NativeSporadic.Carrier .He) 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hc : Nat.card (NativeSporadic.Carrier .He) = 4030387200 := CFSG.Sporadic.He.card_He
  exact sporMidAt_of_noncomm (by rw [hc]; norm_num) CFSG.RankThree.PartOne.CTP.hasNoncommPair_He
    (kernelTrivialAt_of_odd (by norm_num) fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.He_perfect_odd_cover_trivial π hπ hC hodd)

theorem sporMidAt_Ru_three :
    SporMidAt (NativeSporadic.Carrier .Ru) 3 := by
  have hc : Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 := CFSG.Sporadic.Ru.card_Ru
  exact sporMidAt_of_noncomm (by rw [hc]; norm_num) hasNoncommPair_three_Ru
    (kernelTrivialAt_of_odd (by norm_num) fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.Ru_perfect_odd_cover_trivial π hπ hC hodd)

theorem sporMidAt_Ru_five :
    SporMidAt (NativeSporadic.Carrier .Ru) 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 := CFSG.Sporadic.Ru.card_Ru
  exact sporMidAt_of_noncomm (by rw [hc]; norm_num) CFSG.RankThree.PartOne.CTP.hasNoncommPair_Ru
    (kernelTrivialAt_of_odd (by norm_num) fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.Ru_perfect_odd_cover_trivial π hπ hC hodd)

theorem sporMidAt_McL_five :
    SporMidAt (NativeSporadic.Carrier .McL) 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : Nat.card (NativeSporadic.Carrier .McL) = 898128000 := CFSG.Sporadic.McL.card_McL
  have : Finite (NativeSporadic.Carrier .McL) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ :=
    (spec3 21).cubic_of_check mclSylow5HData Certificates.certificate9416.1
  exact sporMidAt_of_cubic (X := NativeSporadic.McL) hx hy hz hzx hzy hQ
    (by rw [CFSG.Sporadic.McL.card_McL]; norm_num) hhx hhy hhz (by decide +revert)

theorem sporMidAt_Co2_five :
    SporMidAt (NativeSporadic.Carrier .Co2) 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : Nat.card (NativeSporadic.Carrier .Co2) = 42305421312000 := CFSG.Sporadic.Co2.card_Co2
  have : Finite (NativeSporadic.Carrier .Co2) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ :=
    (spec2 22).cubic_of_check co2Sylow5HData Certificates.certificate9416.2.1
  exact sporMidAt_of_cubic (X := NativeSporadic.Co2) hx hy hz hzx hzy hQ
    (by rw [CFSG.Sporadic.Co2.card_Co2]; norm_num) hhx hhy hhz (by decide +revert)

theorem sporMidAt_Co3_five :
    SporMidAt (NativeSporadic.Carrier .Co3) 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : Nat.card (NativeSporadic.Carrier .Co3) = 495766656000 := CFSG.Sporadic.Co3.card_Co3
  have : Finite (NativeSporadic.Carrier .Co3) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ :=
    (spec2 22).cubic_of_check co3Sylow5HData Certificates.certificate9416.2.2.1
  exact sporMidAt_of_cubic (X := NativeSporadic.Co3) hx hy hz hzx hzy hQ
    (by rw [CFSG.Sporadic.Co3.card_Co3]; norm_num) hhx hhy hhz (by decide +revert)

theorem sporMidAt_Th_five :
    SporMidAt (NativeSporadic.Carrier .Th) 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : Nat.card (NativeSporadic.Carrier .Th) = 90745943887872000 :=
    CFSG.RankThree.PartOne.CTP.card_Th
  have : Finite (NativeSporadic.Carrier .Th) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ :=
    (spec2 248).cubic_of_check thSylow5HData Certificates.certificate9416.2.2.2.1
  exact sporMidAt_of_cubic (X := NativeSporadic.Th) hx hy hz hzx hzy hQ
    (by rw [CFSG.RankThree.PartOne.CTP.card_Th]; norm_num) hhx hhy hhz (by decide +revert)

theorem sporMidAt_ON_seven :
    SporMidAt (NativeSporadic.Carrier .ONan) 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hc : Nat.card (NativeSporadic.Carrier .ONan) = 460815505920 := CFSG.Sporadic.ON.card_ON
  have : Finite (NativeSporadic.Carrier .ONan) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ :=
    (spec3 154).cubic_of_check onSylow7HData Certificates.certificate9416.2.2.2.2
  exact sporMidAt_of_cubic (X := NativeSporadic.ON) hx hy hz hzx hzy hQ
    (by rw [CFSG.Sporadic.ON.card_ON]; norm_num) hhx hhy hhz (by decide +revert)

end CFSG.AGLEmbedding
