module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporRot
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Data.WCSporRot
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenCensusRot
import CFSG.Sporadic.Th.Max3.AllConjFinal
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic CFSG.Open CFSG.SectionRank CFSG.SectionRank.Native

set_option maxRecDepth 4000

theorem wcOn_Th_seven_of_check_aux
    [Finite CFSG.Blueprint.NativeSporadic.Th]
    (h : (ops2 248).squareCheck thSevenRot = true) : WCOn 7 CFSG.Blueprint.NativeSporadic.Th := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, y, g, hx, hy, hxy, hQ, hgx, hgy⟩ := (spec2 248).square_of_check thSevenRot h
  have hcard : Nat.card CFSG.Blueprint.NativeSporadic.Th = 90745943887872000 :=
    (Nat.card_congr CFSG.Sporadic.Th.thEquivJ.toEquiv).trans CFSG.Sporadic.Th.Max3.natCard_J
  exact WCOn.of_square_witness (p := 7) (K := CFSG.Blueprint.NativeSporadic.Th) hx hy hxy hQ
    (by rw [hcard]; decide) hgx hgy (by decide +revert)

theorem wcOn_Th_seven_of_check
    [Finite (Carrier .Th)]
    (h : (ops2 248).squareCheck thSevenRot = true) : WCOn 7 (Carrier .Th) :=
  wcOn_Th_seven_of_check_aux h

theorem wcOn_Suz_five_of_check_aux
    [Finite CFSG.Blueprint.NativeSporadic.Suz]
    (h : (ops3 64).squareCheck suzFiveRot = true) : WCOn 5 CFSG.Blueprint.NativeSporadic.Suz := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, y, g, hx, hy, hxy, hQ, hgx, hgy⟩ := (spec3 64).square_of_check suzFiveRot h
  have hcard : Nat.card CFSG.Blueprint.NativeSporadic.Suz = 448345497600 :=
    CFSG.Sporadic.Suz.card_Suz
  exact WCOn.of_square_witness (p := 5) (K := CFSG.Blueprint.NativeSporadic.Suz) hx hy hxy hQ
    (by rw [hcard]; decide) hgx hgy (by decide +revert)

theorem wcOn_Suz_five_of_check [Finite (Carrier .Suz)]
    (h : (ops3 64).squareCheck suzFiveRot = true) : WCOn 5 (Carrier .Suz) :=
  wcOn_Suz_five_of_check_aux h

theorem wcOn_B_seven_of_check_aux
    [Finite CFSG.Blueprint.NativeSporadic.B]
    (h : ∃ x y h k : CFSG.Blueprint.NativeSporadic.B,
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.RotSevenData x y h k) :
    WCOn 7 CFSG.Blueprint.NativeSporadic.B := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, y, h3, g, D⟩ := h
  have hy : y ^ 7 = 1 := by rw [← D.hx, conj_pow, D.pow_x, mul_one, mul_inv_cancel]
  have hcard : Nat.card CFSG.Blueprint.NativeSporadic.B = 4154781481226426191177580544000000 := by
    rw [CFSG.Monster.Existence.card_nativeB]
    decide
  exact WCOn.of_square_witness (p := 7) (K := CFSG.Blueprint.NativeSporadic.B) (a := 6) (b := 1)
    (c := 5) (d := 1) D.pow_x hy D.comm D.card (by rw [hcard]; decide)
    (by rw [pow_one]; exact D.kx) (by rw [pow_one]; exact D.ky) (by decide +revert)

theorem wcOn_B_seven_of_check
    [Finite (Carrier .B)]
    (h : ∃ x y h k : CFSG.Blueprint.NativeSporadic.B,
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.RotSevenData x y h k) :
    WCOn 7 (Carrier .B) :=
  wcOn_B_seven_of_check_aux h

@[expose] def RotationDatum (p : ℕ) (K : Type) [Group K] : Prop :=
  ∃ a b g : K, a ≠ 1 ∧ a ^ p = 1 ∧ a * b = b * a ∧ g * a * g⁻¹ = b ∧ g * b * g⁻¹ = a⁻¹

theorem wcOn_eleven_of_rotationDatum {K : Type} [Group K] [Finite K] (h : RotationDatum 11 K)
    (h3 : ¬ 11 ^ 3 ∣ Nat.card K) : WCOn 11 K := by
  obtain ⟨a, b, g, ha1, ha, hab, hga, hgb⟩ := h
  exact wcOn_eleven_of_rotation ha1 ha hab hga hgb h3

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
