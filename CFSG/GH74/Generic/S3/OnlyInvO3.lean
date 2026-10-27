module

public import CFSG.GH74.Generic.S3.OnlyInvO2
public import CFSG.GH74.Generic.S3.Main19
public import CFSG.GH74.Orders.LieType
public import CFSG.LocalAnalysis.ComponentInitial.BlockAschbacherTheorem5
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Asc77.HypOmegaBasic
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Q3.ModelCenter
public import CFSG.ClassicalInvolution.RouteD.LocalLift
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma26
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2More
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial

theorem prod_Icc_two_three (f : ℕ → ℕ) : (∏ i ∈ Finset.Icc 2 3, f i) = f 2 * f 3 := by
  have e : Finset.Icc 2 3 = {2, 3} := by decide
  rw [e]; simp

theorem le_ordA_two {q : ℕ} (hq : 5 ≤ q) : 505 ≤ CFSG.Open.ordA 2 q := by
  unfold CFSG.Open.ordA
  rw [show (2 + 1 : ℕ) = 3 from rfl, prod_Icc_two_three]
  have hg : 0 < Nat.gcd (2 + 1) (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg3 : Nat.gcd (2 + 1) (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  rw [Nat.le_div_iff_mul_le hg]
  have h3 : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 25 ≤ q ^ 2 := by
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have e1 : 24 ≤ q ^ 2 - 1 := by omega
  have e2 : 124 ≤ q ^ 3 - 1 := by omega
  have e3 : 24 * 124 ≤ (q ^ 2 - 1) * (q ^ 3 - 1) := Nat.mul_le_mul e1 e2
  have e4 : 125 * (24 * 124) ≤ q ^ (2 * (2 + 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    have : q ^ (2 * (2 + 1) / 2) = q ^ 3 := rfl
    rw [this]; exact Nat.mul_le_mul h3 e3
  calc 505 * Nat.gcd (2 + 1) (q - 1) ≤ 505 * 3 := Nat.mul_le_mul_left _ hg3
    _ ≤ 125 * (24 * 124) := by norm_num
    _ ≤ _ := e4

theorem le_ordTwistedA_two {q : ℕ} (hq : 5 ≤ q) : 505 ≤ CFSG.Open.ordTwistedA 2 q := by
  unfold CFSG.Open.ordTwistedA
  rw [show (2 + 1 : ℕ) = 3 from rfl, prod_Icc_two_three]
  have hg : 0 < Nat.gcd (2 + 1) (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg3 : Nat.gcd (2 + 1) (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  rw [Nat.le_div_iff_mul_le hg]
  have h3 : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 25 ≤ q ^ 2 := by
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have a2 : ((q : ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
    have : ((q : ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 : ℕ) : ℤ) - 1 := by push_cast; ring
    rw [this]; omega
  have a3 : ((q : ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
    have : ((q : ℤ) ^ 3 - (-1) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this]; exact Int.toNat_natCast _
  rw [a2, a3]
  have e1 : 24 ≤ q ^ 2 - 1 := by omega
  have e2 : 126 ≤ q ^ 3 + 1 := by omega
  have e3 : 24 * 126 ≤ (q ^ 2 - 1) * (q ^ 3 + 1) := Nat.mul_le_mul e1 e2
  have e4 : 125 * (24 * 126) ≤ q ^ (2 * (2 + 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    have : q ^ (2 * (2 + 1) / 2) = q ^ 3 := rfl
    rw [this]; exact Nat.mul_le_mul h3 e3
  calc 505 * Nat.gcd (2 + 1) (q + 1) ≤ 505 * 3 := Nat.mul_le_mul_left _ hg3
    _ ≤ 125 * (24 * 126) := by norm_num
    _ ≤ _ := e4

theorem ordA_one_eight : CFSG.Open.ordA 1 8 = 504 := by decide

theorem le_card_of_l3 {K : Type} [Group K] {p f : ℕ} (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f)
    (h : LieModel K .PSL 3 p f ∨ LieModel K .PSU 3 p f) : 505 ≤ Nat.card K := by
  rcases h with hm | hm
  · rw [card_of_lieModel_PSL (by norm_num) hm]
    exact le_ordA_two hq5
  · rw [card_of_lieModel_PSU (by norm_num) hp2 hm]
    exact le_ordTwistedA_two hq5

end CFSG.GH74.Generic.S3
