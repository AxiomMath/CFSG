module

public import CFSG.CGT.PushingUpLit.T2KR.Fus613Final
public import CFSG.CGT.PushingUpLit.T2KR.P53NatFinal
public import CFSG.CGT.PushingUpLit.T2KR.Sec47Gen
public import CFSG.CGT.PushingUpLit.T2KR.Sec66Final
public import CFSG.CGT.PushingUpLit.T2KR.TorusFinal
public import CFSG.CGT.PushingUpLit.SolomonTimmesfeld

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)
open CFSG.Assembly.RankThreeEven (projSL projSp)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace T2Hyp

variable {L M : Subgroup G} {n : ℕ}

theorem gen4 (h : T2Hyp G L M n) (hgen : CFSG.GH74.SectionalTwoRankLE G 4) :
    n = 2 ∧ CFSG.GH74.sectionalTwoRank G = 4 := by
  have hV := h.natBlock.isElemAbelian_blockU
  have hcard : Nat.card ↥(blockU L) = (2 ^ n) ^ 2 * Nat.card ↥(blockZ L) := h.natBlock.card_blockU
  have hZ : 1 ≤ Nat.card ↥(blockZ L) := Nat.card_pos
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have h16 : 16 ≤ Nat.card ↥(blockU L) := by
    rw [hcard]
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
      _ = (2 ^ n) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (2 ^ n) ^ 2 * Nat.card ↥(blockZ L) := Nat.mul_le_mul_left _ hZ
  have hle : Nat.card ↥(blockU L) ≤ 2 ^ 4 := hgen.card_le_of_elementary _ hV
  have hn : n = 2 := by
    by_contra hne
    have h3 : 3 ≤ n := by have := h.two_le; omega
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    have h64 : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
    have : (2 ^ n) ^ 2 ≤ Nat.card ↥(blockU L) := by
      rw [hcard]
      calc (2 ^ n) ^ 2 = (2 ^ n) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (2 ^ n) ^ 2 * Nat.card ↥(blockZ L) := Nat.mul_le_mul_left _ hZ
    omega
  refine ⟨hn, le_antisymm (CFSG.GH74.sectionalTwoRank_le_iff.2 hgen) ?_⟩
  by_contra hlt
  have h3 : CFSG.GH74.sectionalTwoRank G ≤ 3 := by omega
  have hle3 := (CFSG.GH74.sectionalTwoRank_le_iff.1 h3).card_le_of_elementary _ hV
  omega

end T2Hyp

theorem aschbacherTheoremTwoK_of_inputs (hE1 : FooteNonsolvableSimple)
    (hE2 : SolomonAlternatingBlockK) (hE5 : Aschbacher78OneGen)
    (hST : SolK.SolomonTimmesfeldTight) (hOrd : SolK.TightSmallGroupOrders)
    (h25 : Asc76Lemma25) (hGold : CFSG.CGT.Timmesfeld75.Goldschmidt1974)
    (hbhs : BHSLocalCStar) (h616 : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixSixteenNormal)
    (hCoreNat : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixThreeCoreNat)
    (hBS : T2KR.P53.BenderSuzukiStatement)
    (h55 : Print55) (hL214 : CFSG.CGT.Timmesfeld75.Lemma214) (hSz : T2KR.SzTwoPointTorus)
    (hSCL : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (hList : CFSG.CGT.Timmesfeld75.ListWCIdentification) : AschbacherTheoremTwoK := by
  have h53 : Print53 := T2KR.P53.print53_of_natCore hbhs h616 hCoreNat hBS hE2
  have hE8 : SolomonTimmesfeldTight := solomonTimmesfeldTight_of_solK hST hOrd
  have hE5' : Aschbacher78One := aschbacher78One_of_gen hE5
  have hCamp : Print47Campbell := print47Campbell_of_gen hE1 hE8 h25 hE5
  have hFinal : Print47Final := print47Final_of_gen hE1 hE8 h25 hE5
  intro G _ _ hK hs hc L M hX hmax hLM hsub huniq n hn hnat
  have h : T2Hyp G L M n := ⟨hK, hs, hc, hX, hmax, hLM, hsub, huniq, hn, hnat⟩
  by_cases hgen : CFSG.GH74.SectionalTwoRankLE G 4
  · exact Or.inr (Or.inr (h.gen4 hgen))
  by_cases hL3 : Nonempty (G ≃* projSL 3 (GaloisField 2 n))
  · exact Or.inl hL3
  by_cases hSp : Nonempty (G ≃* projSp 2 (GaloisField 2 n))
  · exact Or.inr (Or.inl hSp)
  exfalso
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 M
  have hs4 := h.sec4 hE1 hE5' hE8 h25 hCamp hFinal hT hgen hL3 hSp
  have hs6 := T2Hyp.sec6 hs4 hE1
    (h.five_one hE1 hE2 hE5' hE8 h25 hCamp hFinal h53 h55 hT hgen hL3 hSp)
  obtain ⟨D, hD⟩ := h.exists_isD
  obtain ⟨g, hg⟩ := T2Hyp.sit64 (print64_of_goldschmidt hGold) hs6 hD
  exact T2KR.print65_of_leaves hE1 (T2KR.print65Torus_of_lemma214 hL214 hSz)
    (T2KR.print66D1_of_list hE1 hSCL hList) T2KR.print611Gen4
    (T2KR.print612_of_614 (T2KR.print614_of_613 T2KR.P613.print613)) G L M T n D g hg

end CFSG.CGT.PushingUpLit.T2K
