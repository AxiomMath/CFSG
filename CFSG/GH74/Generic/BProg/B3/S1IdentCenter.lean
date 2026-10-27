module

public import CFSG.GH74.Generic.BProg.B2.L3Cover
public import CFSG.GH74.Generic.BProg.B1.Stage3aRank

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1IdentCenter

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover Subgroup
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.Generic.BProg.B2
open scoped MatrixGroups

theorem odd_center_of_qShape3
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (h : QShape3 (J ⧸ center J)) : Odd (Nat.card (center J)) := by
  obtain ⟨p, f, hp, hp2, h3, hL | hU⟩ := h
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel hL (by decide)
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = p ^ f := Fintype.card_eq_nat_card.trans hK
    have hoddq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hodd : Odd (Nat.card (hopfMultiplier PSL(3, K))) := by
      refine L3Cover.odd_card_hopf_psl3 (by omega) ?_
      intro h4
      rw [hcard] at h4
      rw [h4] at hoddq
      exact absurd hoddq (by decide)
    exact Odd.of_dvd_nat hodd (L2Cover.card_center_dvd_card_hopfMultiplier_qs hq
      (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm))
  · obtain ⟨⟨hp', hf, -, hne⟩, K, _, _, hK, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessNative.classical_of_lieModel hU (by decide)
    exact Odd.of_dvd_nat (L3Cover.odd_card_hopf_psu3 hp hK hf hne)
      (L2Cover.card_center_dvd_card_hopfMultiplier_qs hq e)

theorem odd_center_of_qShape3SD
    {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (h : B1.QShape3SD (J ⧸ center J)) : Odd (Nat.card (center J)) :=
  odd_center_of_qShape3 hq h.qShape3

end S1IdentCenter

end CFSG.GH74.Generic.BProg.B3
