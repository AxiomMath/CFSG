module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankAlt
import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Center
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycMain

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

theorem pRank_add_one_le_of_quot_center_alternating {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) {n : ℕ} (hn : 5 ≤ n)
    (hA : Nonempty ((Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin n)))
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) :
    CFSG.Open.pRank d (⊤ : Subgroup Y) + 1 ≤ max 2 (CFSG.Open.pRank 3 (⊤ : Subgroup Y)) ∧
      ¬ d ∣ Nat.card (Subgroup.center Y) := by
  have hthree : CFSG.Open.pRank 3 (⊤ : Subgroup Y) = n / 3 :=
    CFSG.LocalAnalysis.RankThreeUC.S15.lieOddRankAlt_holds Y hq n hn hA 3
      (by norm_num) (by norm_num)
  have hdrank : CFSG.Open.pRank d (⊤ : Subgroup Y) = n / d :=
    CFSG.LocalAnalysis.RankThreeUC.S15.lieOddRankAlt_holds Y hq n hn hA d hd (by omega)
  constructor
  · rw [hthree, hdrank]
    have hdiv : n / d ≤ n / 5 := Nat.div_le_div_left hd5 (by norm_num)
    have harith : n / 5 + 1 ≤ max 2 (n / 3) := by omega
    omega
  · intro hdvd
    haveI : Group.IsPerfect Y := Group.IsPerfect.mk hq.1
    have hcf :=
      CFSG.HardMathSupport.Timmesfeld.Tables.Alt.center_facts hn hA.some hd (by omega)
    exact absurd (hcf.2 hdvd).1 (by omega)

theorem quot_center_alternating_of_mulEquiv {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) {n : ℕ} (e : Y ≃* alternatingGroup (Fin n)) :
    5 ≤ n ∧ Subgroup.center Y = ⊥ ∧
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin n)) := by
  haveI : Group.IsPerfect Y := Group.IsPerfect.mk hq.1
  haveI : Nontrivial (Y ⧸ Subgroup.center Y) := hq.2.toNontrivial
  haveI : Nontrivial Y := (QuotientGroup.mk'_surjective (Subgroup.center Y)).nontrivial
  have h5 : 5 ≤ n :=
    CFSG.AGLEmbedding.BlockCyc.five_le_of_perfect_mulEquiv_alternatingGroup e
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using h5)
  haveI : IsSimpleGroup Y := MulEquiv.isSimpleGroup e
  have hZ : Subgroup.center Y = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center Y) with h | h
    · exact h
    · exfalso
      have hcomm : IsMulCommutative Y := Subgroup.center_eq_top_iff.mp h
      exact (Group.IsPerfect.not_isMulCommutative (G := Y)) hcomm
  exact ⟨h5, hZ,
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
