module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Bridge1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Bridge2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Clos
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114CoreTop
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I112Ctx
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA.I114

variable {G : Type} [Group G] [Finite G]

theorem i114At_of_facts (Tb : Tables112) (TL : TableL2) (TT : Tables112Types)
    (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G)
    (hFA : I114FactA) (hFB : I114FactB) (hFC : I114FactC) : I114At G := by
  intro X B K hXK hBX hBmax hK hnBK hcat hZ T hTcl hTp hBT
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hB3 : IsElemAbelian 3 B := hBmax.1
  have hr : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B :=
    twoLocalRank_le_of_glaIsBmax hp hBmax
  obtain ⟨hXne, hQK, hQcore, hBel, hrankQ, hLbar, hnLQ⟩ :=
    i112c_bar hsimple hKP hp hp2 hB3 hBX hr hK hnBK
  obtain ⟨-, hrel, haut, ⟨hZE, -⟩, htype⟩ :=
    i112f_core Tb TL TT hQK hp hp2 hQcore hBel hrankQ hLbar hnLQ
  have hKc : CFSG.Open.IsComponentOf (barX 3 X K) ⊤ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1314.isComponentOf_barX_of_glaPComponent hK
  have hBbar : IsElemAbelian 3 (barX 3 X B) := isElemAbelian_barX hB3
  have hZ' : Nat.card (Subgroup.center ↥(barX 3 X K)) = 3 := by
    rw [← card_center_of_mulEquiv (quotEquivBarX hp hK.1 hK.2.1)]
    exact hZ
  have hcat' : catalogIs (↥(barX 3 X K) ⧸ Subgroup.center ↥(barX 3 X K)) S9.isL3char2 :=
    catalogIs_center_quot_of_mulEquiv (quotEquivBarX hp hK.1 hK.2.1) hcat
  have hdisj : IsLTwoOddPow ↥(barX 3 X K) ∨
      CFSG.HardMathSupport.Solomon.LocalBalance.IsHatSix ↥(barX 3 X K) ∨
      IsHatSeven ↥(barX 3 X K) ∨ IsHatMTwentyTwo ↥(barX 3 X K) ∨ IsSLThreeExc ↥(barX 3 X K) ∨
      IsSUThreeExc ↥(barX 3 X K) := by
    rcases htype with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hSL : IsSLThreeExc ↥(barX 3 X K) := hFC _ hZ' hcat' hdisj
  have hTbot : (T.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) = ⊥ :=
    core_T_eq_bot hBbar hrel
      (fun b hb hbN => elemCommute_cj_of_mem hBbar hKc hb hbN)
      (hmax_of_rank hp hBbar hrankQ) hZ' (hFA _ hZ' hcat') (hFB _ hSL hcat')
      (fun H hH => card_le_nine_of_pRank_le_two haut hH)
      (map_subgroupOf_le_Sbar hK.1 hBX hTcl) (isPGroup_map_subgroupOf hTp)
      (barX_le_normalizer_map hBT)
  exact le_glaPPrimeCoreOf_closureIn hp hK.1 hBX hTcl hTbot

end CFSG.LocalAnalysis.GLTheoremA
