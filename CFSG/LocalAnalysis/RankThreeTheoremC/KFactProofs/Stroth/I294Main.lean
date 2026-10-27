module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Lines
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Outer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Alt
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294DefChar
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Spor
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294Lemmas
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

theorem I294Cfg.noPSignalizer
    (hCore : CFSG.HardMathSupport.Timmesfeld.Coordinator.DefCharInnerCoreFree)
    (hK : KDOutDerived) (hO : I294OuterDiag) (hS1 : SporadicOuterOddFree)
    (hS2 : SporadicCentralizerPPart) (hC : I294InnerLieCross) (hD : I294InnerLieLayer)
    {p : ℕ} {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal] {z g : Y}
    {D : Subgroup Y} (cfg : I294Cfg p L z g D) : NoPSignalizer p D := by
  have hp : p.Prime := cfg.prime
  have hDL : D ≤ L := cfg.le_of_outer_inputs hK hO
  obtain ⟨i, ⟨e⟩⟩ := cfg.catalog
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ := cfg.nonab
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  | alternating n hn => exact (i294_false_of_alternating cfg hDL hn e).elim
  | sporadic s => exact (i294_false_of_sporadic hS1 hS2 cfg hDL s e).elim
  | lie d =>
    by_cases hch : d.1.characteristic = p
    · exact CFSG.LocalAnalysis.RankFourTheoremC.signalizer_eq_bot_of_constrained hp cfg.odd
        cfg.elem cfg.card cfg.sylow fun w hw hw1 =>
          ⟨hD p Y L z g D cfg hDL d hch ⟨e⟩ w hw hw1,
            cfg.pPrimeCore_eq_bot_of_defCharInnerCoreFree hCore hDL d hch ⟨e⟩ hw hw1⟩
    · exact (hC p Y L z g D cfg hDL d hch ⟨e⟩).elim

theorem input29_4Rank3_of_inputs
    (hCore : CFSG.HardMathSupport.Timmesfeld.Coordinator.DefCharInnerCoreFree)
    (hK : KDOutDerived) (hO : I294OuterDiag) (hS1 : SporadicOuterOddFree)
    (hS2 : SporadicCentralizerPPart) (hC : I294InnerLieCross) (hD : I294InnerLieLayer) :
    Input29_4Rank3 := by
  intro p hp hodd Y _ _ L _ hLs hLn hLcat hLC hrk z D hDe hDc hzD hz1 hDS hg
  by_cases hnt : LinesTrans D z
  · exact Or.inr hnt
  · left
    obtain ⟨g, hg⟩ := hg
    obtain ⟨x, hxD, hx1, hxS⟩ :=
      exists_sylowLine_of_not_linesTrans hp hDe hDc hDS hzD hz1 hnt
    exact I294Cfg.noPSignalizer hCore hK hO hS1 hS2 hC hD
      ⟨hp, hodd, hLs, hLn, hLcat, hLC, hrk, hDe, hDc, hzD, hz1, hDS, hg, ⟨x, hxD, hx1, hxS⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
