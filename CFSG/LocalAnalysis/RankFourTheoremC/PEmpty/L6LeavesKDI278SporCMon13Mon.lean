module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13Loc
public import CFSG.HardMathSupport.Dickson.BMRows.M13B
public import CFSG.GroupTheory.PCore.FixedSubgroupCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13

open CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13
  CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

theorem balance_gmat_c13
    :
    ∀ R Y : Subgroup Gmat, CFSG.Open.IsElemAbelian 13 R → Nat.card R = 13 ^ 2 →
      gw genD13W1 ∈ R → Y ≤ Subgroup.centralizer ({gw genD13W1} : Set Gmat) →
      ¬ 13 ∣ Nat.card Y → R ≤ Subgroup.normalizer (Y : Set Gmat) → Y = ⊥ := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨hg13, hd13, -, hcg, hcd, hdg, hc1, -⟩ := d13_gw_facts
  have hc13 : orderOf (gw genD13W1) = 13 := orderOf_c13
  have hG : (Nat.card Gmat).factorization 13 = 3 := factorization_Gmat_thirteen
  obtain ⟨hpG, hmax, hcard, hnab, hcmem, hcs⟩ :=
    closure_sylow_of_central hG hg13 hd13 hc13 hcg hcd hdg (by norm_num)
  have hodd := odd_card_core_thirteen (gw genD13W1) hc13
  have hcore0 :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenB.gLAPPrimeCoreOf_c13_eq_bot hodd
  have hcore : CFSG.pPrimeCore 13 ↥(Subgroup.centralizer ({gw genD13W1} : Set Gmat)) = ⊥ :=
    (CFSG.gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore).1 hcore0
  exact balance_at_central hc13 hpG hmax hcard hnab hcmem hcs
    CFSG.HardMathSupport.Dickson.BMRows.isSolvable_centralizer_c13 hcore

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13
