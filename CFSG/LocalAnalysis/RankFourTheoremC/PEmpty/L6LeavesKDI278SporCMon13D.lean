module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13Red
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13DMain
public import CFSG.HardMathSupport.Dickson.BMRows.M13L33
public import CFSG.HardMathSupport.Dickson.BMRows.M13AOrder
public import CFSG.HardMathSupport.Dickson.BMRows.M13Inf

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13

open Subgroup CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal

theorem noSig_xE_of_sl33
    (hSL : SL33Thirteen) :
    ∀ R Y : Subgroup Gmat, CFSG.Open.IsElemAbelian 13 R →
      Nat.card R = 13 ^ 2 → gw thirteenX ∈ R →
      Y ≤ Subgroup.centralizer ({gw thirteenX} : Set Gmat) →
      ¬ 13 ∣ Nat.card Y → R ≤ Subgroup.normalizer (Y : Set Gmat) → Y = ⊥ := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hG : CFSG.Monster.Generated.Gmat = CFSG.Monster.Griess.AutO :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.gmat_eq_griess
  let φ : CFSG.Monster.Generated.Gmat ≃* CFSG.Monster.Existence.MGriess :=
    MulEquiv.subgroupCongr hG
  have hx : orderOf (gw thirteenX) = 13 := orderOf_xE
  have hc13 : orderOf (gw genD13W1) = 13 := orderOf_c13
  obtain ⟨Q, hQC, ⟨e⟩⟩ := CFSG.HardMathSupport.Dickson.BMRows.M13L33.exists_l33_xE
  have hC : Nat.card ↥(Subgroup.centralizer ({gw thirteenX} : Set Gmat)) ≤ 451 * 936 :=
    CFSG.HardMathSupport.Dickson.BMRows.card_centralizer_xE_le φ
  have hI : ∀ u : Gmat, u * u = 1 → u ≠ 1 → u * gw thirteenX = gw thirteenX * u →
      Nat.card ↥(Subgroup.centralizer ({u} : Set Gmat) ⊓
        Subgroup.centralizer ({gw thirteenX} : Set Gmat)) ≤ 936 :=
    fun u hu2 hu1 hux => CFSG.HardMathSupport.Dickson.BMRows.card_cent_inf_xE_le φ hu2 hu1 hux
  have hbal := balance_gmat_c13
  obtain ⟨hg13, hd13, -, hcg, hcd, hdg, -, -⟩ := d13_gw_facts
  have hG : (Nat.card Gmat).factorization 13 = 3 := factorization_Gmat_thirteen
  obtain ⟨hpG, hmax, hcard, hnab, hcmem, hcs⟩ :=
    closure_sylow_of_central hG hg13 hd13 hc13 hcg hcd hdg (by norm_num)
  have hSnab : ∃ a ∈ closure ({gw genD13W0, gw genD13W2} : Set Gmat), ∃ b ∈
      closure ({gw genD13W0, gw genD13W2} : Set Gmat), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
  exact noSig_of_structure hx hc13 hQC e hC hI hSL hbal hpG hmax hcard hSnab hcmem hcs

theorem kdI278SporCMonster_of_sl33
    (hSL : SL33Thirteen) : KDI278SporCMonster :=
  kdI278SporCMonster_of_xE (noSig_xE_of_sl33 hSL)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13
