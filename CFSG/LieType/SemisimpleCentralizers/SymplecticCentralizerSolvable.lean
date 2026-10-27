module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivFactors
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsSp
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalPComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas

public section

namespace CFSG.LieType.SemisimpleCentralizers

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.LieType.Universal

theorem isSolvable_statedSp_centralizer_of_hasNormalPComplement
    {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F ^ 2 - 1)
    {E : Subgroup (StatedSp n F)} (hE : IsPGroup p E)
    (hNPC : CFSG.HasNormalPComplement p
      ↥(⁅Subgroup.centralizer (E : Set (StatedSp n F)),
         Subgroup.centralizer (E : Set (StatedSp n F))⁆)) :
    Group.IsSolvable ↥(Subgroup.centralizer (E : Set (StatedSp n F))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let H := Subgroup.centralizer (E : Set (StatedSp n F))
  obtain ⟨β, S, ⟨hSC, _, hSq, ⟨k, hder⟩, _⟩, hdiv⟩ :=
    LayerPDiv.exists_coreFamily_sp_pDiv LayerPDiv.altFactorPDivInput_holds
      LayerPDiv.hermFactorPDivInput_holds hp hp2 hpF hE
  have hno : ∀ b : β, False := by
    intro b
    have hperf : ⁅S b, S b⁆ = S b :=
      LayerFacts.ggCommutator_eq_of_isQuasisimple (hSq b)
    have hle : S b ≤ ⁅H, H⁆ := by
      rw [← hperf]
      exact Subgroup.commutator_mono (hSC b) (hSC b)
    have hNPCS : CFSG.HasNormalPComplement p ↥(S b) :=
      CFSG.hasNormalPComplement_of_le p hle hNPC
    haveI : Group.IsPerfect ↥(S b) := LayerFacts.ggIsPerfect_of_commutator_eq hperf
    obtain ⟨N, hN, hcop, hpg⟩ := hNPCS
    haveI : N.Normal := hN
    have hNtop : N = ⊤ :=
      CFSG.ComponentClassification.LiteratureLocal.eq_top_of_isPGroup_quotient_of_perfect N hpg
    have hcopS : Nat.Coprime p (Nat.card ↥(S b)) := by
      simpa only [hNtop, Subgroup.card_top] using hcop
    exact (hp.coprime_iff_not_dvd).mp hcopS (hdiv b)
  have hcorebot : (⨆ b, S b) ≤ ⊥ := iSup_le fun b => (hno b).elim
  have hpc : CFSG.Quasithin.perfectCore H = ⊥ := by
    apply le_bot_iff.mp
    exact (LayerPDiv.le_of_perfect_of_ggDer_le
      (CFSG.Quasithin.perfectCore_le H) (CFSG.Quasithin.perfectCore_perfect H) hder).trans hcorebot
  exact (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot H).mpr hpc

end CFSG.LieType.SemisimpleCentralizers
