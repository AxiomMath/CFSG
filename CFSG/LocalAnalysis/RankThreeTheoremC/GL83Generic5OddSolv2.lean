module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5OddSolv
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup2
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerCoprime
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen5_primeCore_solvable (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    (hEv : KFactCoprimeAutEvenCentralizer) : Group.IsSolvable ↥(rankThreePrimeCore p M) := by
  have hp := gen5_prime hl
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hXM, hMX, hXcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p M
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hG.setting hl.sigma hl.core
  obtain ⟨hxP, ⟨-, -, hxp, -, -⟩, -, -⟩ := hl.generic
  have hp2 : p ≠ 2 := by
    have := gen5_five_le hG hl
    omega
  obtain ⟨e⟩ := gen5_psl hG hl
  have hodd : Odd (Nat.card (rankThreePrimeCore p M ⊓ centralizer ({x} : Set G) : Subgroup G)) := by
    have hle := primeCore_inf_centralizer_le_centralizer_layer hG.setting hl.sigma hl.core
      hl.generic le_rfl e
    refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => (gen5_Z hG hl).2.1 ?_)
    exact h.trans (card_dvd_of_le hle)
  have := hG.setting.simple
  have hMtop : M ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hG.setting.nonab hl.core.1.1
  have hcat : CatalogSimpleSections (rankThreePrimeCore p M) :=
    ((catalogSimpleSections_of_isKProper hG.setting.kProper M hMtop).subgroup
      ((rankThreePrimeCore p M).subgroupOf M)).of_surjective
      (subgroupOfEquivOfLe hXM).toMonoidHom (MulEquiv.surjective _)
  exact oddCentralizerSolvable_holds hEv hp2 (hMX (hPM hxP)) hxp
    ((Nat.Prime.coprime_iff_not_dvd hp).mp hXcop) hodd hcat

end CFSG.LocalAnalysis.RankThreeTheoremC
