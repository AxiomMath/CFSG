module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaDefs
import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbParabSelfNorm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.RowClauseO
import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCore
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OutL27Proof
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.OuterThree.LieTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree
open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

variable {G : Type} [Group G] [Finite G]

private theorem clauseO_of_nineThreeTwo_of_field (hU : OutU33) (hGA : GriessAllModelsStatement)
    {M S L : Subgroup G} (hL : IsWeakSBlock M S L) (h2 : NineThreeTwo M S L)
    (hfield : ∀ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2Index d.1 →
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃*
        (TauCeti.CFSGIndex.lie d).Group) → LieField d.1 = 2)
    (hr : Open.pRank 3 (barM M L) ≤ 3) : ClauseO M L := by
  have hr' : Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barM M L)]
    exact hr
  have hperf : Group.IsPerfect ↥(barM M L) :=
    Subgroup.isPerfect_iff.mpr (barM_perfect hL.le hL.perfect)
  rcases h2.1 with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · exact clauseO_of_cover hL.le hL.perfect
      (autThreePowInner_of_lie_two hGA hperf hr' d hd (hfield d hd ⟨e⟩) e)
      (MulEquiv.refl _)
  · exact clauseO_of_cover hL.le hL.perfect
      (autThreePowInner_alt_of_five_le (N := n) (by omega)) e
  · rcases hd with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
    · exact clauseO_of_cover hL.le hL.perfect
        (outL27_proved _ ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩) (MulEquiv.refl _)
    · exact clauseO_of_cover hL.le hL.perfect
        (hU _ ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩) (MulEquiv.refl _)

theorem mem_normalizer_of_nineThreeTwo (hKP : KFactParabolicSymThreeNormal) (hU : OutU33)
    (hGA : GriessAllModelsStatement) {M S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (h2 : NineThreeTwo M S L) (hr : Open.pRank 3 (barM M L) ≤ 3)
    {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hT : T ∈ cZero (blockParabolic M S L))
    (hT3 : Nonempty (↥T ⧸ CFSG.pCore 2 ↥T ≃* Equiv.Perm (Fin 3)))
    {y : ↥M ⧸ CFSG.pCore 2 ↥M} (hy : ∃ k : ℕ, y ^ 3 ^ k = 1)
    (hyL : y ∈ normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hyP : y ∈ normalizer (blockParabolic M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    y ∈ normalizer (T : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  classical
  have hO2 : pCoreOf 2 (barM M L) = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.pCoreOf_barM_eq_bot
      hL.toIsTwoPrimeComponent
  have hkp := hKP (↥M ⧸ CFSG.pCore 2 ↥M) (barM M L) (blockParabolic M S L)
    hL.component.2.2 hO2 h2.1 h2.2.1 T hT hT3
  have hclause : ClauseO M L :=
    clauseO_of_nineThreeTwo_of_field hU hGA hL h2 hkp.2 hr
  have h3y : IsPGroup 3 (Subgroup.zpowers y) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    rintro ⟨g, z, rfl⟩
    obtain ⟨k, hk⟩ := hy
    refine ⟨k, Subtype.ext ?_⟩
    change (y ^ z) ^ 3 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨l, c, hcC, hlc⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.exists_mul_of_mem_sup_centralizer'
      (L := barM M L) (hclause y hyL h3y)
  have hPleL : blockParabolic M S L ≤ barM M L := barM_mono inf_le_right
  have hcP : c ∈ Subgroup.centralizer (blockParabolic M S L : Set _) :=
    Subgroup.centralizer_le hPleL hcC
  have hcN : c ∈ normalizer (blockParabolic M S L : Set _) :=
    Subgroup.centralizer_le_normalizer _ hcP
  have hlN : (l : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ normalizer (blockParabolic M S L : Set _) := by
    have hl_eq : (l : ↥M ⧸ CFSG.pCore 2 ↥M) = y * c⁻¹ := by
      rw [← hlc]
      group
    rw [hl_eq]
    exact (Subgroup.normalizer _).mul_mem hyP ((Subgroup.normalizer _).inv_mem hcN)
  have hlP : (l : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ blockParabolic M S L :=
    CFSG.HardMathSupport.Curtis.UnitaryLevi.mem_of_mem_normalizer_of_isParabolicTwo
      h2.2.1 l.2 hlN
  have hlNT : (l : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ normalizer (T : Set _) := hkp.1 hlP
  have hTL : T ≤ barM M L := hT.le.trans hPleL
  have hcT : c ∈ Subgroup.centralizer (T : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subgroup.mem_centralizer_iff.mp hcC t (hTL ht)
  have hcNT : c ∈ normalizer (T : Set _) := Subgroup.centralizer_le_normalizer _ hcT
  rw [← hlc]
  exact Subgroup.mul_mem (Subgroup.normalizer (T : Set (↥M ⧸ CFSG.pCore 2 ↥M))) hlNT hcNT

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma
