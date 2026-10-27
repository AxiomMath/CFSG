module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplitFin
import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplitKer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplit

theorem pRank_le_of_beta {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type} [Group Y] [Finite Y]
    {P : Subgroup Y} (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤) {x : Y} (hxP : x ∈ P)
    (hxp : x ^ p = 1)
    (hJC : ∀ E : Subgroup Y, E ≤ P → CFSG.Open.IsElemAbelian p E →
      x ∈ Subgroup.normalizer (E : Set Y) → Nat.card E ≤ p ^ p)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections Y)
    (hcard : Nat.card (CFSG.LocalCores.ComponentIndex Y) = p)
    (hZ : ∀ C : CFSG.LocalCores.ComponentIndex Y, Subgroup.center C.1 = ⊥)
    (htrans : ∀ C C' : CFSG.LocalCores.ComponentIndex Y,
      ∃ k : ℕ, CFSG.LocalAnalysis.RankFourTheoremC.Lemma213.cjComp (x ^ k) C = C')
    (hcyc : ∀ C : CFSG.LocalCores.ComponentIndex Y, IsCyclic ↥(P ⊓ C.1 : Subgroup Y))
    (hC : ∀ g ∈ P, g ∈ Subgroup.centralizer (CFSG.layer Y : Set Y) → g = 1)
    (hdvd : ∀ C : CFSG.LocalCores.ComponentIndex Y, p ∣ Nat.card C.1)
    (h7131 : GL83.I_7_13_1) (hsplit : KFactSylowSplit) :
    CFSG.Open.pRank p P ≤ p := by
  have hcfg : SplitCfg p P x :=
    ⟨hp, hp5, hP, hxP, hxp, hJC, hcat, hcard, hZ, htrans, hcyc, hC, hdvd⟩
  have hl := compKer_le_layer hsplit h7131 hcfg
  refine CFSG.GH74.Uniqueness.SU.SU1.pRank_le_of fun E hEP hE k hk => ?_
  have h1 := card_le_of_compKer_le_layer hcfg hl hEP hE
  rw [hk] at h1
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
