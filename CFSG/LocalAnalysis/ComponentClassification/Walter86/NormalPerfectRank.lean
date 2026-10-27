module

import CFSG.LocalAnalysis.AGLEmbedding.ComponentTrichotomy
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.Walter86.NormalPerfectRank

theorem pRank_le_inf_centralizer_add_mulAut_centerQuotient_of_perfect
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {A R : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (A : Set G))
    (hperfect : commutator ↥A = ⊤) :
    CFSG.Open.pRank p R ≤
      CFSG.Open.pRank p (R ⊓ Subgroup.centralizer (A : Set G)) +
      CFSG.Open.pRank p
        (⊤ : Subgroup (MulAut (↥A ⧸ Subgroup.center ↥A))) := by
  have hbase := CFSG.AGLEmbedding.pRank_le_pRank_inf_centralizer_add_pRank_mulAut
    (X := G) (p := p) hp (K := A) (R := R) hR
  have hperfectAut :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_mulAut_le_of_perfect
      (L := ↥A) (p := p) hp.one_lt hperfect
  exact hbase.trans (Nat.add_le_add_left hperfectAut _)

end CFSG.ComponentClassification.Walter86.NormalPerfectRank
