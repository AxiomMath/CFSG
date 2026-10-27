module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutDefs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwoLocal

import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SzFiveTrans
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut

theorem autMAt_sz32
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore 5 X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) : AutMAt 5 N := by
  obtain ⟨-, -, hKn, hKC⟩ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar (p := 5) (by norm_num) hO hN
  obtain hSz := CFSG.AGLEmbeddingD2.sz32Normal_of_mulEquiv d hd hKn hKC e
  have hcardX : Nat.card X ∣ 32537600 * 5 := by
    rw [← Subgroup.card_mul_index (CFSG.generalizedFitting X), hSz.card]
    exact mul_dvd_mul_left 32537600 hSz.index_dvd_five
  refine autMAt_of_not_three_dvd 5 N ?_
  intro h3
  have h3' : 3 ∣ 32537600 * 5 := h3.trans hcardX
  norm_num at h3'

theorem autMAt_of_d2HeisLocalAt {i : TauCeti.CFSGIndex} {p : ℕ} [Fact p.Prime]
    (hp : p = 5 ∨ p = 11) (H : CFSG.AGLEmbeddingD2.D2HeisLocalAt i fun q => q = p)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* i.Group) : AutMAt p N :=
  autMAt_of_pRank_le_one p
    (KFTwo.isSolvable_and_pRank_three_self_le_one_of_d2HeisLocalAt hp H hO hN e).2

theorem autMAt_of_d2TorusLocalAt {i : TauCeti.CFSGIndex} [Fact (Nat.Prime 5)]
    (H : CFSG.AGLEmbeddingD2.D2TorusLocalAt i fun q => q = 5)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore 5 X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N)
    (e : ↥(CFSG.generalizedFitting X) ≃* i.Group) : AutMAt 5 N :=
  autMAt_of_pRank_le_one 5
    (KFTwo.isSolvable_and_pRank_three_self_le_one_of_d2TorusLocalAt H hO hN e).2

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut
