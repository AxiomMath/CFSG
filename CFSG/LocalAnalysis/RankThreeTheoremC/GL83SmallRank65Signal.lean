module

import CFSG.RankThree.PartOne.K1327.Trick
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

theorem le_of_plane_centralizers_le {G : Type} [Group G] [Finite G] {U V M : Subgroup G}
    (hU : IsElemAbelian 3 U) (hUc : Nat.card U = 9) (hUV : U ≤ normalizer (V : Set G))
    (hV : ¬ 3 ∣ Nat.card V) (hC : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set G) ≤ M) : V ≤ M := by
  have hgen := CFSG.RankThree.PartOne.K1327.le_iSup_centralizers Nat.prime_three hU
    (by rw [hUc]; norm_num) hUV hV
  refine hgen.trans (iSup_le fun b => ?_)
  exact inf_le_right.trans (hC b.val.val b.val.property fun h => b.property (Subtype.ext h))

end CFSG.LocalAnalysis.RankThreeTheoremC
