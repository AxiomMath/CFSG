module

public import CFSG.CGT.PushingUpLit.EightOneFinalSetup

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open CFSG.Assembly (KProper InCatalog)

namespace EightOneFinal

variable {G : Type} [Group G] [Finite G]

theorem inClassXG_of_key {L P : Subgroup G} (hL : InClassX ↥L)
    (hP : IsSylowOf 2 P (centralizerModCore L)) (hP1 : P ≠ ⊥)
    (hLP : L ≤ Subgroup.normalizer (P : Set G))
    (key : ∀ N' : Subgroup G, IsMaximalTwoLocal N' → Subgroup.normalizer (P : Set G) ≤ N' →
      (L.subgroupOf N').IsSubnormal) : InClassXG L := by
  have hP2 : IsPGroup 2 P := hP.2.1
  have hloc : ∀ K : Subgroup G, IsPLocal 2 K → Subgroup.normalizer (P : Set G) ≤ K →
      (L.subgroupOf K).IsSubnormal := by
    intro K hK hPK
    obtain ⟨N', hKN', hN'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hK
    exact isSubnormal_subgroupOf_mono (hLP.trans hPK) hKN' (key N' hN' (hPK.trans hKN'))
  refine inClassXG_of_sylow hL hP
    ⟨hLP, hloc _ (isPLocal_normalizer_of_isPGroup hP2 hP1) le_rfl⟩
    (Or.inr ⟨hLP.trans (normalizer_le_normalizer_jIn P),
      hloc _ (isPLocal_normalizer_of_isPGroup (isPGroup_jIn hP2) (jIn_ne_bot hP2 hP1))
        (normalizer_le_normalizer_jIn P)⟩)

end EightOneFinal

open EightOneFinal

end CFSG.CGT.PushingUpLit
