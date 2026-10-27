module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Gz9.NoInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Gz9.Exists

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gz9_of_hyps (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (_hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z)
    (hOrb : Vert GzOrbitFacts a z) (hNo : Vert GzNoFacts a z) (_hY4a : Vert Y4aFacts a z) :
    Gz9Facts a z where
  aschbacher := ⟨CFSG.pCore 2 ↥(Gx z), inferInstance,
    { toIsExtraspecialPlusByA5WrTwoWith := isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z
      irreducible := cIrreducible_pCore h hOrb.self
      no_involution := fun t ht ht2 => gz9_no_involution h hNo.self t ht ht2
      exists_involution := gz9_exists_involution hC h hF3 hOrb.self hNo.self }⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
