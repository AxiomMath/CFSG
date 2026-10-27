module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.GammaInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GraphLocal

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem oddInv_of_hyps {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (hF3 : Vert Fusion3Facts a z) (hOrb : Vert GzOrbitFacts a z) (hCls : Vert GzClassFacts a z)
    (hNo : Vert GzNoFacts a z) (hY4a : Vert Y4aFacts a z) (hSGz : Vert StructGzFacts a z)
    (hPar : Vert ParityFacts a z) (hT5 : Vert TableVFacts a z) (hT7 : Vert TableVIIFacts a z) :
    OddInvFacts a z := by
  have hodd : ∀ w x y : G, IsConj z w → IsConj a x → IsConj a y → x ∈ Gx w → y ∈ Gx w →
      Odd (orderOf (x * y)) → ∃ t : G, IsConj a t ∧ t ∈ Gxyz x w y := by
    intro w x y hw hx hy hxw hyw hxy
    obtain ⟨t, ht, htm⟩ := oddInv_core (isF5Type_of_isConj h hx hw) (hF3.of_isConj hx hw)
      (hOrb x w hx hw) (hCls x w hx hw) (hNo x w hx hw) (hY4a x w hx hw) (hSGz x w hx hw)
      (hPar x w hx hw) (hT5 x w hx hw) (hx.symm.trans hy) hxw hyw hxy
    exact ⟨t, hx.trans ht, htm⟩
  exact ⟨hodd, fun x y hx hy ht => oddInv_gamma_of_inv hCls.self hT5 hT7 hodd hx hy ht⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
