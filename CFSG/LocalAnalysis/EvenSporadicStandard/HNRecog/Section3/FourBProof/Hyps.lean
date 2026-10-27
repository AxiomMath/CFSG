module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

structure FourBHyps {G : Type} [Group G] (a z : G) : Prop where
  hI : TwoHSInterface
  h : IsF5Type a z
  hF1 : Vert Fusion1Facts a z
  hF2 : Vert Fusion2Facts a z
  hF3 : Vert Fusion3Facts a z
  hPic : Vert A8Pictures a z
  hPerp : Vert PerpFacts a z
  hT5 : Vert TableVFacts a z

structure FourBPair {G : Type} [Group G] (a p q : G) : Prop where
  hp : IsConj a p
  hq : IsConj a q
  hb : IsConj a ((p * q) ^ 2)

theorem FourBPair.of_mem_orb4B {G : Type} [Group G] {a x : G} (hx : x ∈ orb4B a a) :
    FourBPair a a x :=
  ⟨IsConj.refl a, hx.1, hx.2⟩

theorem FourBPair.symm {G : Type} [Group G] {a p q : G} (P : FourBPair a p q) :
    FourBPair a q p := by
  refine ⟨P.hq, P.hp, ?_⟩
  have h : (q * p) ^ 2 = p⁻¹ * (p * q) ^ 2 * p⁻¹⁻¹ := by
    rw [pow_two, pow_two]
    group
  rw [h]
  exact P.hb.trans (isConj_iff.mpr ⟨p⁻¹, rfl⟩)

end CFSG.EvenSporadicStandard.HNRecog.Section3
