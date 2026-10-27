module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreS
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter
public import CFSG.HardMathSupport.Solomon.Coordinator.FixSubgroupInf

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

variable {p : ℕ} {d : TauCeti.ValidLieTypeIndex} [Finite (TauCeti.CFSGIndex.lie d).Group]
  {A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)} {m c : ℕ}

theorem KD264CoreHyp.characteristic_ne (h : KD264CoreHyp p d A m c) :
    p ≠ d.1.characteristic :=
  (characteristic_ne_of_not_isChevSimple d.2 ⟨MulEquiv.refl _⟩ h.notChev).symm

theorem KD264CoreHyp.pRank_eq (h : KD264CoreHyp p d A m c) : CFSG.Open.pRank p A = m :=
  CFSG.HardMathSupport.Solomon.LocalBalance.pRank_eq_of_card h.prime h.elem h.card

theorem isGood_zpowers_of_glaPComponent (hp : p.Prime) {S : Type} [Group S] [Finite S]
    {β : MulAut S} {J : Subgroup S} (hJ : GLAPComponent p (fixSubgroup β) J) :
    IsGood p (Subgroup.zpowers β) := by
  unfold IsGood
  rw [iInf_fixSubgroup_zpowers]
  exact (CFSG.LocalAnalysis.GLTheoremA.S3.glaPLayer_ne_bot_iff hp).2 ⟨J, hJ⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
