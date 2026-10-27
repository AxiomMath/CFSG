module

public import CFSG.LocalAnalysis.GL83PartI.I713.Extension
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListFive

open CFSG.Open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

noncomputable def equiv_of_centerQuotient {K S : Type} [Group K] [Group S]
    [IsSimpleGroup K] (hq : CFSG.IsQuasisimple K) (e : K ⧸ center K ≃* S) : K ≃* S := by
  have hnab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a, b, fun h => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
  have hZ := GL83.I713.center_eq_bot_of_simple hnab
  exact (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ).symm).trans e

theorem pRank_top_le_of_inner_le {S : Type} [Group S] [Finite S] {p : ℕ}
    (hp : 1 < p) (hZ : center S = ⊥) {Y : Subgroup (MulAut S)}
    (hY : (MulAut.conj : S →* MulAut S).range ≤ Y) :
    CFSG.Open.pRank p (⊤ : Subgroup S) ≤ CFSG.Open.pRank p Y := by
  have hi : CFSG.Open.pRank p (inner S) = CFSG.Open.pRank p (⊤ : Subgroup S) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp (GL83.I713.innerEquiv S hZ)]
  rw [← hi]
  exact CFSG.SectionRank.pRank_mono hp hY

theorem pRank_top_le_of_centerQuotient {K S : Type} [Group K] [Finite K]
    [Group S] [Finite S] [IsSimpleGroup K] (hq : CFSG.IsQuasisimple K)
    (e : K ⧸ center K ≃* S) {p : ℕ} (hp : 1 < p) {Y : Subgroup (MulAut S)}
    (hY : (MulAut.conj : S →* MulAut S).range ≤ Y) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p Y := by
  have : IsSimpleGroup (K ⧸ center K) := hq.2.1
  have : IsSimpleGroup S := e.symm.isSimpleGroup
  have hnab : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact ⟨e a, e b, fun h => hab (e.injective (by simpa only [map_mul] using h))⟩
  have hZ := GL83.I713.center_eq_bot_of_simple hnab
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp (equiv_of_centerQuotient hq e)]
  exact pRank_top_le_of_inner_le hp hZ hY

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListFive

end
