module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.PreuniquenessRankFour.AlternatingForm
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalPerfectLifts
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitBasis

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers Subgroup
  CFSG.AGLEmbedding.ParabPrime
open CFSG.PreuniquenessRankFour.Helpers
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Hyp111

theorem mem_normalizer_oUpperTwo {X : Subgroup G} {n : G} (hn : n ∈ X) :
    n ∈ normalizer (CFSG.ComponentClassification.AS76b.oUpperTwo X : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, CFSG.ComponentClassification.AS76b.oUpperTwo,
    MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨w, ⟨hwX, hw⟩, rfl⟩
    refine ⟨X.mul_mem (X.mul_mem hn hwX) (X.inv_mem hn), ?_⟩
    have h := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective w
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    change Odd (orderOf (n * w * n⁻¹))
    rwa [h]
  · rintro ⟨hxX, hx⟩
    refine ⟨n⁻¹ * x * n, ⟨by simpa [mul_assoc] using X.mul_mem (X.mul_mem (X.inv_mem hn) hxX) hn,
      ?_⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
    have : orderOf (n⁻¹ * x * n) = orderOf x := by
      have h := orderOf_injective (MulAut.conj n⁻¹).toMonoidHom (MulAut.conj n⁻¹).injective x
      simpa [MulAut.conj_apply] using h
    rwa [this]

end Hyp111

end CFSG.LocalAnalysis.RankThreeTheoremC
