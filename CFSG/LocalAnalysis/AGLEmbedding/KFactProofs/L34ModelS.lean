module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Local

public section

namespace CFSG.AGLEmbedding

namespace KFactProofs.L34ModelS

open CFSG.ComponentClassification.PSL3Four

theorem nonempty_mulEquiv_S_of_isLinThreeFour {K : Type}
    [Group K] (h : IsLinThreeFour K) : Nonempty (K ≃* ↥S) := by
  obtain ⟨ε⟩ := KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour h
  refine nonempty_equiv_of_stated K ⟨?_, GaloisField 2 2, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · exact ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  · rw [GaloisField.card 2 2 (by norm_num)]
  · exact ε.trans ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 (GaloisField 2 2))).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3
        (GaloisField 2 2)))

end KFactProofs.L34ModelS

end CFSG.AGLEmbedding
