module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalSimple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBasic
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharCoatom
import CFSG.GroupTheory.PCoreSelfCentralizing
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.GroupTheory

open CFSG.Open Subgroup

theorem chevParabolicRadicalSimple_of_forall_charTwo {K : Type} [Group K] [Finite K]
    (hK : IsSimpleGroup K)
    (h : ∀ (S : Sylow 2 K) (Y : Subgroup K), normalizer ((S : Subgroup K) : Set K) ≤ Y →
      Y ≠ ⊤ → QuasithinUnique.CharTwo Y) :
    ChevParabolicRadicalSimple K :=
  fun S _ hSP hP => pCoreOf_ne_bot_and_centralizer_le_of_isSimpleGroup hK S (h S) hSP hP

theorem chevParabolicRadicalSimple_of_overgroups {K : Type} [Group K] [Finite K]
    (hK : IsSimpleGroup K) (h : QuasithinUnique.Bridge.Over.Overgroups K) :
    ChevParabolicRadicalSimple K :=
  chevParabolicRadicalSimple_of_forall_charTwo hK fun S Y hSY hY =>
    h _ Y (QuasithinUnique.isSylowTwoOf_top_of_sylow S) (le_normalizer.trans hSY) hY

theorem chevParabolicRadicalSimple_of_ggNormalizerOvergroupsChar {K : Type} [Group K] [Finite K]
    (hK : IsSimpleGroup K) (h : StandardType.GGNormalizerOvergroupsChar 2 K) :
    ChevParabolicRadicalSimple K :=
  chevParabolicRadicalSimple_of_forall_charTwo hK fun S Y hSY hY =>
    QuasithinUnique.charTwo_iff_isCharacteristicP.2 (h _ Y S.isPGroup' S.not_dvd_index hSY hY)

end CFSG.GroupTheory
