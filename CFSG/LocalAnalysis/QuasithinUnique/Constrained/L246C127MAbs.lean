module

public import CFSG.Open.Defs
public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.F1Models
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace L246C127

namespace MAbs

section Abs

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem comm_eq_self {K : Subgroup Ω} (hK : IsQuasisimple ↥K) : ⁅K, K⁆ = K := by
  rw [← Subgroup.map_subtype_commutator, hK.1, Subgroup.map_top, Subgroup.range_subtype]

end Abs

end MAbs

end L246C127

end CFSG.QuasithinUnique
