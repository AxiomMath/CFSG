module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.ASHypK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltPair
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltPlumb

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace B69K

variable {V : Type} [CommGroup V] [Finite V]

theorem not_alt_odd {X T M A L : Subgroup (MulAut V)} (hH : B69.CompHypK X T M A L) {m : ℕ}
    (hm : 9 ≤ m) (hodd : Odd m) (hnp : ¬ ∃ j : ℕ, m = 2 ^ j + 1) :
    ¬ IsAlt m (↥L ⧸ Subgroup.center ↥L) := by
  rintro ⟨e₀⟩
  obtain ⟨Y, _, _, K, T', M', hAS, ⟨e'⟩⟩ := asHyp_of_compHypK hH
  exact false_of_alt_pair hAS (Or.inr (by omega)) (e'.symm.trans e₀)
    fun T'' hT'' => alt_pair_odd (by omega) hodd hnp T'' hT''

end B69K

end CFSG.Quasithin
