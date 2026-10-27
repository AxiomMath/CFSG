module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumO1
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15DynkinA2
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

theorem k541DynkinA2 : K541DynkinA2 := by
  intro X _ _ T hGN Ls hL hJ n hn e s
  classical
  obtain ⟨W, _, _, _, ρ, hρ, A, hA2, hAbest, hAN, hLA⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.exists_rep_offender X T hGN Ls hL hJ
  have hfaith : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1 := fun a _ h =>
    hρ (by rw [map_one]; exact LinearMap.ext h)
  have hb : IsBestOffenderOn ρ A ⊤ := (isBestOffender_iff_on ρ A hfaith).mp ⟨hA2, hAbest⟩
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  exact exists_eq_slConjugation_mul_slFieldAut_of_offender ρ hρ hn hF e hL.2.2 hA2 hAN hLA hb s s.2

end CFSG.LocalAnalysis.RankThreeUC.S15

end
