module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerGNDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.I542ThreeOffender

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.Quasithin
open scoped commutatorElement

theorem threePrimeJCentral_proved
    : ThreePrimeJCentral := by
  intro X _ _ T hGN N hN hcop
  have h3 : ¬ 3 ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop
  have hle := thompsonJ_star_le_centralizer hGN N h3
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hle

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
