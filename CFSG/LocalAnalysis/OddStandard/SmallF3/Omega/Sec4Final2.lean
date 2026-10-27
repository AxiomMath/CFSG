module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ZExists
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem aschOmega7_of_410ctx_seven (h410 : Asc82Lemma410Ctx) (hZ : Asc82ZExists7) :
    AschOmega7 := by
  intro G _ _ t L hset hmodel
  obtain ⟨P⟩ : Nonempty (Sylow 2 (centralizer ({t} : Set G))) := inferInstance
  obtain ⟨z, hz⟩ := hZ G t L hset hmodel _ (isSylow2Of_map_sylow P)
  exact h410 G t L _ z ⟨⟨hset, hmodel⟩, hz⟩

end CFSG.OddStandard.SmallF3.Omega
