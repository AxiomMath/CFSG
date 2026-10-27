module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiDefsHered

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

theorem sol78ClosingFi_of_parts (h22 : Sol78Closing [.Fi22] fun _ => fiIn22)
    (h23 : Sol78ClosingCHered [.Fi23] fun _ => fiIn23)
    (h24 : Sol78Closing [.Fi24Prime] fun _ => fiIn24)
    (hout : ∀ (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (t u : H), FStarSimple N →
      N.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover .Fi24Prime L →
        SolomonGlobalQ H L K t u → fiOut24 H L K u → False)
    (hcfg : Sol78Lit → ∀ (H : Type) [Group H] [Finite H],
      BelowSec (Sol78PredS fiTypes) H → ∀ (N L : Subgroup H) (t u : H),
        CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover .Fi24Prime L →
          Cfg610_2 H N L t u → False) :
    Sol78ClosingFi := by
  intro lit H _ _ ih N L s hs hN hidx hKP hcov hout'
  rcases hout' with ⟨K, t, u, hglob, hpair⟩ | ⟨rfl, t, u, hc⟩
  · have hs' : s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime := by simpa [fiTypes] using hs
    rcases hs' with rfl | rfl | rfl
    · exact (h22 H N L K t u .Fi22 (List.mem_singleton.2 rfl) hN hidx hKP hcov hglob hpair).elim
    · exact h23 H ih.uHered N L K t u .Fi23 (List.mem_singleton.2 rfl) hN hidx hKP hcov hglob
        hpair
    · rcases hpair with hin | hot
      · exact (h24 H N L K t u .Fi24Prime (List.mem_singleton.2 rfl) hN hidx hKP hcov hglob
          hin).elim
      · exact (hout H N L K t u hN hidx hKP hcov hglob hot).elim
  · exact (hcfg lit H ih N L t u hKP hcov hc).elim

end CFSG.EvenSporadicStandard.Induction
