module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeRankThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeRankThreeClassical
import CFSG.Adapters.LinearCatalogStated
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open

theorem i294CrossThreeRankThreeOn_classical_of_models
    (hL4 : I294CrossModelPSL4) (hL67 : I294CrossModelPSL67) (hU4 : I294CrossModelPSU4)
    (hU67 : I294CrossModelPSU67) (hSp : I294CrossModelPSp6) (hO7 : I294CrossModelPOmega7)
    (hOm : I294CrossModelPOmegaMinus4) :
    I294CrossThreeRankThreeOn I294CrossIsClassical := by
  intro L _ _ _ _ d hd hc3 hLe hLU hS h243 _ x hx
  obtain ⟨idx, hv⟩ := d
  obtain ⟨e⟩ := hLe
  cases idx with
  | A r q =>
    have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_A] using hc3
    exact I294Cross.rankThree_of_classical_model hL4 hL67 hU4 hU67 hSp hO7 hOm
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e) hp3 hLU hS h243 x hx
  | twistedA r q =>
    have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_twistedA] using hc3
    exact I294Cross.rankThree_of_classical_model hL4 hL67 hU4 hU67 hSp hO7 hOm
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e) hp3 hLU hS h243 x hx
  | B r q =>
    have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_B] using hc3
    have hr2 : 2 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
    rcases Nat.lt_or_ge r 3 with hr | hr
    · obtain rfl : r = 2 := by omega
      exact I294Cross.rankThree_of_classical_model hL4 hL67 hU4 hU67 hSp hO7 hOm
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e) hp3 hLU hS h243 x hx
    · by_cases hq2 : q.p = 2
      · exact I294Cross.rankThree_of_classical_model hL4 hL67 hU4 hU67 hSp hO7 hOm
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2 hr e)
          hp3 hLU hS h243 x hx
      · exact I294Cross.rankThree_of_classical_model hL4 hL67 hU4 hU67 hSp hO7 hOm
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hq2 hr e)
          hp3 hLU hS h243 x hx
  | C r q =>
    have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_C] using hc3
    exact I294Cross.rankThree_of_classical_model hL4 hL67 hU4 hU67 hSp hO7 hOm
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e) hp3 hLU hS h243 x hx
  | D r q =>
    have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_D] using hc3
    exact I294Cross.rankThree_of_classical_model hL4 hL67 hU4 hU67 hSp hO7 hOm
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e) hp3 hLU hS h243 x hx
  | twistedD r q =>
    have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_twistedD] using hc3
    exact I294Cross.rankThree_of_classical_model hL4 hL67 hU4 hU67 hSp hO7 hOm
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e) hp3 hLU hS
      h243 x hx
  | _ => exact (hd : False).elim

theorem i294CrossThreeRankThreeOn_nonclassical :
    I294CrossThreeRankThreeOn fun d => ¬ I294CrossIsClassical d := by
  intro L _ _ hs hn d hd
  obtain ⟨i, hv⟩ := d
  cases i with
  | A r q => exact (hd trivial).elim
  | twistedA r q => exact (hd trivial).elim
  | B r q => exact (hd trivial).elim
  | C r q => exact (hd trivial).elim
  | D r q => exact (hd trivial).elim
  | twistedD r q => exact (hd trivial).elim
  | E6 q => exact i294CrossThreeRankThreeOn_excBig L hs hn ⟨_, hv⟩ trivial
  | E7 q => exact i294CrossThreeRankThreeOn_excBig L hs hn ⟨_, hv⟩ trivial
  | E8 q => exact i294CrossThreeRankThreeOn_excBig L hs hn ⟨_, hv⟩ trivial
  | F4 q => exact i294CrossThreeRankThreeOn_excBig L hs hn ⟨_, hv⟩ trivial
  | twistedE6 q => exact i294CrossThreeRankThreeOn_excBig L hs hn ⟨_, hv⟩ trivial
  | G2 q => exact i294CrossThreeRankThreeOn_g2 L hs hn ⟨_, hv⟩ trivial
  | trialityD4 q => exact i294CrossThreeRankThreeOn_triality L hs hn ⟨_, hv⟩ trivial
  | suzuki m => exact i294CrossThreeRankThreeOn_sz L hs hn ⟨_, hv⟩ trivial
  | reeG2 m => exact i294CrossThreeRankThreeOn_reeG2 L hs hn ⟨_, hv⟩ trivial
  | reeF4 m => exact i294CrossThreeRankThreeOn_reeF4 L hs hn ⟨_, hv⟩ trivial
  | tits => exact i294CrossThreeRankThreeOn_tits L hs hn ⟨_, hv⟩ trivial

theorem i294CrossThreeRankThree_of_models
    (hL4 : I294CrossModelPSL4) (hL67 : I294CrossModelPSL67) (hU4 : I294CrossModelPSU4)
    (hU67 : I294CrossModelPSU67) (hSp : I294CrossModelPSp6) (hO7 : I294CrossModelPOmega7)
    (hOm : I294CrossModelPOmegaMinus4) : I294CrossThreeRankThree :=
  I294CrossThreeRankThree.of_classical
    (i294CrossThreeRankThreeOn_classical_of_models hL4 hL67 hU4 hU67 hSp hO7 hOm)
    i294CrossThreeRankThreeOn_nonclassical

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
