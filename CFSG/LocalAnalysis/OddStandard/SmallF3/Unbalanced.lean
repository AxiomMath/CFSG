module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Facts
public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.LocalAnalysis.OddStandard.AltNoHe

import CFSG.LocalAnalysis.ComponentClassification.SmallLocalSimpleFitting
import CFSG.ClassicalInvolution.OrderForm

public section

namespace CFSG.OddStandard.SmallF3

open Subgroup CFSG.Blueprint CFSG.OddStandard.SmallF3Interfaces

theorem oddLieType_of_unbalanced {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hS : StandardSetting G L) (hU : UImplication G)
    (hQ : SmallF3LieQuotient (L ⧸ center L))
    (hub : ∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥) :
    OddLieType G := by
  haveI : IsSimpleGroup G := hS.simple
  have htop : CFSG.ComponentClassification.GeneralizedFitting.subgroup G = ⊤ :=
    (CFSG.ComponentClassification.SmallLocal.simple_generalized_fitting_self_local G
      hS.nonab).2.2.2.2
  let e : CFSG.ComponentClassification.GeneralizedFitting.subgroup G ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  rcases hU hub with h | ⟨n, _, h7, ⟨eA⟩, _⟩ | ⟨-, hlt⟩
  · exact (CFSG.ClassicalInvolution.oddLieType_congr e).1 h
  · obtain ⟨m, -, ⟨eL⟩⟩ :=
      CFSG.OddStandard.exists_mulEquiv_alternatingGroup_of_standard (e.symm.trans eA) hS.standard
    exact absurd ⟨eL⟩ (not_nonempty_mulEquiv_alternatingGroup hQ m)
  · exact absurd htop hlt.ne

end CFSG.OddStandard.SmallF3
