module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma210
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutSU2
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutAbelian

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Assembly.LowTwoRank

theorem inputSylowCentreInn_holds : LocalBalance.Lemma210Ns.InputSylowCentreInn := by
  intro Lb _ _ h S hS hmax σ hσ hcomm
  rcases h with ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, q, hcard, hq9, ⟨e⟩⟩
  · exact sylowCentreInn_of_mulEquiv e (sylowCentreInn_statedSL K hK) S hS hmax σ hσ hcomm
  · obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
    by_cases hq : 2 < p ^ f
    · exact sylowCentreInn_of_mulEquiv e (sylowCentreInn_statedSU hF hq hq9) S hS hmax σ hσ hcomm
    · have h2 : p ^ f = 2 ^ 1 := by
        have h1 : 2 ≤ p ^ f := le_trans hF.prime.two_le (Nat.le_self_pow (by have := hF.one_le; omega) p)
        omega
      rw [h2] at e hcard
      exact sylowCentreInn_of_mulEquiv e (sylowCentreInn_statedSU_two hcard) S hS hmax σ hσ hcomm

end CFSG.HardMathSupport.Solomon.Coordinator
