module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Small
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Simple

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup Blueprint CFSG.LieType.Ree

theorem leafRee_holds :
    LeafRee := by
  intro X _ _ _ hr f h
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hree⟩ := h.reeTitsModel (by decide)
  obtain ⟨-, -, -, -, hiso⟩ := small_Ree_model_Schreier X 3 f hree
  obtain ⟨-, a, hfa, K, _, _, hK, hw⟩ := hree
  have hchar : CharP K ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hK
  obtain ⟨E⟩ := hiso a K hfa hK hw
  have hK' : Nat.card K = 3 ^ (2 * a + 1) := by rw [hK, hfa]
  have hfin : Finite (ReeTag.G2.reeGamma K a) := Finite.of_equiv X E.toEquiv
  obtain ⟨w₀, hw₀⟩ :=
    Finite.exists_max (CFSG.LieType.Chevalley.coxeterSystem ReeTag.G2.tag).length
  obtain ⟨-, hcard, P, hP⟩ := CFSG.Walter.Ree.Model.smallRee_E8_sylow hK' hw₀
  have hP8 : Nat.card (P : Subgroup (ReeTag.G2.reeGamma K a)) = 8 := by
    rw [hP]
    exact hcard
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 X))
  have hS : Nat.card (S : Subgroup X) = 8 := by
    have h1 : Nat.card (S : Subgroup X) = 2 ^ Nat.factorization (Nat.card X) 2 :=
      Sylow.card_eq_multiplicity S
    have h2 : Nat.card (P : Subgroup (ReeTag.G2.reeGamma K a)) =
        2 ^ Nat.factorization (Nat.card (ReeTag.G2.reeGamma K a)) 2 :=
      Sylow.card_eq_multiplicity P
    rw [h1, Nat.card_congr E.toEquiv, ← h2, hP8]
  exact sylowFourJoined_of_card_sylow_eq_eight S hS hr

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
