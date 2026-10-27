module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6ToralD5
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6ToralA5
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofToralReps

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem oddExcInnerDiagInput_E6
    : OddExcInnerDiagInput .E6 := by
  intro K _ _ p f hp hp2 hKp α g a hαg hαo L hL
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hKp
  have hKodd : Odd (Nat.card K) := by
    rw [hKp]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαo
    exact absurd hαo (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ :=
    exists_toralCentralizer_equiv_of_innerDiag (Or.inr (Or.inr (Or.inl rfl))) hKodd hαg hα
  refine oddLieCentralQuotient_of_mulEquiv (L.equivMapOfInjective Θ.toMonoidHom Θ.injective)
    (toralCentralizer_component_of_orbitCheck hK2 e6SignOrbit_check (fun ρ hρ hne N hN => ?_) hb
      (hb1 hα1) (LocalCores.isComponent_map_mulEquiv Θ hL))
  have hlen : e6SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact e6_toral_D5_component hp hp2 hKp hN
  · exact e6_toral_A5_component hp hp2 hKp hN

end CFSG.ComponentClassification.CatLeafProof
