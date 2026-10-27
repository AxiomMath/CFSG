module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8ToralD8
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8ToralE7
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofToralReps

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def e8MaskWord : List (Fin (Tag.rank .E8)) :=
  ([0, 2, 3, 4, 5, 6, 7] : List (Fin 8)).map e8Node

theorem maskAct_e8MaskWord :
    maskAct e8MaskWord e8BitsE7 = listMask (τ := .E8) (e8SignReps.getD 2 []) := by
  funext j
  revert j
  decide

theorem oddExcInnerDiagInput_E8
    : OddExcInnerDiagInput .E8 := by
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
    exists_toralCentralizer_equiv_of_innerDiag (Or.inr (Or.inr (Or.inr rfl))) hKodd hαg hα
  refine oddLieCentralQuotient_of_mulEquiv (L.equivMapOfInjective Θ.toMonoidHom Θ.injective)
    (toralCentralizer_component_of_orbitCheck hK2 e8SignOrbit_check (fun ρ hρ hne N hN => ?_) hb
      (hb1 hα1) (LocalCores.isComponent_map_mulEquiv Θ hL))
  have hlen : e8SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact e8_toral_D8_component hp hp2 hKp hN
  ·
    have hmap := map_conj_toralCentralizer_of_maskAct (K := K) hK2 e8MaskWord e8BitsE7
    rw [maskAct_e8MaskWord] at hmap
    let e : toralCentralizer .E8 K (bitsTuple e8BitsE7) ≃*
        toralCentralizer .E8 K (bitsTuple (listMask (e8SignReps.getD 2 []))) :=
      ((toralCentralizer .E8 K _).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact oddLieCentralQuotient_of_mulEquiv (N.equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective) (e8_toral_E7_component hp hp2 hKp
        (LocalCores.isComponent_map_mulEquiv e.symm hN))

end CFSG.ComponentClassification.CatLeafProof
