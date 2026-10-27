module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Ly
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Inv
public import CFSG.Sporadic.Co2Schreier.InvolClasses
public import CFSG.Sporadic.Co2Schreier.OddCore
public import CFSG.Sporadic.Co2Schreier.ThreeRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert

theorem l3Inputs_tP :
    L3Inputs tP := by
  refine l3Inputs_of_not_dvd ?_
  rw [← locD_subgroupOf_eq]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe locD_le_P).toEquiv, card_locD]
  norm_num

theorem l3Inputs_uP :
    L3Inputs uP := by
  refine l3Inputs_of_not_dvd ?_
  rw [centralizer_uP]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := locH3) (K := co2P) inf_le_left).toEquiv,
    card_locH3]
  norm_num

theorem l3Inputs_zP :
    L3Inputs zP := by
  have hC : ∀ x : co2P, x ∈ Subgroup.centralizer ({zP} : Set co2P) ↔
      (x : Equiv.Perm (Fin 2300)) ∈ locC := fun x => by
    rw [← locC_subgroupOf_eq, Subgroup.mem_subgroupOf]
  have hmap : ∀ F : Subgroup co2P, F ≤ Subgroup.centralizer ({zP} : Set co2P) →
      F.map co2P.subtype ≤ locC := by
    rintro F hF _ ⟨x, hx, rfl⟩
    exact (hC x).1 (hF hx)
  refine ⟨fun F hF hFab => ?_, fun F hF hFab hF27 u hu2 huF hut => Subtype.ext ?_⟩
  · have h := card_le_of_isElemAbelian_locC (hmap F hF) (hFab.map co2P.subtype)
    rwa [Subgroup.card_map_of_injective co2P.subtype_injective] at h
  · refine eq_locZ_of_isElemAbelian_locC (hmap F hF) (hFab.map co2P.subtype)
      (by rw [Subgroup.card_map_of_injective co2P.subtype_injective, hF27])
      ((hC u).1 (Subgroup.mem_centralizer_singleton_iff.2 hut))
      (by rw [Subgroup.orderOf_coe, hu2]) ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 huF x hx)

section Co2


theorem i1016Co2Fact_of_l3Inputs_zP (hz : L3Inputs zP) : I1016Co2Fact := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Co2
  let e' : K ≃* co2P := (e.trans b.symm).trans co2PermEquiv
  have hdata : ∀ t : K, orderOf t = 2 → L3Inputs t := by
    intro t ht
    have ht' : orderOf (e' t) = 2 := (MulEquiv.orderOf_eq e' t).trans ht
    have hz' : L3Inputs (e' t) := by
      rcases isConj_cases_myRep (e' t) ht' with h | h | h
      · exact L3Inputs.of_isConj h hz
      · exact L3Inputs.of_isConj h l3Inputs_tP
      · exact L3Inputs.of_isConj h l3Inputs_uP
    exact L3Inputs.of_mulEquiv e' hz'
  refine CFSG.LocalAnalysis.GLTheoremA.glaTwoLocalRank_le_of_card_le Nat.prime_three
    fun R E hR hR2 hEN hE => ?_
  exact card_le_of_involution_data (fun t ht => (hdata t ht).1)
    (fun t ht => (hdata t ht).2) R E hR hR2 hEN hE

theorem i1016Co2Fact_holds :
    I1016Co2Fact :=
  i1016Co2Fact_of_l3Inputs_zP l3Inputs_zP

end Co2

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
