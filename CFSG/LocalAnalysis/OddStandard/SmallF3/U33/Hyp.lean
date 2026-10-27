module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.HypIndex

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.Blueprint

structure Hyp (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) : Prop where
  ord_t : orderOf t = 2
  mem_centralizer : t ∈ Subgroup.centralizer (L : Set G)
  oddCore_eq_bot : CFSG.oddCore (invCent t) = ⊥
  center_eq_bot : Subgroup.center L = ⊥
  lieModel : LieModel L .PSU 3 3 1
  layer_eq : CFSG.inSubgroup CFSG.layer (invCent t) = L
  normal : (L.subgroupOf (invCent t)).Normal
  centralizer_eq : Subgroup.centralizer (L : Set G) ⊓ invCent t = twoCore t
  isCyclic : IsCyclic (twoCore t)
  mem_twoCore : t ∈ twoCore t
  eq_one_or_eq : ∀ x ∈ twoCore t, x ^ 2 = 1 → x = 1 ∨ x = t
  fstar_eq : CFSG.inSubgroup CFSG.generalizedFitting (invCent t) = twoCore t ⊔ L
  twoCore_inf : twoCore t ⊓ L = ⊥
  relIndex_le : (twoCore t ⊔ L).relIndex (invCent t) ≤ 2
  perfectResidual_eq : CFSG.inSubgroup CFSG.perfectResidual (invCent t) = L

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_involution_mem_centralizer (hC : SmallF3Cyclic G L) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ Subgroup.centralizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (Subgroup.centralizer (L : Set G)) :=
    even_iff_two_dvd.mp hC.standard.2.1
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer (L : Set G)) 2 h2
  exact ⟨(u : G), by rw [Subgroup.orderOf_coe]; exact hu, u.2⟩

theorem hyp_of_smallF3Cyclic
    (hC : SmallF3Cyclic G L)
    (hQ : LieModel (L ⧸ center L) .PSU 3 3 1) {t : G} (ht : orderOf t = 2)
    (htL : t ∈ Subgroup.centralizer (L : Set G)) : Hyp G t L := by
  have hZ : Subgroup.center L = ⊥ := center_eq_bot_of_psu33 hC hQ
  obtain ⟨-, -, hLn, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      hC.standard htL ht
  exact
    { ord_t := ht
      mem_centralizer := htL
      oddCore_eq_bot := hC.balanced t ht
      center_eq_bot := hZ
      lieModel := LieModel.of_quotient_center hZ hQ
      layer_eq := inSubgroup_layer_invCent_eq hC ht htL
      normal := hLn
      centralizer_eq := centralizer_inf_invCent_eq_twoCore hC ht htL
      isCyclic := isCyclic_twoCore hC ht htL
      mem_twoCore := mem_twoCore hC ht htL
      eq_one_or_eq := fun _ hx hx2 =>
        eq_one_or_eq_of_mem_twoCore_of_sq_eq_one hC ht htL hx hx2
      fstar_eq := inSubgroup_generalizedFitting_invCent_eq hC ht htL
      twoCore_inf := twoCore_inf_eq_bot hC hQ ht htL
      relIndex_le := relIndex_twoCore_sup_le_two hC hQ ht htL
      perfectResidual_eq := inSubgroup_perfectResidual_invCent_eq hC hQ ht htL }

theorem exists_hyp_of_smallF3Cyclic
    (hC : SmallF3Cyclic G L)
    (hQ : LieModel (L ⧸ center L) .PSU 3 3 1) : ∃ t : G, Hyp G t L := by
  obtain ⟨t, ht, htL⟩ := exists_involution_mem_centralizer hC
  exact ⟨t, hyp_of_smallF3Cyclic hC hQ ht htL⟩

end CFSG.OddStandard.SmallF3.HarrisU33
