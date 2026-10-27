module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GH74.GLS.TwoThin.Struct

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement


theorem commutator_mem_pPrimeCore_of_component {H : Type} [Group H] [Finite H] {J : Subgroup H}
    (hJ : IsComponent J) {m : H} (hm : m ∈ pPrimePCore 2 H) :
    ∀ j ∈ J, ⁅j, m⁆ ∈ pPrimeCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q : H →* H ⧸ pPrimeCore 2 H := QuotientGroup.mk' (pPrimeCore 2 H) with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hodd : Odd (Nat.card (pPrimeCore 2 H)) := TwoThin.odd_card_pPrimeCore H
  have hsolv : Group.IsSolvable (pPrimeCore 2 H) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hnot : ¬ J ≤ q.ker := by
    rw [hq, QuotientGroup.ker_mk']
    exact LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hJ hsolv
  have hJbar : IsComponent (J.map q) :=
    ⟨LocalCores.isQuasisimple_map hJ.1 q hnot, hJ.2.map hqs⟩
  have hJlayer : J.map q ≤ layer (H ⧸ pPrimeCore 2 H) :=
    LocalCores.component_le_layer hJbar
  have hnil := CFSG.LocalCores.fitting_nilpotent (G := H ⧸ pPrimeCore 2 H)
  have hFn : (pCore 2 (H ⧸ pPrimeCore 2 H)).Normal := CFSG.pCore_normal
  have hF2 : IsPGroup 2 (pCore 2 (H ⧸ pPrimeCore 2 H)) := pCore_isPGroup
  have hFfit : pCore 2 (H ⧸ pPrimeCore 2 H) ≤ fittingSubgroup (H ⧸ pPrimeCore 2 H) :=
    hnil.2.2.1 _ hFn hF2.isNilpotent
  intro j hj
  have hqm : q m ∈ pCore 2 (H ⧸ pPrimeCore 2 H) := hm
  have h0 : ⁅fittingSubgroup (H ⧸ pPrimeCore 2 H), layer (H ⧸ pPrimeCore 2 H)⁆ = ⊥ :=
    CFSG.LocalCores.fitting_layer_commute
  have h1 : ⁅q m, q j⁆ ∈ (⁅fittingSubgroup (H ⧸ pPrimeCore 2 H), layer (H ⧸ pPrimeCore 2 H)⁆ :
      Subgroup (H ⧸ pPrimeCore 2 H)) :=
    Subgroup.commutator_mem_commutator (hFfit hqm) (hJlayer ⟨j, hj, rfl⟩)
  rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  have h2 : q ⁅j, m⁆ = 1 := by
    simp only [commutatorElement_def, map_mul, map_inv]
    have : q m * q j = q j * q m := h1
    calc q j * q m * (q j)⁻¹ * (q m)⁻¹ = (q m * q j) * (q j)⁻¹ * (q m)⁻¹ := by rw [← this]
      _ = 1 := by group
  rw [hq] at h2
  exact (QuotientGroup.eq_one_iff _).mp h2


end CFSG.GH74.GLS.Balance
