module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.HypOut

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem commutator_le_of_index_le_two {X : Type*} [Group X] [Finite X]
    (K : Subgroup X) [K.Normal] (hK : K.index ≤ 2) :
    _root_.commutator X ≤ K := by
  rcases Nat.lt_or_ge K.index 2 with hlt | hge
  · have h1 : K.index = 1 := by
      have h0 := K.index_ne_zero_of_finite
      omega
    rw [Subgroup.index_eq_one] at h1
    rw [h1]
    exact le_top
  · have h2 : K.index = 2 := le_antisymm hK hge
    change ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ K
    rw [Subgroup.commutator_le]
    intro x _ y _
    have hx2 : x ^ 2 ∈ K := Subgroup.sq_mem_of_index_two h2 x
    have hy2 : y ^ 2 ∈ K := Subgroup.sq_mem_of_index_two h2 y
    have hxy2 : (x * y) ^ 2 ∈ K := Subgroup.sq_mem_of_index_two h2 (x * y)
    have hxinv : x⁻¹ = x * (x ^ 2)⁻¹ := by group
    have hyinv : y⁻¹ = y * (y ^ 2)⁻¹ := by group
    have hconj : y⁻¹ * (x ^ 2)⁻¹ * y ∈ K := by
      simpa using (inferInstance : K.Normal).conj_mem (x ^ 2)⁻¹ (K.inv_mem hx2) y⁻¹
    rw [commutatorElement_def, hxinv, hyinv]
    have hrw : x * y * (x * (x ^ 2)⁻¹) * (y * (y ^ 2)⁻¹) =
        (x * y) ^ 2 * (y⁻¹ * (x ^ 2)⁻¹ * y) * (y ^ 2)⁻¹ := by
      rw [pow_two (x * y)]
      group
    rw [hrw]
    exact K.mul_mem (K.mul_mem hxy2 hconj) (K.inv_mem hy2)

private theorem commutator_sup_eq_right {X : Type*} [Group X] {P R : Subgroup X}
    [P.Normal] [R.Normal] (hPP : ⁅P, P⁆ = ⊥) (hPR : ⁅P, R⁆ = ⊥) (hRR : ⁅R, R⁆ = R) :
    ⁅P ⊔ R, P ⊔ R⁆ = R := by
  haveI : (P ⊔ R).Normal := inferInstance
  have hRP : ⁅R, P⁆ = ⊥ := by rw [Subgroup.commutator_comm, hPR]
  calc ⁅P ⊔ R, P ⊔ R⁆
      = ⁅P ⊔ R, P⁆ ⊔ ⁅P ⊔ R, R⁆ := Subgroup.commutator_sup_left (P ⊔ R) P R
    _ = (⁅P, P⁆ ⊔ ⁅R, P⁆) ⊔ (⁅P, R⁆ ⊔ ⁅R, R⁆) := by
          rw [Subgroup.commutator_sup_right P R P, Subgroup.commutator_sup_right P R R]
    _ = R := by rw [hPP, hRP, hPR, hRR]; simp

theorem inSubgroup_generalizedFitting_invCent_eq (hC : SmallF3Cyclic G L) {t : G}
    (ht : orderOf t = 2) (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    CFSG.inSubgroup CFSG.generalizedFitting (invCent t) = twoCore t ⊔ L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOdd : CFSG.oddCore ↥(invCent t) = ⊥ := hC.balanced t ht
  have hF : CFSG.fittingSubgroup ↥(invCent t) = CFSG.pCore 2 ↥(invCent t) := by
    refine le_antisymm ?_ (CFSG.pCore_le_fitting _ 2)
    have h := CFSG.WholeGroup.fittingSubgroup_le_pCore_two_sup_oddCore
      (G := ↥(invCent t))
    rw [hOdd] at h
    simpa using h
  have hPmap : (CFSG.pCore 2 ↥(invCent t)).map (invCent t).subtype = twoCore t := rfl
  have hLmap : (CFSG.layer ↥(invCent t)).map (invCent t).subtype = L :=
    inSubgroup_layer_invCent_eq hC ht htL
  change (CFSG.generalizedFitting ↥(invCent t)).map (invCent t).subtype = twoCore t ⊔ L
  rw [CFSG.generalizedFitting.eq_sup, Subgroup.map_sup, hF, hPmap, hLmap]

theorem twoCore_inf_eq_bot (hC : SmallF3Cyclic G L)
    (hQ : LieModel (L ⧸ center L) .PSU 3 3 1) {t : G}
    (ht : orderOf t = 2) (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    twoCore t ⊓ L = ⊥ := by
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_psu33 hC hQ
  have hcent : twoCore t ≤ Subgroup.centralizer (L : Set G) :=
    (centralizer_inf_invCent_eq_twoCore hC ht htL).ge.trans inf_le_left
  refine (Subgroup.eq_bot_iff_forall (twoCore t ⊓ L)).2 fun x hx => ?_
  obtain ⟨hxP, hxL⟩ := Subgroup.mem_inf.mp hx
  have hxcent : x ∈ Subgroup.centralizer (L : Set G) := hcent hxP
  have hxcenter : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by
      simpa using Subgroup.mem_centralizer_iff.mp hxcent (g : G) g.2)
  have hxmap : x ∈ (Subgroup.center ↥L).map L.subtype := ⟨⟨x, hxL⟩, hxcenter, rfl⟩
  rw [hZ, Subgroup.map_bot] at hxmap
  simpa using hxmap

theorem inSubgroup_perfectResidual_invCent_eq
    (hC : SmallF3Cyclic G L)
    (hQ : LieModel (L ⧸ center L) .PSU 3 3 1) {t : G}
    (ht : orderOf t = 2) (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    CFSG.inSubgroup CFSG.perfectResidual (invCent t) = L := by
  let P : Subgroup ↥(invCent t) := CFSG.pCore 2 ↥(invCent t)
  let L' : Subgroup ↥(invCent t) := L.subgroupOf (invCent t)
  let K : Subgroup ↥(invCent t) := P ⊔ L'
  obtain ⟨-, hLH, hLn, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      hC.standard htL ht
  haveI : P.Normal := CFSG.pCore_normal
  haveI : L'.Normal := hLn
  haveI : K.Normal := inferInstance
  have hPmap : P.map (invCent t).subtype = twoCore t := rfl
  have hLmap : L'.map (invCent t).subtype = L := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hLH
  haveI hCyc : IsCyclic (twoCore t) := isCyclic_twoCore hC ht htL
  haveI hComm : IsMulCommutative (twoCore t) := IsCyclic.isMulCommutative
  have hPP : ⁅P, P⁆ = ⊥ := by
    rw [← Subgroup.map_subtype_inj (H := invCent t)]
    rw [Subgroup.map_commutator, hPmap, Subgroup.map_bot,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer (twoCore t)
  have hPL : ⁅P, L'⁆ = ⊥ := by
    rw [← Subgroup.map_subtype_inj (H := invCent t)]
    rw [Subgroup.map_commutator, hPmap, hLmap, Subgroup.map_bot,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (centralizer_inf_invCent_eq_twoCore hC ht htL).ge.trans inf_le_left
  have hLL' : ⁅L', L'⁆ = L' := by
    haveI : Group.IsPerfect ↥L := ⟨hC.standard.1.1⟩
    rw [← Subgroup.map_subtype_inj (H := invCent t)]
    rw [Subgroup.map_commutator, hLmap, Subgroup.commutator_eq_self]
  have hKcomm : ⁅K, K⁆ = L' := by
    have := commutator_sup_eq_right (P := P) (R := L') hPP hPL hLL'
    simpa only [K] using this
  have hsub' : (twoCore t ⊔ L).subgroupOf (invCent t) = P ⊔ L' := by
    change ((CFSG.pCore 2 ↥(invCent t)).map (invCent t).subtype ⊔ L).subgroupOf
      (invCent t) = P ⊔ L'
    rw [Subgroup.subgroupOf_sup
      (Subgroup.map_subtype_le (K := CFSG.pCore 2 ↥(invCent t))) hLH]
    have hPsub : ((CFSG.pCore 2 ↥(invCent t)).map (invCent t).subtype).subgroupOf
        (invCent t) = P :=
      Subgroup.comap_map_eq_self_of_injective (invCent t).subtype_injective
        (CFSG.pCore 2 ↥(invCent t))
    rw [hPsub]
  have hsub : K = (twoCore t ⊔ L).subgroupOf (invCent t) := by
    show P ⊔ L' = (twoCore t ⊔ L).subgroupOf (invCent t)
    exact hsub'.symm
  have hKindex : K.index ≤ 2 := by
    rw [hsub]
    change (twoCore t ⊔ L).relIndex (invCent t) ≤ 2
    exact relIndex_twoCore_sup_le_two hC hQ ht htL
  have hcomm : _root_.commutator ↥(invCent t) ≤ K :=
    commutator_le_of_index_le_two K hKindex
  have hper : CFSG.perfectResidual ↥(invCent t) ≤ L' := by
    calc CFSG.perfectResidual ↥(invCent t)
        = ⨅ n, derivedSeries ↥(invCent t) n := rfl
      _ ≤ derivedSeries ↥(invCent t) 2 := iInf_le _ 2
      _ = ⁅_root_.commutator ↥(invCent t), _root_.commutator ↥(invCent t)⁆ := by
            rw [show (2 : ℕ) = 1 + 1 from rfl, derivedSeries_succ, derivedSeries_one]
      _ ≤ ⁅K, K⁆ := Subgroup.commutator_mono hcomm hcomm
      _ = L' := hKcomm
  have hle : L' ≤ CFSG.perfectResidual ↥(invCent t) := by
    change L' ≤ ⨅ n, derivedSeries ↥(invCent t) n
    refine le_iInf fun n => ?_
    induction n with
    | zero => exact le_top
    | succ n ih =>
        rw [derivedSeries_succ, ← hLL']
        exact Subgroup.commutator_mono ih ih
  have hEq : CFSG.perfectResidual ↥(invCent t) = L' := le_antisymm hper hle
  calc CFSG.inSubgroup CFSG.perfectResidual (invCent t)
      = (CFSG.perfectResidual ↥(invCent t)).map (invCent t).subtype := rfl
    _ = L'.map (invCent t).subtype := by rw [hEq]
    _ = L := hLmap

end CFSG.OddStandard.SmallF3.HarrisU33
