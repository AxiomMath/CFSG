module

public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.DistinctPrimeCoresCommute
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
public import Mathlib.GroupTheory.Nilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G]

theorem mul_comm_of_isPGroup_of_isMulCommutative_sylow [Finite G] {p : ℕ} (hp : p.Prime)
    (P : Sylow p G) (hP : IsMulCommutative (P : Subgroup G)) {S : Subgroup G}
    (hS : IsPGroup p S) {x y : G} (hx : x ∈ S) (hy : y ∈ S) : x * y = y * x := by
  have : Fact p.Prime := ⟨hp⟩
  have := hP
  obtain ⟨g, hg⟩ := exists_forall_inv_mul_mul_mem P.card_eq_multiplicity hS
  have h := setLike_mul_comm (s := (P : Subgroup G)) (hg x hx) (hg y hy)
  have key : g⁻¹ * (x * y) * g = g⁻¹ * (y * x) * g := by
    calc g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by group
      _ = (g⁻¹ * y * g) * (g⁻¹ * x * g) := h
      _ = g⁻¹ * (y * x) * g := by group
  exact mul_left_cancel (mul_right_cancel key)

theorem isMulCommutative_of_isPGroup_of_isMulCommutative_sylow [Finite G] {p : ℕ} (hp : p.Prime)
    (P : Sylow p G) (hP : IsMulCommutative (P : Subgroup G)) {S : Subgroup G}
    (hS : IsPGroup p S) : IsMulCommutative S :=
  IsMulCommutative.of_comm fun x y =>
    Subtype.ext (mul_comm_of_isPGroup_of_isMulCommutative_sylow hp P hP hS x.2 y.2)

theorem le_normalizer_map_subtype_of_characteristic {M : Subgroup G} (N : Subgroup M)
    [N.Characteristic] {L : Subgroup G} (hL : L ≤ normalizer (M : Set G)) :
    L ≤ normalizer ((N.map M.subtype : Subgroup G) : Set G) := by
  rw [le_normalizer_iff]
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
  have hgN : g ∈ normalizer (M : Set G) := hL hg
  set φ := M.normalizerMonoidHom ⟨g, hgN⟩ with hφ
  have hmap : N.map φ.toMonoidHom = N := Subgroup.characteristic_iff_map_eq.1 ‹N.Characteristic› φ
  have hmem : φ y ∈ N := by rw [← hmap]; exact mem_map_of_mem _ hy
  exact ⟨φ y, hmem, by simp [hφ, M.normalizerMonoidHom_apply_apply_coe ⟨g, hgN⟩ y]⟩

theorem le_map_fittingRaw_of_le_normalizer [Finite G] {M K : Subgroup G} (hKM : K ≤ M)
    (hnorm : M ≤ normalizer (K : Set G)) (hnil : Group.IsNilpotent K) :
    K ≤ (fittingRaw M).map M.subtype := by
  have : (K.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hKM).2 hnorm
  have : Group.IsNilpotent K := hnil
  have : Group.IsNilpotent (K.subgroupOf M) :=
    Group.nilpotent_of_mulEquiv (subgroupOfEquivOfLe hKM).symm
  have h := le_fittingRaw_of_normal_of_isNilpotent (N := K.subgroupOf M) inferInstance inferInstance
  calc K = (K.subgroupOf M).map M.subtype := (map_subgroupOf_eq_of_le hKM).symm
    _ ≤ (fittingRaw M).map M.subtype := Subgroup.map_mono h

theorem isNilpotent_map_fittingRaw [Finite G] (M : Subgroup G) :
    Group.IsNilpotent ((fittingRaw M).map M.subtype) :=
  Group.nilpotent_of_mulEquiv ((fittingRaw M).equivMapOfInjective M.subtype M.subtype_injective)

theorem le_normalizer_centralizer_of_normal_subgroupOf {H A : Subgroup G} (hAH : A ≤ H)
    (hA : (A.subgroupOf H).Normal) : H ≤ normalizer (centralizer (A : Set G) : Set G) := by
  rw [le_normalizer_iff]
  intro h hh c hc
  rw [mem_centralizer_iff]
  intro a ha
  have hinv : h⁻¹ * a * h ∈ A := by
    have := hA.conj_mem ⟨a, hAH ha⟩ (by simpa [mem_subgroupOf] using ha) (⟨h, hh⟩ : H)⁻¹
    simpa [mem_subgroupOf] using this
  have hcomm := mem_centralizer_iff.1 hc _ hinv
  calc a * (h * c * h⁻¹) = h * ((h⁻¹ * a * h) * c) * h⁻¹ := by group
    _ = h * (c * (h⁻¹ * a * h)) * h⁻¹ := by rw [hcomm]
    _ = (h * c * h⁻¹) * a := by group

variable [Finite G]

theorem fittingRaw_le_centralizer_subgroupOf {p : ℕ} (hp : p.Prime) (P : Sylow p G)
    (hP : IsMulCommutative (P : Subgroup G)) {H A : Subgroup G} (hAH : A ≤ H)
    (hAnormal : (A.subgroupOf H).Normal) (hA : IsPGroup p A) :
    fittingRaw H ≤ centralizer ((A.subgroupOf H : Subgroup H) : Set H) := by
  have hApc : A.subgroupOf H ≤ pCore p H :=
    le_pCore hp hAnormal (IsPGroup.of_equiv hA (subgroupOfEquivOfLe hAH).symm)
  have habel : ∀ x y : H, x ∈ pCore p H → y ∈ pCore p H → x * y = y * x := by
    intro x y hx hy
    have hS : IsPGroup p ((pCore p H).map H.subtype) := (isPGroup_pCore hp H).map H.subtype
    exact Subtype.ext (mul_comm_of_isPGroup_of_isMulCommutative_sylow hp P hP hS
      (mem_map_of_mem _ hx) (mem_map_of_mem _ hy))
  have habel' : IsMulCommutative (pCore p H) :=
    IsMulCommutative.of_comm fun x y => Subtype.ext (habel _ _ x.2 y.2)
  rw [fittingRaw_eq_iSup_pCore]
  refine iSup₂_le fun q hq => ?_
  rcases eq_or_ne q p with rfl | hqp
  · exact le_trans (Subgroup.le_centralizer (pCore q H))
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hApc))
  · intro x hx
    rw [mem_centralizer_iff]
    intro h hh
    exact mul_comm_of_mem_pCore hp hq hqp.symm (hApc hh) hx

theorem map_fittingRaw_le_centralizer {p : ℕ} (hp : p.Prime) (P : Sylow p G)
    (hP : IsMulCommutative (P : Subgroup G)) {H A : Subgroup G} (hAH : A ≤ H)
    (hAnormal : (A.subgroupOf H).Normal) (hA : IsPGroup p A) :
    (fittingRaw H).map H.subtype ≤ centralizer (A : Set G) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine (fittingRaw_le_centralizer_subgroupOf hp P hP hAH hAnormal hA).trans fun x hx => ?_
  rw [Subgroup.mem_comap, mem_centralizer_iff]
  intro a ha
  exact congrArg Subtype.val
    (mem_centralizer_iff.1 hx ⟨a, hAH ha⟩ (by simpa [mem_subgroupOf] using ha))

theorem map_fittingRaw_eq_map_fittingRaw_centralizer {p : ℕ} (hp : p.Prime) (P : Sylow p G)
    (hP : IsMulCommutative (P : Subgroup G)) {H A : Subgroup G} (hAH : A ≤ H)
    (hAnormal : (A.subgroupOf H).Normal) (hA : IsPGroup p A)
    (hCH : centralizer (A : Set G) ≤ H) :
    (fittingRaw H).map H.subtype
      = (fittingRaw (centralizer (A : Set G))).map (centralizer (A : Set G)).subtype := by
  refine le_antisymm ?_ ?_
  · exact le_map_fittingRaw_of_le_normalizer
      (map_fittingRaw_le_centralizer hp P hP hAH hAnormal hA)
      (le_normalizer_map_subtype_of_characteristic (fittingRaw H) (hCH.trans le_normalizer))
      (isNilpotent_map_fittingRaw H)
  · exact le_map_fittingRaw_of_le_normalizer ((Subgroup.map_subtype_le _).trans hCH)
      (le_normalizer_map_subtype_of_characteristic (fittingRaw (centralizer (A : Set G)))
        (le_normalizer_centralizer_of_normal_subgroupOf hAH hAnormal))
      (isNilpotent_map_fittingRaw _)

end

end CFSG.FeitThompson
