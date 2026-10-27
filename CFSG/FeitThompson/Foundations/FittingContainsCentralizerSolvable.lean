module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.NormalContainsMinimalNormal
import CFSG.FeitThompson.Foundations.MinimalNormalSolvableElemAbelian
import CFSG.FeitThompson.Foundations.MinimalNormalInFittingCenter
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G]

theorem subgroupOf_le_center_of_le_centralizer {H E M : Subgroup G} (hEH : E ≤ H)
    (hM : M ≤ centralizer (H : Set G)) : E.subgroupOf M ≤ center ↥M := fun {_} hx =>
  mem_center_iff.2 fun y => Subtype.ext
    (mem_centralizer_iff.1 (hM y.2) _ (hEH (mem_subgroupOf.1 hx))).symm

theorem isNilpotent_comap_of_le_centralizer {H E : Subgroup G} [E.Normal] (hEH : E ≤ H)
    {N : Subgroup (G ⧸ E)} (hN : Group.IsNilpotent ↥N)
    (hM : Subgroup.comap (QuotientGroup.mk' E) N ≤ centralizer (H : Set G)) :
    Group.IsNilpotent ↥(Subgroup.comap (QuotientGroup.mk' E) N) := by
  set π := QuotientGroup.mk' E with hπ
  set M := Subgroup.comap π N with hMdef
  have hf : ∀ x : ↥M, (π.comp M.subtype) x ∈ N := fun x => x.2
  have hfker : ((π.comp M.subtype).codRestrict N hf).ker = E.subgroupOf M := by
    rw [MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker, hπ, QuotientGroup.ker_mk']
    rfl
  exact Subgroup.isNilpotent_of_ker_le_center ((π.comp M.subtype).codRestrict N hf)
    (hfker ▸ subgroupOf_le_center_of_le_centralizer hEH hM)

theorem centralizer_fittingRaw_le_fittingRaw (G : Type*) [Group G] [Finite G]
    [Group.IsSolvable G] : centralizer (fittingRaw G : Set G) ≤ fittingRaw G := by
  have hFn : (fittingRaw G).Normal := fittingRaw_normal G
  have hCn : (centralizer (fittingRaw G : Set G)).Normal := Subgroup.normal_centralizer
  by_contra hCF
  set E := centralizer (fittingRaw G : Set G) ⊓ fittingRaw G with hEdef
  have hEn : E.Normal := inferInstance
  set π := QuotientGroup.mk' E with hπ
  have hker : π.ker = E := QuotientGroup.ker_mk' E
  have hCbar : ((centralizer (fittingRaw G : Set G)).map π).Normal := inferInstance
  have hCbarne : (centralizer (fittingRaw G : Set G)).map π ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff, hker]
    intro h
    exact hCF (h.trans inf_le_right)
  obtain ⟨N, hNn, hNbot, hNle, hNmin⟩ :=
    exists_normal_ne_bot_le_forall_lt_eq_bot hCbar hCbarne
  have hNn' : N.Normal := hNn
  have hcomm : IsMulCommutative ↥N :=
    isMulCommutative_of_isSolvable_of_forall_normal_lt_eq_bot hNbot hNmin
  let _instCG : CommGroup ↥N := IsMulCommutative.instCommGroup
  have hnilN : Group.IsNilpotent ↥N := CommGroup.isNilpotent
  have hMn : (Subgroup.comap π N).Normal := hNn'.comap π
  have hMC : Subgroup.comap π N ≤ centralizer (fittingRaw G : Set G) := by
    have h1 := Subgroup.comap_mono (f := π) hNle
    rw [Subgroup.comap_map_eq, hker] at h1
    exact h1.trans (sup_le le_rfl inf_le_left)
  have hnilM : Group.IsNilpotent ↥(Subgroup.comap π N) :=
    isNilpotent_comap_of_le_centralizer (H := fittingRaw G) inf_le_right hnilN hMC
  have hMF : Subgroup.comap π N ≤ fittingRaw G :=
    le_fittingRaw_of_normal_of_isNilpotent hMn hnilM
  have hME : Subgroup.comap π N ≤ E := le_inf hMC hMF
  have hmap : (Subgroup.comap π N).map π = N :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective E) N
  refine hNbot (le_bot_iff.1 ?_)
  rw [← hmap]
  calc (Subgroup.comap π N).map π ≤ E.map π := Subgroup.map_mono hME
    _ = ⊥ := (Subgroup.map_eq_bot_iff E).2 hker.ge

theorem le_fittingRaw_of_le_centralizer_fittingRaw [Finite G] [Group.IsSolvable G]
    {H : Subgroup G} (h : H ≤ centralizer (fittingRaw G : Set G)) : H ≤ fittingRaw G :=
  h.trans (centralizer_fittingRaw_le_fittingRaw G)

theorem centralizer_fittingRaw_eq_map_center (G : Type*) [Group G] [Finite G]
    [Group.IsSolvable G] : centralizer (fittingRaw G : Set G) =
      (center ↥(fittingRaw G)).map (fittingRaw G).subtype := by
  rw [map_center_subtype_eq_inf_centralizer, inf_comm,
    inf_eq_left.2 (centralizer_fittingRaw_le_fittingRaw G)]

end

end CFSG.FeitThompson
