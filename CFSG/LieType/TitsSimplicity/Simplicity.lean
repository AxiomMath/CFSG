module

public import CFSG.LieType.TitsSimplicity.Core
public import CFSG.LieType.TitsSimplicity.Indecomposable
public import CFSG.LieType.TitsSimplicity.Unipotent
public import CFSG.Foundations.Basic

public section

namespace CFSG.LieType.TitsSimplicity

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {K : Type*} [Group K]

theorem eq_top_of_sup_eq_top {B M : Subgroup K} [M.Normal] (hperf : Group.IsPerfect K)
    (hB : Group.IsSolvable B) (h : M ⊔ B = ⊤) : M = ⊤ := by
  have := hperf
  have := hB
  have hsurj : Function.Surjective ((QuotientGroup.mk' M).comp B.subtype) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M y
    have hg : g ∈ M ⊔ B := h ▸ Subgroup.mem_top g
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hg
    obtain ⟨m, hm, b, hb, rfl⟩ := hg
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff m).2 hm, one_mul]
  have : Group.IsSolvable (K ⧸ M) := Group.isSolvable_of_surjective hsurj
  rw [eq_top_iff]
  intro g _
  by_contra hg
  have : Nontrivial (K ⧸ M) :=
    ⟨⟨(g : K ⧸ M), 1, fun h' => hg ((QuotientGroup.eq_one_iff g).1 h')⟩⟩
  exact Group.IsPerfect.not_isSolvable (K ⧸ M) inferInstance

theorem isSimpleGroup_quotient_center_of_forall [Nontrivial K] (hperf : Group.IsPerfect K)
    (h : ∀ M : Subgroup K, M.Normal → M ≤ Subgroup.center K ∨ M = ⊤) :
    IsSimpleGroup (K ⧸ Subgroup.center K) := by
  have := hperf
  obtain ⟨g, hg⟩ : ∃ g, g ∉ Subgroup.center K := by
    by_contra! h'
    have : IsMulCommutative K :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.1 (h' a) b).symm⟩⟩
    exact Group.IsPerfect.not_isMulCommutative K this
  have : Nontrivial (K ⧸ Subgroup.center K) :=
    ⟨⟨(g : K ⧸ Subgroup.center K), 1, fun h' => hg ((QuotientGroup.eq_one_iff g).1 h')⟩⟩
  refine ⟨fun N hN => ?_⟩
  rcases h _ (hN.comap (QuotientGroup.mk' (Subgroup.center K))) with hle | htop
  · left
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ y
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff g).2 (hle hy)
  · right
    rw [eq_top_iff]
    intro y _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have : g ∈ N.comap (QuotientGroup.mk' (Subgroup.center K)) := htop ▸ Subgroup.mem_top g
    exact this

theorem isQuasisimple_of_forall [Nontrivial K] (hperf : Group.IsPerfect K)
    (h : ∀ M : Subgroup K, M.Normal → M ≤ Subgroup.center K ∨ M = ⊤) : IsQuasisimple K := by
  have hs := isSimpleGroup_quotient_center_of_forall hperf h
  have := hperf
  refine ⟨hperf, hs, ?_⟩
  by_contra! hc
  have : IsMulCommutative (K ⧸ Subgroup.center K) := ⟨⟨hc⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (K ⧸ Subgroup.center K) this

variable {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

theorem isIndecomposable_cartan_iff_connected [NeZero D.rank] :
    IsIndecomposable D.cartan ↔ (dynkinGraph D.cartan).Connected :=
  ⟨connected_of_isIndecomposable fun _ _ h => D.isFiniteType.apply_eq_zero_iff.1 h,
    isIndecomposable_of_connected⟩

variable (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

include hct hext in
theorem forall_n_notMem_or_forall_n_mem (hA : IsIndecomposable D.cartan) (M : Subgroup K)
    [M.Normal] : (∀ i, n i ∉ M ⊔ borel D H) ∨ ∀ i, n i ∈ M ⊔ borel D H := by
  classical
  rcases isIndecomposable_iff.1 hA (Finset.univ.filter fun i => n i ∈ M ⊔ borel D H)
      (fun i hi j hj => cartan_eq_zero_of_n_mem_sup hct hext (Finset.mem_filter.1 hi).2
        fun hj' => hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj'⟩)) with h | h
  · refine Or.inl fun i hi => ?_
    have : i ∈ Finset.univ.filter fun i => n i ∈ M ⊔ borel D H :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
    rw [h] at this
    exact Finset.notMem_empty _ this
  · refine Or.inr fun i => ?_
    have : i ∈ Finset.univ.filter fun i => n i ∈ M ⊔ borel D H := by
      rw [h]
      exact Finset.mem_univ i
    exact (Finset.mem_filter.1 this).2

include hct hext in
theorem le_borel_or_sup_eq_top (hA : IsIndecomposable D.cartan) (M : Subgroup K) [M.Normal] :
    M ≤ borel D H ∨ M ⊔ borel D H = ⊤ := by
  rcases forall_n_notMem_or_forall_n_mem hct hext hA M with h | h
  · exact Or.inl (le_sup_left.trans (le_borel_of_forall_n_notMem hct hext le_sup_right h))
  · exact Or.inr (eq_top_of_forall_n_mem hct le_sup_right h)

include hct hext in
theorem le_center_or_eq_top_of_isSolvable (hBU : BruhatExtras D H)
    (hA : IsIndecomposable D.cartan) (hperf : Group.IsPerfect K)
    (hU : Group.IsSolvable (posUnipotent D)) (M : Subgroup K) [M.Normal] :
    M ≤ Subgroup.center K ∨ M = ⊤ := by
  rcases le_borel_or_sup_eq_top hct hext hA M with h | h
  · left
    rw [center_eq_normalCore_borel hct hext hBU]
    exact Subgroup.normal_le_normalCore.2 h
  · exact Or.inr (eq_top_of_sup_eq_top hperf (isSolvable_borel hct hext hU) h)

include hct hext in
theorem isSimpleGroup_quotient_center_of_isSolvable [Nontrivial K] (hBU : BruhatExtras D H)
    (hA : IsIndecomposable D.cartan) (hperf : Group.IsPerfect K)
    (hU : Group.IsSolvable (posUnipotent D)) : IsSimpleGroup (K ⧸ Subgroup.center K) :=
  isSimpleGroup_quotient_center_of_forall hperf fun M _ =>
    le_center_or_eq_top_of_isSolvable hct hext hBU hA hperf hU M

include hct hext in
theorem isQuasisimple_of_isSolvable [Nontrivial K] (hBU : BruhatExtras D H)
    (hA : IsIndecomposable D.cartan) (hperf : Group.IsPerfect K)
    (hU : Group.IsSolvable (posUnipotent D)) : IsQuasisimple K :=
  isQuasisimple_of_forall hperf fun M _ =>
    le_center_or_eq_top_of_isSolvable hct hext hBU hA hperf hU M

include hct hext in
theorem le_center_or_eq_top (hBU : BruhatExtras D H) (hE : RootGroupCommutators D)
    (hA : IsIndecomposable D.cartan) (hperf : Group.IsPerfect K) (M : Subgroup K) [M.Normal] :
    M ≤ Subgroup.center K ∨ M = ⊤ :=
  le_center_or_eq_top_of_isSolvable hct hext hBU hA hperf (isSolvable_posUnipotent hext hE) M

include hct hext in
theorem isSimpleGroup_quotient_center [Nontrivial K] (hBU : BruhatExtras D H)
    (hE : RootGroupCommutators D) (hA : IsIndecomposable D.cartan) (hperf : Group.IsPerfect K) :
    IsSimpleGroup (K ⧸ Subgroup.center K) :=
  isSimpleGroup_quotient_center_of_isSolvable hct hext hBU hA hperf
    (isSolvable_posUnipotent hext hE)

include hct hext in
theorem isQuasisimple [Nontrivial K] (hBU : BruhatExtras D H) (hE : RootGroupCommutators D)
    (hA : IsIndecomposable D.cartan) (hperf : Group.IsPerfect K) : IsQuasisimple K :=
  isQuasisimple_of_isSolvable hct hext hBU hA hperf (isSolvable_posUnipotent hext hE)

end CFSG.LieType.TitsSimplicity
