module

public import CFSG.LieType.TitsSimplicity.LeviBruhat
public import CFSG.LieType.TitsSimplicity.LeviCT
public import CFSG.LieType.TitsSimplicity.LeviSteinberg
import Mathlib.Data.Finset.Sort

public section

namespace CFSG.LieType.TitsSimplicity.Levi

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem.Restrict

theorem exists_injective_range_eq {m N : ℕ} (e : Fin m → Fin N) :
    ∃ (k : ℕ) (e' : Fin k → Fin N), Function.Injective e' ∧ Set.range e' = Set.range e := by
  refine ⟨_, (Finset.univ.image e).orderEmbOfFin rfl,
    ((Finset.univ.image e).orderEmbOfFin rfl).injective, ?_⟩
  rw [Finset.range_orderEmbOfFin]
  ext x
  simp

theorem iSup_comp_eq_of_range_eq {G : Type*} [Group G] {ι κ N : Type*} {e : ι → N} {e' : κ → N}
    (H : N → Subgroup G) (h : Set.range e' = Set.range e) :
    ⨆ i, H (e' i) = ⨆ i, H (e i) := by
  rw [← iSup_range (g := H) (f := e'), ← iSup_range (g := H) (f := e), h]

theorem isIndecomposable_submatrix_of_range_eq {m k N : ℕ} {A : Matrix (Fin N) (Fin N) ℤ}
    {e : Fin m → Fin N} {e' : Fin k → Fin N} (he' : Function.Injective e')
    (h : Set.range e' = Set.range e) (hA : IsIndecomposable (A.submatrix e e)) :
    IsIndecomposable (A.submatrix e' e') := by
  classical
  rw [isIndecomposable_iff] at hA ⊢
  intro S' hS'
  have key := hA (Finset.univ.filter fun i => ∃ a ∈ S', e i = e' a) (by
    intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and] at hi hj
    obtain ⟨a, ha, hia⟩ := hi
    obtain ⟨b, hb⟩ : e j ∈ Set.range e' := h ▸ ⟨j, rfl⟩
    have hbS : b ∉ S' := fun hbS => hj b hbS hb.symm
    simp only [Matrix.submatrix_apply]
    rw [hia, ← hb]
    exact hS' a ha b hbS)
  rcases key with hempty | huniv
  · left
    rw [Finset.eq_empty_iff_forall_notMem]
    intro a ha
    obtain ⟨i, hi⟩ : e' a ∈ Set.range e := h ▸ ⟨a, rfl⟩
    have hmem : i ∈ Finset.univ.filter fun i => ∃ a ∈ S', e i = e' a := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha, hi⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  · right
    rw [Finset.eq_univ_iff_forall]
    intro b
    obtain ⟨i, hi⟩ : e' b ∈ Set.range e := h ▸ ⟨b, rfl⟩
    have hmem : i ∈ Finset.univ.filter fun i => ∃ a ∈ S', e i = e' a := by
      rw [huniv]
      exact Finset.mem_univ i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨a, ha, hia⟩ := hmem
    exact (he' (hia.symm.trans hi)) ▸ ha

variable {G : Type*} [Group G] {D : UniversalRootDatum G} {m : ℕ} {e : Fin m → Fin D.rank}
  (he : Function.Injective e) {n : Fin D.rank → G} {H : Fin D.rank → Subgroup G}
  (hdiv : D.divisible = ∅)

theorem leviC_eq_of_range_eq {k : ℕ} {e' : Fin k → Fin D.rank}
    (h : Set.range e' = Set.range e) : leviC D e' = leviC D e := by
  have himg : Finset.univ.image e' = Finset.univ.image e := by
    apply Finset.coe_injective
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using h
  unfold leviC
  rw [himg]

set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

variable (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)

include he hct hdiv in
theorem isQuasisimple_leviC_of_injective (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hE : RootGroupCommutators D) (hA : IsIndecomposable (D.cartan.submatrix e e))
    (hperf : Group.IsPerfect ↥(leviC D e)) [Nontrivial ↥(leviC D e)] :
    IsQuasisimple ↥(leviC D e) :=
  CFSG.LieType.TitsSimplicity.isQuasisimple (D := restrict D he) (n := nC D n e) (H := HC D H e)
    (restrict_isCTGroupDatum he hdiv hct) (restrict_steinbergExtras he hdiv hct hext)
    (restrict_bruhatExtras he hdiv hct hBU) (restrict_rootGroupCommutators he hdiv hct hE) hA hperf

include he hct hdiv in
theorem center_leviC_le_of_injective (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) :
    (Subgroup.center ↥(leviC D e)).map (leviC D e).subtype ≤ ⨆ i, H (e i) := by
  have hct' := restrict_isCTGroupDatum he hdiv hct
  have hext' := restrict_steinbergExtras he hdiv hct hext
  have hBU' := restrict_bruhatExtras he hdiv hct hBU
  have hcore : Subgroup.center ↥(leviC D e) ≤ ⨆ i, HC D H e i :=
    (CFSG.LieType.TitsSimplicity.center_eq_normalCore_borel (D := restrict D he)
      (n := nC D n e) (H := HC D H e) hct' hext' hBU').le.trans
      (CFSG.LieType.TitsSimplicity.normalCore_borel_le_iSup (D := restrict D he)
        (n := nC D n e) (H := HC D H e) hct' hBU')
  calc (Subgroup.center ↥(leviC D e)).map (leviC D e).subtype
      ≤ (⨆ i, HC D H e i).map (leviC D e).subtype := Subgroup.map_mono hcore
    _ = ⨆ i, (HC D H e i).map (leviC D e).subtype := Subgroup.map_iSup _ _
    _ ≤ ⨆ i, H (e i) := iSup_mono fun i => by
      rw [HC, Subgroup.subgroupOf_map_subtype]
      exact inf_le_left

include hct hdiv in
theorem isQuasisimple_leviC (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hE : RootGroupCommutators D) (hA : IsIndecomposable (D.cartan.submatrix e e))
    (hperf : Group.IsPerfect ↥(leviC D e)) [Nontrivial ↥(leviC D e)] :
    IsQuasisimple ↥(leviC D e) := by
  obtain ⟨k, e', he', hr⟩ := exists_injective_range_eq e
  have hL : leviC D e' = leviC D e := leviC_eq_of_range_eq hr
  have hperf' : Group.IsPerfect ↥(leviC D e') := by
    rw [hL]
    exact hperf
  have hnt : Nontrivial ↥(leviC D e') := by
    rw [hL]
    infer_instance
  have hq := isQuasisimple_leviC_of_injective he' hdiv hct hext hBU hE
    (isIndecomposable_submatrix_of_range_eq he' hr hA) hperf'
  rwa [hL] at hq

include hct hdiv in
theorem center_leviC_le (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) :
    (Subgroup.center ↥(leviC D e)).map (leviC D e).subtype ≤ ⨆ i, H (e i) := by
  obtain ⟨k, e', he', hr⟩ := exists_injective_range_eq e
  have hL : leviC D e' = leviC D e := leviC_eq_of_range_eq hr
  have hle := center_leviC_le_of_injective he' hdiv hct hext hBU
  rw [hL, iSup_comp_eq_of_range_eq H hr] at hle
  exact hle

end CFSG.LieType.TitsSimplicity.Levi
