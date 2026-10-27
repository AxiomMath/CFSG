module

public import CFSG.FeitThompson.Definitions.LocalComplementaryPrimeConstraint
public import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
public import CFSG.FeitThompson.Local.SimpleGroupNormalizerProper
import Mathlib.Data.Rat.Floor

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G]

theorem map_centralizer_equiv (φ : G ≃* G) (s : Set G) :
    (centralizer s).map φ.toMonoidHom = centralizer (φ '' s) := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [Subgroup.mem_centralizer_iff, Set.mem_image, forall_exists_index, and_imp]
  constructor
  · rintro h y z hz rfl
    have h2 := h z hz
    have : φ (z * φ.symm x) = φ (φ.symm x * z) := by rw [h2]
    simpa using this
  · intro h y hy
    have h2 := h (φ y) y hy rfl
    exact φ.injective (by simpa using h2)

theorem map_centralizer_conj {A : Subgroup G} {g : G} (hg : g ∈ normalizer (A : Set G)) :
    (centralizer (A : Set G)).map (MulAut.conj g).toMonoidHom = centralizer (A : Set G) := by
  rw [map_centralizer_equiv, mem_normalizer_iff_conj_image_eq.1 hg]

theorem le_centralizer_of_le_centralizer {A Y : Subgroup G} (h : Y ≤ centralizer (A : Set G)) :
    A ≤ centralizer (Y : Set G) :=
  fun a ha => mem_centralizer_iff.2 fun _ hy => ((mem_centralizer_iff.1 (h hy)) a ha).symm

theorem le_centralizer_of_inf_eq_bot {L A D : Subgroup G} (hAL : A ≤ L) (hDL : D ≤ L)
    (hA : L ≤ normalizer (A : Set G)) (hD : L ≤ normalizer (D : Set G)) (h : A ⊓ D = ⊥) :
    D ≤ centralizer (A : Set G) := by
  have hA' : (A.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hAL).2 hA
  have hD' : (D.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hDL).2 hD
  have hdisj : Disjoint (A.subgroupOf L) (D.subgroupOf L) := by
    rw [disjoint_iff_inf_le]
    intro x hx
    have hxAD : (x : G) ∈ A ⊓ D := ⟨hx.1, hx.2⟩
    rw [h, Subgroup.mem_bot] at hxAD
    simpa only [Subgroup.mem_bot] using Subtype.ext hxAD
  exact fun d hd => mem_centralizer_iff.2 fun a ha =>
    congrArg Subtype.val (Subgroup.commute_of_normal_of_disjoint _ _ hA' hD' hdisj
      (⟨a, hAL ha⟩ : L) (⟨d, hDL hd⟩ : L) ha hd)

variable [Finite G] {π : Set ℕ}

theorem map_piCore_le (π : Set ℕ) (H : Subgroup G) : (piCore π H).map H.subtype ≤ H :=
  Subgroup.map_subtype_le _

theorem subgroupOf_map_piCore (π : Set ℕ) (H : Subgroup G) :
    ((piCore π H).map H.subtype).subgroupOf H = piCore π H := by
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]

theorem isPiSubgroup_map_piCore (π : Set ℕ) (H : Subgroup G) :
    IsPiSubgroup π ((piCore π H).map H.subtype) :=
  isPiSubgroup_map_subtype_iff.2 (isPiSubgroup_piCore _ _)

theorem le_normalizer_map_piCore (π : Set ℕ) (H : Subgroup G) :
    H ≤ normalizer (((piCore π H).map H.subtype : Subgroup G) : Set G) := by
  refine (normal_subgroupOf_iff_le_normalizer (map_piCore_le π H)).1 ?_
  rw [subgroupOf_map_piCore]
  exact piCore_normal _ _

theorem le_map_piCore_of_le_of_le_normalizer {H N : Subgroup G} (hNH : N ≤ H)
    (hnorm : H ≤ normalizer (N : Set G)) (hπ : IsPiSubgroup π N) :
    N ≤ (piCore π H).map H.subtype := by
  have h1 : (N.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hnorm
  have h2 : IsPiSubgroup π (N.subgroupOf H) := by
    rw [← isPiSubgroup_map_subtype_iff, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hNH]
    exact hπ
  have h3 := Subgroup.map_mono (f := H.subtype) (le_piCore h1 h2)
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hNH] at h3

variable {A : Subgroup G}

def constrainedCentralizerCore (A : Subgroup G) : Subgroup G :=
  (piCore (subgroupPrimeSupportCompl A) (centralizer (A : Set G))).map
    (centralizer (A : Set G)).subtype

theorem constrainedCentralizerCore_eq (A : Subgroup G) :
    constrainedCentralizerCore A =
      (piCore (subgroupPrimeSupportCompl A) (centralizer (A : Set G))).map
        (centralizer (A : Set G)).subtype := (rfl)

theorem constrainedCentralizerCore_le_centralizer (A : Subgroup G) :
    constrainedCentralizerCore A ≤ centralizer (A : Set G) :=
  map_piCore_le _ _

theorem isPiSubgroup_constrainedCentralizerCore (A : Subgroup G) :
    IsPiSubgroup (subgroupPrimeSupportCompl A) (constrainedCentralizerCore A) :=
  isPiSubgroup_map_piCore _ _

theorem centralizer_le_normalizer_constrainedCentralizerCore (A : Subgroup G) :
    centralizer (A : Set G) ≤ normalizer (constrainedCentralizerCore A : Set G) :=
  le_normalizer_map_piCore _ _

theorem le_constrainedCentralizerCore {N : Subgroup G} (hNC : N ≤ centralizer (A : Set G))
    (hnorm : centralizer (A : Set G) ≤ normalizer (N : Set G))
    (hπ : IsPiSubgroup (subgroupPrimeSupportCompl A) N) :
    N ≤ constrainedCentralizerCore A :=
  le_map_piCore_of_le_of_le_normalizer hNC hnorm hπ

theorem isGreatest_constrainedCentralizerCore (A : Subgroup G) :
    IsGreatest {N : Subgroup G | N ≤ centralizer (A : Set G) ∧
      centralizer (A : Set G) ≤ normalizer (N : Set G) ∧
      IsPiSubgroup (subgroupPrimeSupportCompl A) N} (constrainedCentralizerCore A) :=
  ⟨⟨constrainedCentralizerCore_le_centralizer A,
      centralizer_le_normalizer_constrainedCentralizerCore A,
      isPiSubgroup_constrainedCentralizerCore A⟩,
    fun _ hN => le_constrainedCentralizerCore hN.1 hN.2.1 hN.2.2⟩

theorem le_constrainedCentralizerCore_of_isConstrained [IsSimpleGroup G]
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) {Y : Subgroup G}
    (hY : Y ≤ centralizer (A : Set G))
    (hYπ : IsPiSubgroup (subgroupPrimeSupportCompl A) Y) :
    Y ≤ constrainedCentralizerCore A := by
  set L : Subgroup G := A ⊔ centralizer (A : Set G) with hLdef
  have hAL : A ≤ L := le_sup_left
  have hCL : centralizer (A : Set G) ≤ L := le_sup_right
  have hLN : L ≤ normalizer (A : Set G) :=
    sup_le Subgroup.le_normalizer (centralizer_le_normalizer _)
  have hLtop : L < ⊤ := lt_of_le_of_lt hLN (normalizer_lt_top_of_isSimpleGroup hAbot hAtop)
  set D : Subgroup G := (piCore (subgroupPrimeSupportCompl A) L).map L.subtype with hDdef
  have hYD : Y ≤ D :=
    hcon.le_map_piCore hLtop hAL (hY.trans hCL) hYπ
      ((le_centralizer_of_le_centralizer hY).trans (centralizer_le_normalizer _))
  have hDL : D ≤ L := map_piCore_le _ _
  have hDN : L ≤ normalizer (D : Set G) := le_normalizer_map_piCore _ _
  have hDπ : IsPiSubgroup (subgroupPrimeSupportCompl A) D := isPiSubgroup_map_piCore _ _
  have hAD : A ⊓ D = ⊥ := inf_eq_bot_of_isPiSubgroup_subgroupPrimeSupportCompl hDπ
  have hDC : D ≤ centralizer (A : Set G) := le_centralizer_of_inf_eq_bot hAL hDL hLN hDN hAD
  exact hYD.trans (le_constrainedCentralizerCore hDC (hCL.trans hDN) hDπ)

theorem map_conj_constrainedCentralizerCore_le {g : G} (hg : g ∈ normalizer (A : Set G)) :
    (constrainedCentralizerCore A).map (MulAut.conj g).toMonoidHom ≤
      constrainedCentralizerCore A := by
  refine le_constrainedCentralizerCore ?_ ?_
    ((isPiSubgroup_constrainedCentralizerCore A).map_equiv _)
  · rw [← map_centralizer_conj hg]
    exact Subgroup.map_mono (constrainedCentralizerCore_le_centralizer A)
  · rw [← map_centralizer_conj hg]
    calc (centralizer (A : Set G)).map (MulAut.conj g).toMonoidHom
        ≤ (normalizer (constrainedCentralizerCore A : Set G)).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono (centralizer_le_normalizer_constrainedCentralizerCore A)
      _ = _ := Subgroup.map_normalizer_eq_of_bijective _ (MulEquiv.bijective (MulAut.conj g))

theorem normalizer_le_normalizer_constrainedCentralizerCore (A : Subgroup G) :
    normalizer (A : Set G) ≤ normalizer (constrainedCentralizerCore A : Set G) := by
  intro g hg
  refine mem_normalizer_iff_map_conj_eq.2
    (le_antisymm (map_conj_constrainedCentralizerCore_le hg) ?_)
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
    (map_conj_constrainedCentralizerCore_le (A := A) ((normalizer (A : Set G)).inv_mem hg))
  rw [Subgroup.map_map] at h2
  refine le_trans (le_of_eq ?_) h2
  have hcomp : ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulAut.conj_apply,
      MonoidHom.id_apply, MulEquiv.coe_toMonoidHom]
    group
  rw [hcomp]
  simp

end

end CFSG.FeitThompson
