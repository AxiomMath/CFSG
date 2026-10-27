module

public import CFSG.ClassicalInvolution.Uniform.UFacts
public import CFSG.ClassicalInvolution.Uniform.UTwinSolv
public import CFSG.ClassicalInvolution.Omega

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification
open scoped MatrixGroups

theorem oddCoreIn_conjSub {G : Type*} [Group G] (g : G) (X : Subgroup G) :
    Balance.oddCoreIn (conjSub g X) = conjSub g (Balance.oddCoreIn X) := by
  let e : X ≃* conjSub g X :=
    X.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hO : (componentClassificationOddCore X).map e.toMonoidHom =
      componentClassificationOddCore (conjSub g X) := OddCore.equiv_invariant e
  have h1 : Balance.oddCoreIn (conjSub g X) =
      ((componentClassificationOddCore X).map e.toMonoidHom).map (conjSub g X).subtype := by
    rw [hO]
    rfl
  rw [h1, Subgroup.map_map]
  change _ = ((componentClassificationOddCore X).map X.subtype).map (MulAut.conj g).toMonoidHom
  rw [Subgroup.map_map]
  rfl

@[expose] def IsIntrinsicU (t : MemberType) {Y : Type*} [Group Y] (K : Subgroup Y) (z : Y) :
    Prop :=
  t.IsSolvableType → Balance.oddCoreIn (Subgroup.centralizer ({z} : Set Y)) ≤ K

namespace IsIntrinsicU

variable {t : MemberType} {Y : Type*} [Group Y] {K : Subgroup Y} {z : Y}

theorem of_not_isSolvableType (h : ¬ t.IsSolvableType) : IsIntrinsicU t K z :=
  fun hs => absurd hs h

theorem conj (h : IsIntrinsicU t K z) (g : Y) :
    IsIntrinsicU t (conjSub g K) (g * z * g⁻¹) := by
  intro hs
  rw [← map_conj_centralizer_singleton g z, show (Subgroup.centralizer ({z} : Set Y)).map
      (MulAut.conj g).toMonoidHom = conjSub g (Subgroup.centralizer ({z} : Set Y)) from rfl,
    oddCoreIn_conjSub]
  exact Subgroup.map_mono (h hs)

theorem conj_centralizer (h : IsIntrinsicU t K z) {g : Y}
    (hg : g ∈ Subgroup.centralizer ({z} : Set Y)) : IsIntrinsicU t (conjSub g K) z := by
  have hgz : g * z * g⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp hg z (Set.mem_singleton z)
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have := h.conj g
  rwa [hgz] at this

end IsIntrinsicU

section Twins

variable {t : MemberType} {G : Type} [Group G] [Finite G] {K J : Subgroup G} {z : G}

theorem oddCoreIn_eq_of_intrinsic (hK : IsClassicalMemberU t K z) (hi : Balance.oddCoreIn
    (Subgroup.centralizer ({z} : Set G)) ≤ K) :
    Balance.oddCoreIn K = Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
  le_antisymm (Balance.oddCoreIn_le_of_isSubnormal hK.subnormal)
    (Balance.le_oddCoreIn_of_normalizes hi
      (hK.le_centralizer.trans (Balance.normalizer_oddCoreIn _)) (Balance.odd_card_oddCoreIn _))

theorem twins_of_memberU_solvable (hK : IsClassicalMemberU t K z) (hJ : IsClassicalMemberU t J z)
    (hs : t.IsSolvableType) (hiK : IsIntrinsicU t K z) (hiJ : IsIntrinsicU t J z) (hne : K ≠ J) :
    J ≤ Subgroup.normalizer (K : Set G) ∧ K ≤ Subgroup.normalizer (J : Set G) ∧
      ⁅K, J⁆ ≤ Balance.oddCoreIn K ⊓ Balance.oddCoreIn J ∧
      ⁅K, J⁆ ≤ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) := by
  have hcomm : ⁅K, J⁆ ≤ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
    (twin_modOdd3 hK.subnormal hJ.subnormal hK.orderOf_eq_two hK.mem hJ.mem
      (hK.nonempty_equiv_sl2Three hs) (hJ.nonempty_equiv_sl2Three hs) (hiK hs)
      (hiJ hs)).resolve_left hne
  have hOK := oddCoreIn_eq_of_intrinsic hK (hiK hs)
  have hOJ := oddCoreIn_eq_of_intrinsic hJ (hiJ hs)
  refine ⟨?_, ?_, ?_, hcomm⟩
  · refine Subgroup.le_normalizer_iff_commutator_le_left.mpr ?_
    rw [hOK] at *
    exact hcomm.trans (hiK hs)
  · refine Subgroup.le_normalizer_iff_commutator_le_left.mpr ?_
    rw [Subgroup.commutator_comm]
    exact hcomm.trans (hiJ hs)
  · rw [hOK, hOJ]
    exact le_inf hcomm hcomm

theorem twins_of_memberU_perfect (hK : IsClassicalMemberU t K z) (hJ : IsClassicalMemberU t J z)
    (hns : ¬ t.IsSolvableType) (hne : K ≠ J) :
    J ≤ Subgroup.normalizer (K : Set G) ∧ K ≤ Subgroup.normalizer (J : Set G) ∧
      ⁅K, J⁆ ≤ Balance.oddCoreIn K ⊓ Balance.oddCoreIn J ∧
      ⁅K, J⁆ ≤ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) := by
  have hA := isTwoComponent_subgroupOf_of_perfect hK.subnormal (hK.perfect hns).commutator_eq_top
    (hK.isQuasisimple_quot hns)
  have hB := isTwoComponent_subgroupOf_of_perfect hJ.subnormal (hJ.perfect hns).commutator_eq_top
    (hJ.isQuasisimple_quot hns)
  exact twoComponents_interaction (isSubnormal_le hK.subnormal) (isSubnormal_le hJ.subnormal)
    hA hB hne

theorem twins_of_memberU (hK : IsClassicalMemberU t K z) (hJ : IsClassicalMemberU t J z)
    (hiK : IsIntrinsicU t K z) (hiJ : IsIntrinsicU t J z) (hne : K ≠ J) :
    J ≤ Subgroup.normalizer (K : Set G) ∧ K ≤ Subgroup.normalizer (J : Set G) ∧
      ⁅K, J⁆ ≤ Balance.oddCoreIn K ⊓ Balance.oddCoreIn J ∧
      ⁅K, J⁆ ≤ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) := by
  by_cases hs : t.IsSolvableType
  · exact twins_of_memberU_solvable hK hJ hs hiK hiJ hne
  · exact twins_of_memberU_perfect hK hJ hs hne

end Twins

end CFSG.ClassicalInvolution.Uniform
