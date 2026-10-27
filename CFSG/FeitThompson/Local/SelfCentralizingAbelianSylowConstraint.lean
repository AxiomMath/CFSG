module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Local.NormalAbelianSylowInPrimeCore
import CFSG.FeitThompson.Local.PiCoreQuotientPiCore
import CFSG.FeitThompson.Local.PCoreSelfCentralizingNoNormalComplement
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
import CFSG.FeitThompson.Local.NormalComplementSylowDerivedIntersection
import CFSG.FeitThompson.Local.FittingOfComplementaryPrimeCore
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.HallImageQuotient

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {X : Type*} [Group X] {p : ℕ}

def conjNormalHom (W T : Subgroup X) [T.Normal] : W →* MulAut T :=
  (MulAut.conjNormal (H := T)).comp W.subtype

@[simp]
theorem coe_conjNormalHom_apply (W T : Subgroup X) [T.Normal] (w : W) (x : T) :
    ((conjNormalHom W T w x : T) : X) = (w : X) * (x : X) * (w : X)⁻¹ := (rfl)

theorem conjNormalHom_eq_one_iff (W T : Subgroup X) [T.Normal] (w : W) :
    conjNormalHom W T w = 1 ↔ ∀ x ∈ T, (w : X) * x = x * (w : X) := by
  constructor
  · intro h x hx
    have hx' : ((conjNormalHom W T w ⟨x, hx⟩ : T) : X) = x := by rw [h]; rfl
    rw [coe_conjNormalHom_apply] at hx'
    calc (w : X) * x = ((w : X) * x * (w : X)⁻¹) * (w : X) := by group
      _ = x * (w : X) := by rw [hx']
  · intro h
    ext x
    have hx : ((conjNormalHom W T w x : T) : X) = (x : X) := by
      rw [coe_conjNormalHom_apply, h (x : X) x.2]
      group
    exact hx

theorem fixedPoints_conjNormalHom (W T : Subgroup X) [T.Normal] :
    FixedPoints.subgroup (conjNormalHom W T).range T
      = (centralizer (W : Set X) ⊓ T).subgroupOf T := by
  ext x
  rw [mem_fixedPoints_range_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨mem_centralizer_iff.2 fun w hw => ?_, x.2⟩
    have hx : (w : X) * (x : X) * (w : X)⁻¹ = (x : X) :=
      congrArg (fun z : T => (z : X)) (h ⟨w, hw⟩)
    calc w * (x : X) = (w * (x : X) * w⁻¹) * w := by group
      _ = (x : X) * w := by rw [hx]
  · rintro ⟨h1, -⟩
    intro a
    ext
    rw [coe_conjNormalHom_apply, mem_centralizer_iff.1 h1 (a : X) a.2]
    group

theorem eq_of_mk'_eq_of_inf_eq_bot {N S : Subgroup X} [N.Normal] (hNS : N ⊓ S = ⊥) {s t : X}
    (hs : s ∈ S) (ht : t ∈ S)
    (h : (QuotientGroup.mk' N) s = (QuotientGroup.mk' N) t) : s = t := by
  have hmem : s⁻¹ * t ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hmem' : s⁻¹ * t ∈ N ⊓ S := ⟨hmem, S.mul_mem (S.inv_mem hs) ht⟩
  rw [hNS, Subgroup.mem_bot] at hmem'
  exact inv_mul_eq_one.mp hmem'

theorem isMulCommutative_of_inf_centralizer_eq {A S : Subgroup X}
    (hAself : centralizer (A : Set X) ⊓ S = A) : IsMulCommutative A :=
  Subgroup.le_centralizer_iff_isMulCommutative.1 fun _ ha =>
    (Subgroup.mem_inf.1 (hAself ▸ ha)).1

theorem le_pComplCore_of_normal_selfCentralizing_of_le_normalizer [Finite X] [Group.IsSolvable X]
    (hp : p.Prime) (hXodd : Odd (Nat.card X)) (S : Sylow p X) {A : Subgroup X}
    (hAS : A ≤ (S : Subgroup X)) (hAnormal : (A.subgroupOf (S : Subgroup X)).Normal)
    (hAself : centralizer (A : Set X) ⊓ (S : Subgroup X) = A) {Y : Subgroup X}
    (hYp : ¬ p ∣ Nat.card Y) (hYA : A ≤ normalizer (Y : Set X)) :
    Y ≤ pComplCore p X := by
  have := Fact.mk hp
  have hAcomm : IsMulCommutative A := isMulCommutative_of_inf_centralizer_eq hAself
  have hNnormal : (pComplCore p X).Normal := pComplCore_normal p X
  set N := pComplCore p X with hN
  set f := QuotientGroup.mk' N with hf
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hNS : N ⊓ (S : Subgroup X) = ⊥ :=
    inf_eq_bot_of_not_dvd_natCard_of_isPGroup hp (not_dvd_natCard_pComplCore hp X) S.isPGroup'
  have hTnormal : (pCore p (X ⧸ N)).Normal := pCore_normal p _
  set T := pCore p (X ⧸ N) with hT
  set Ab := A.map f with hAb
  set Yb := Y.map f with hYb
  have hAT : Ab ≤ T :=
    map_mk'_pComplCore_le_pCore_quotient_of_normal_abelian_sylow hp hXodd S hAS hAnormal hAcomm
  have hTS : T ≤ (S : Subgroup X).map f := by
    have h := (isPGroup_pCore hp (X ⧸ N)).le_sylow_of_normal (S.mapSurjective hfsurj)
    rwa [S.coe_mapSurjective hfsurj] at h
  have hAbself : centralizer (Ab : Set (X ⧸ N)) ⊓ (S : Subgroup X).map f ≤ Ab := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_inf.1 hz).2
    refine ⟨s, ?_, rfl⟩
    have hsA : s ∈ centralizer (A : Set X) ⊓ (S : Subgroup X) := by
      refine Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 fun a ha => ?_, hs⟩
      have hcc := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).1 (f a) ⟨a, ha, rfl⟩
      exact eq_of_mk'_eq_of_inf_eq_bot hNS ((S : Subgroup X).mul_mem (hAS ha) hs)
        ((S : Subgroup X).mul_mem hs (hAS ha)) (by simpa only [map_mul] using hcc)
    rwa [hAself] at hsA
  have hYbp : ¬ p ∣ Nat.card Yb := fun h => hYp (h.trans (natCard_map_mk'_dvd Y N))
  have hYbT : Yb ⊓ T = ⊥ :=
    inf_eq_bot_of_not_dvd_natCard_of_isPGroup hp hYbp (isPGroup_pCore hp _)
  have hYbA : Ab ≤ normalizer (Yb : Set (X ⧸ N)) :=
    (Subgroup.map_mono hYA).trans (Subgroup.le_normalizer_map f)
  have hcomm : ⁅Ab, Yb⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, eq_bot_iff, ← hYbT]
    exact le_inf (Subgroup.le_normalizer_iff_commutator_le_left.1 hYbA)
      ((Subgroup.commutator_mono le_rfl hAT).trans (Subgroup.commutator_le_right _ _))
  have hAbF : Ab ≤ centralizer (Yb : Set (X ⧸ N)) ⊓ T :=
    le_inf (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm) hAT
  have hcop : (Nat.card Yb).Coprime (Nat.card T) := by
    obtain ⟨k, hk⟩ := (isPGroup_pCore hp (X ⧸ N)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).2 hYbp).symm
  have hself : centralizer ((FixedPoints.subgroup (conjNormalHom Yb T).range T : Subgroup T)
      : Set T) ≤ FixedPoints.subgroup (conjNormalHom Yb T).range T := by
    rw [fixedPoints_conjNormalHom]
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hAbF (hAbself (Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 fun a ha => ?_, hTS x.2⟩))
    have hmem : (⟨a, hAT ha⟩ : T) ∈ (centralizer (Yb : Set (X ⧸ N)) ⊓ T).subgroupOf T :=
      Subgroup.mem_subgroupOf.2 (hAbF ha)
    exact congrArg Subtype.val (mem_centralizer_iff.1 hx _ hmem)
  have htriv := eq_one_of_coprime_of_centralizer_fixedPoints_le hp (isPGroup_pCore hp (X ⧸ N))
    (conjNormalHom Yb T) hcop hself
  have hYbCT : Yb ≤ centralizer (T : Set (X ⧸ N)) := fun y hy =>
    mem_centralizer_iff.2 fun t ht =>
      ((conjNormalHom_eq_one_iff Yb T ⟨y, hy⟩).1 (htriv ⟨y, hy⟩) t ht).symm
  have hYbbot : Yb = ⊥ := by
    rcases subsingleton_or_nontrivial (X ⧸ N) with hsub | hnt
    · exact Subsingleton.elim _ _
    · have hcen : centralizer (T : Set (X ⧸ N)) ≤ T :=
        centralizer_pCore_le_pCore hp (pComplCore_quotient_pComplCore p X)
      rw [eq_bot_iff, ← hYbT]
      exact le_inf le_rfl (hYbCT.trans hcen)
  rwa [hYb, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hYbbot

theorem le_pComplCore_of_normal_selfCentralizing_of_natCard_eq [Finite X] [Group.IsSolvable X]
    (hp : p.Prime) (hXodd : Odd (Nat.card X)) {S : Subgroup X}
    (hS : Nat.card S = p ^ (Nat.card X).factorization p) {A : Subgroup X} (hAS : A ≤ S)
    (hAnormal : (A.subgroupOf S).Normal) (hAself : centralizer (A : Set X) ⊓ S = A)
    {Y : Subgroup X} (hYp : (Nat.card Y).Coprime p) (hYA : A ≤ normalizer (Y : Set X)) :
    Y ≤ pComplCore p X := by
  have := Fact.mk hp
  have hSyl : ((Sylow.ofCard S hS : Sylow p X) : Subgroup X) = S := Sylow.coe_ofCard S hS
  exact le_pComplCore_of_normal_selfCentralizing_of_le_normalizer hp hXodd (Sylow.ofCard S hS)
    (by rw [hSyl]; exact hAS) (by rw [hSyl]; exact hAnormal) (by rw [hSyl]; exact hAself)
    ((Nat.Prime.coprime_iff_not_dvd hp).1 hYp.symm) hYA

end

end CFSG.FeitThompson
