module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoInternalHull

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G] [Finite G]

theorem point_hull_hom_to_commutative_trivial (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z w : G) (hzQ : z ∈ Q) (hwQ : w ∈ Q)
    (hz : orderOf z = 2) (hw : orderOf w = 2)
    (hne : z ≠ w) (hcomm : Commute z w)
    {A : Type*} [Group A] [IsMulCommutative A]
    (f : involutionPointHull z →* A) : ∀ x, f x = 1 := by
  let L := involutionPointHull z
  let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
  have hDclass := conjugateQInvolutions_eq_pointClass Q hodd hnormal z hzQ hz
  have hwclass : w ∈ involutionPointClass z := hDclass ▸
    involution_mem_conjugateQInvolutions Q w hwQ hw
  have hprodclass : z * w ∈ involutionPointClass z := hDclass ▸
    conjugateQInvolutions_mul_mem Q hodd z
      (involution_mem_conjugateQInvolutions Q z hzQ hz) w
      (involution_mem_conjugateQInvolutions Q w hwQ hw) hne hcomm
  have hinternal := pointClass_eq_internal_hull_class Q hodd hnormal z hzQ hz
  rw [hinternal] at hwclass hprodclass
  obtain ⟨wL, hwLclass, hwLval⟩ := hwclass
  obtain ⟨pL, hpLclass, hpLval⟩ := hprodclass
  change (wL : G) = w at hwLval
  change (pL : G) = z * w at hpLval
  have hprodL : pL = zL * wL := by
    apply Subtype.ext
    change (pL : G) = z * (wL : G)
    rw [hwLval]
    exact hpLval
  have hzcentral : f zL ∈ Set.center A := by
    change f zL ∈ (Subgroup.center A : Set A)
    rw [Subgroup.center_eq_top]
    trivial
  have hfw : f wL = f zL :=
    ((f.map_isConj hwLclass).eq_of_left_mem_center hzcentral).symm
  have hfp : f pL = f zL :=
    ((f.map_isConj hpLclass).eq_of_left_mem_center hzcentral).symm
  have hmul : f zL * f zL = f zL := by
    calc
      _ = f (zL * wL) := by rw [map_mul, hfw]
      _ = f pL := congrArg f hprodL.symm
      _ = f zL := hfp
  have hfz : f zL = 1 :=
    mul_left_cancel (hmul.trans (mul_one (f zL)).symm)
  have hle : Subgroup.closure (conjugatesOf zL) ≤ f.ker := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    change f x = 1
    exact ((f.map_isConj hx).eq_of_left_mem_center hzcentral).symm.trans hfz
  rw [internal_hull_class_generates Q hodd hnormal z hzQ hz] at hle
  intro x
  exact hle (Subgroup.mem_top x)

theorem point_hull_perfect_of_commuting_involutions (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z w : G) (hzQ : z ∈ Q) (hwQ : w ∈ Q)
    (hz : orderOf z = 2) (hw : orderOf w = 2)
    (hne : z ≠ w) (hcomm : Commute z w) :
    Group.IsPerfect (involutionPointHull z) := by
  let L := involutionPointHull z
  refine ⟨top_unique ?_⟩
  intro x _
  rw [← Abelianization.ker_of L]
  exact point_hull_hom_to_commutative_trivial Q hodd hnormal z w hzQ hwQ hz hw hne hcomm
    Abelianization.of x

theorem point_hull_commutative_factor_subsingleton (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z w : G) (hzQ : z ∈ Q) (hwQ : w ∈ Q)
    (hz : orderOf z = 2) (hw : orderOf w = 2)
    (hne : z ≠ w) (hcomm : Commute z w)
    {A B : Type*} [Group A] [IsMulCommutative A] [Group B]
    (e : involutionPointHull z ≃* A × B) : Subsingleton A := by
  let f : involutionPointHull z →* A := (MonoidHom.fst A B).comp e.toMonoidHom
  have hf := point_hull_hom_to_commutative_trivial Q hodd hnormal z w hzQ hwQ hz hw hne hcomm f
  have haone : ∀ a : A, a = 1 := by
    intro a
    have h := hf (e.symm (a, 1))
    change (e (e.symm (a, 1))).1 = 1 at h
    rw [e.apply_symm_apply] at h
    exact h
  exact ⟨fun a b => (haone a).trans (haone b).symm⟩

end CFSG.ComponentClassification.AschbacherTightEmbedding
