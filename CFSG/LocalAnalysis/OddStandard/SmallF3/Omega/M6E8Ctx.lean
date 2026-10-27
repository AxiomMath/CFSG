module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Statements
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Chain
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64TwoA
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

structure M6E8Ctx (t : G) (L : Subgroup G) (y : G) (X Y T : Subgroup G) : Prop where
  setting : Sec3SettingLB G t L
  hyp62 : Asc82Hyp62 G
  hy : orderOf y = 2
  hXC : InC X
  hXF : InFStar X
  hX29 : IsL29 X
  hYc : IsComponentIn Y (centralizer ({y} : Set G))
  hXY : X ≤ Y
  hYC : InCStar Y
  hYF : InFStar Y
  hY6 : IsOmega6Minus Y
  hT : IsSylow2Of T (centralizer (X : Set G))
  hyT : y ∈ T
  hab : CFSG.Open.IsElemAbelian 2 (T ⊓ centralizer ({y} : Set G))
  h8 : Nat.card ↥(T ⊓ centralizer ({y} : Set G)) = 8
  h2 : Nat.card ↥(T ⊓ centralizer (Y : Set G)) = 2
  hne : T ⊓ centralizer ({y} : Set G) ≠ T

namespace M6E8Ctx

variable {t : G} {L : Subgroup G} {y : G} {X Y T : Subgroup G}

theorem isPGroup_T (c : M6E8Ctx t L y X Y T) : IsPGroup 2 ↥T :=
  c.hT.2.1

theorem y_mem_R (c : M6E8Ctx t L y X Y T) : y ∈ T ⊓ centralizer ({y} : Set G) :=
  Subgroup.mem_inf.mpr ⟨c.hyT, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem y_mem_centralizer_Y (c : M6E8Ctx t L y X Y T) : y ∈ centralizer (Y : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (c.hYc.1 ha)

theorem isPGroup_R (c : M6E8Ctx t L y X Y T) : IsPGroup 2 ↥(T ⊓ centralizer ({y} : Set G)) :=
  c.isPGroup_T.to_le inf_le_left

theorem R_comm (c : M6E8Ctx t L y X Y T) {a b : G} (ha : a ∈ T ⊓ centralizer ({y} : Set G))
    (hb : b ∈ T ⊓ centralizer ({y} : Set G)) : a * b = b * a := by
  haveI : IsMulCommutative ↥(T ⊓ centralizer ({y} : Set G)) := c.hab.1
  exact congrArg Subtype.val
    (mul_comm' (⟨a, ha⟩ : ↥(T ⊓ centralizer ({y} : Set G))) ⟨b, hb⟩)

theorem R_sq (c : M6E8Ctx t L y X Y T) {a : G} (ha : a ∈ T ⊓ centralizer ({y} : Set G)) :
    a ^ 2 = 1 :=
  c.hab.2 a ha

theorem cent_eq (c : M6E8Ctx t L y X Y T) : T ⊓ centralizer (Y : Set G) = zpowers y := by
  have hle : zpowers y ≤ T ⊓ centralizer (Y : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨c.hyT, c.y_mem_centralizer_Y⟩)
  exact (Subgroup.eq_of_le_of_card_ge hle
    (by rw [c.h2, Nat.card_zpowers, c.hy])).symm

theorem R_inf_cent_eq (c : M6E8Ctx t L y X Y T) :
    T ⊓ centralizer ({y} : Set G) ⊓ centralizer (Y : Set G) = zpowers y := by
  apply le_antisymm
  · calc T ⊓ centralizer ({y} : Set G) ⊓ centralizer (Y : Set G)
        ≤ T ⊓ centralizer (Y : Set G) := inf_le_inf inf_le_left le_rfl
      _ = zpowers y := c.cent_eq
  · exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨c.y_mem_R, c.y_mem_centralizer_Y⟩)

theorem relIndex_four (c : M6E8Ctx t L y X Y T) :
    (centralizer (Y : Set G)).relIndex (T ⊓ centralizer ({y} : Set G)) = 4 := by
  have h := sec64_card_eq (T ⊓ centralizer ({y} : Set G)) (centralizer (Y : Set G))
  rw [c.h8, c.R_inf_cent_eq, Nat.card_zpowers, c.hy] at h
  omega

theorem R_le_normalizer (h63 : Asc82Lemma63) (c : M6E8Ctx t L y X Y T) :
    T ⊓ centralizer ({y} : Set G) ≤ normalizer (Y : Set G) ⊓ centralizer (X : Set G) := by
  intro r hr
  exact ⟨sec64_mem_normalizer h63 c.setting c.hyp62 c.hy c.hYc c.hYF hr.2, c.hT.1 hr.1⟩

end M6E8Ctx

structure M6E8Datum (t : G) (L : Subgroup G) (y : G) (X Y T : Subgroup G) (r : G) : Prop
    extends M6E8Ctx t L y X Y T where
  mem_R : r ∈ T ⊓ centralizer ({y} : Set G)
  not_mem : r ∉ zpowers y
  card_gt : 8 < Nat.card ↥(T ⊓ centralizer ({r} : Set G))
  omega5 : IsOmega5 (layerCent Y r)
  quasi : IsQuasisimple ↥(layerCent Y r)
  xj : X ≤ layerCent Y r
  cent_le : T ⊓ centralizer ({y} : Set G) ⊓ centralizer (layerCent Y r : Set G) ≤
    zpowers y ⊔ zpowers r
  comp : IsComponentIn (layerCent Y r) (centralizer ({y, r} : Set G))

namespace M6E8Datum

variable {t : G} {L : Subgroup G} {y : G} {X Y T : Subgroup G} {r : G}

theorem orderOf_r (d : M6E8Datum t L y X Y T r) : orderOf r = 2 := by
  refine orderOf_eq_prime (d.toM6E8Ctx.R_sq d.mem_R) ?_
  intro h
  exact d.not_mem (h ▸ Subgroup.one_mem _)

theorem comm_yr (d : M6E8Datum t L y X Y T r) : y * r = r * y :=
  d.toM6E8Ctx.R_comm d.toM6E8Ctx.y_mem_R d.mem_R

theorem J_le_Y (d : M6E8Datum t L y X Y T r) : layerCent Y r ≤ Y := by
  unfold layerCent CFSG.inSubgroup
  exact (Subgroup.map_subtype_le _).trans inf_le_left

theorem J_le_centralizer_r (d : M6E8Datum t L y X Y T r) :
    layerCent Y r ≤ centralizer ({r} : Set G) := by
  unfold layerCent CFSG.inSubgroup
  exact (Subgroup.map_subtype_le _).trans inf_le_right

theorem r_mem_centralizer_J (d : M6E8Datum t L y X Y T r) :
    r ∈ centralizer (layerCent Y r : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (d.J_le_centralizer_r ha)

theorem y_mem_centralizer_J (d : M6E8Datum t L y X Y T r) :
    y ∈ centralizer (layerCent Y r : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (d.hYc.1 (d.J_le_Y ha))

end M6E8Datum

end CFSG.OddStandard.SmallF3.Omega
