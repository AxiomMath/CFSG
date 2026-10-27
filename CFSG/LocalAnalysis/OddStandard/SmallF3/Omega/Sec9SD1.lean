module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Early
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L66In

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t z g : G} {L S B : Subgroup G}

theorem sec9d_comm_t (h : Sec8Base G t L S z g B) {x : G} (hx : x ∈ L) : x * t = t * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (h.toSec3SettingLB.component.le hx)

theorem sec9d_t_mem_cent (h : Sec8Base G t L S z g B) : t ∈ centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact sec9d_comm_t h hx

theorem sec9d_isOm6M (h : Sec8Base G t L S z g B) : IsOm6M L :=
  ⟨h.toSec3SettingLB.component.isQuasisimple, h.omega6m⟩

theorem sec9d_t_sq (h : Sec8Base G t L S z g B) : t * t = 1 := by
  rw [← pow_two, ← h.toSec3SettingLB.involution, pow_orderOf_eq_one]

theorem sec9d_z_sq (h : Sec8Base G t L S z g B) : z * z = 1 := by
  rw [← pow_two, ← h.pocket.1, pow_orderOf_eq_one]

theorem sec9d_t_not_mem (h : Sec8Base G t L S z g B) : t ∉ L := by
  intro htL
  have hodd : Odd (orderOf t) :=
    sec66_odd_of_mem_inf (sec9d_isOm6M h) ⟨htL, sec9d_t_mem_cent h⟩
  rw [h.toSec3SettingLB.involution] at hodd
  obtain ⟨k, hk⟩ := hodd
  omega

theorem sec9d_B_comm (h : Sec8Base G t L S z g B) {a b : G} (ha : a ∈ B) (hb : b ∈ B) :
    a * b = b * a :=
  CFSG.Open.IsElemAbelian.comm h.B_e16.1 ha hb

theorem sec9d_B_sq (h : Sec8Base G t L S z g B) {b : G} (hb : b ∈ B) : b * b = 1 :=
  CFSG.Open.IsElemAbelian.mul_self_eq_one h.B_e16.1 hb

theorem sec9d_t_B (h : Sec8Base G t L S z g B) {b : G} (hb : b ∈ B) : t * b = b * t :=
  (sec9d_comm_t h (h.B_le hb).1).symm

theorem sec9d_isOm6M_conj (h : Sec8Base G t L S z g B) : IsOm6M (CFSG.conjugate L g) :=
  sec68_isOm6M_conjugate (sec9d_isOm6M h) g

theorem sec9d_setting_conj (h : Sec8Base G t L S z g B) :
    Sec3SettingLB G (g⁻¹ * t * g) (CFSG.conjugate L g) :=
  h.toSec3SettingLB.conjugate g

theorem sec9d_tg_order (h : Sec8Base G t L S z g B) : orderOf (g⁻¹ * t * g) = 2 := by
  rw [orderOf_conjugate_eq t g, h.toSec3SettingLB.involution]

theorem sec9d_tg_mem_cent (h : Sec8Base G t L S z g B) :
    g⁻¹ * t * g ∈ centralizer (CFSG.conjugate L g : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp ((sec9d_setting_conj h).component.le hx)

theorem sec9d_B_comm_tg (hB8 : Asc82Sec8B) (h : Sec8Base G t L S z g B) {b : G} (hb : b ∈ B) :
    b * (g⁻¹ * t * g) = (g⁻¹ * t * g) * b := by
  have hzB : z ∈ B := (hB8 G t L S z g B h).1
  have hbt : b * t = t * b := (sec9d_t_B h hb).symm
  have hbz : b * z = z * b := sec9d_B_comm h hb hzB
  rw [h.tz]
  calc b * (t * z) = (b * t) * z := by group
    _ = (t * b) * z := by rw [hbt]
    _ = t * (b * z) := by group
    _ = t * (z * b) := by rw [hbz]
    _ = (t * z) * b := by group

theorem sec9d_tg_not_mem_B (hB8 : Asc82Sec8B) (h : Sec8Base G t L S z g B) :
    g⁻¹ * t * g ∉ B := by
  intro htgB
  have hzB : z ∈ B := (hB8 G t L S z g B h).1
  have htzB : t * z ∈ B := by
    rw [← h.tz]
    exact htgB
  have htB : t ∈ B := by
    have ht : t = (t * z) * z⁻¹ := by group
    rw [ht]
    exact B.mul_mem htzB (B.inv_mem hzB)
  exact sec9d_t_not_mem h ((h.B_le htB).1)

theorem sec9d_B_le_normalizer (h36 : Asc82Lemma36) (hB8 : Asc82Sec8B)
    (h : Sec8Base G t L S z g B) : B ≤ normalizer (CFSG.conjugate L g : Set G) := by
  intro b hb
  apply mem_normalizer_of_conjugate_eq
  exact conjugate_eq_self_of_lemma36 h36 (sec9d_setting_conj h) b
    (Subgroup.mem_centralizer_singleton_iff.mpr (sec9d_B_comm_tg hB8 h hb))

end CFSG.OddStandard.SmallF3.Omega
