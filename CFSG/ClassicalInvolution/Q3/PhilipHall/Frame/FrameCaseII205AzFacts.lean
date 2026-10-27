module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3SConf
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf6C205

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

section Az

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem a_comm_z (d : Std20Frame K K' J S R R' W V z t) {a : G} (hd : Frame205Data d a) :
    a * z = z * a :=
  d.s_comm_z hd.conf.hA.1.1

theorem az_mul_self (d : Std20Frame K K' J S R R' W V z t) {a : G} (hd : Frame205Data d a) :
    (a * z) * (a * z) = 1 := by
  have hcomm : a * z = z * a := a_comm_z d hd
  have ha2 := hd.conf.ha2
  have hz2 := d.viol.hzK.sq
  calc a * z * (a * z) = a * (z * a) * z := by group
    _ = a * (a * z) * z := by rw [← hcomm]
    _ = (a * a) * (z * z) := by group
    _ = 1 := by rw [ha2, hz2, one_mul]

theorem a_ne_z (d : Std20Frame K K' J S R R' W V z t) {a : G} (hd : Frame205Data d a) :
    z ≠ a := fun e => d.s_a_not_mem_closure hd.conf.c4 hd.conf.hA hd.conf.ha1 (by
  rw [← e]
  exact Subgroup.subset_closure (by simp))

theorem az_ne_one (d : Std20Frame K K' J S R R' W V z t) {a : G} (hd : Frame205Data d a) :
    a * z ≠ 1 := fun e => a_ne_z d hd (by
  have h1 : a = z⁻¹ := eq_inv_of_mul_eq_one_left e
  rw [h1]
  exact (inv_eq_of_mul_eq_one_right d.viol.hzK.sq).symm)

theorem z_ne_az (d : Std20Frame K K' J S R R' W V z t) {a : G} (hd : Frame205Data d a) :
    z ≠ a * z := fun e => hd.conf.ha1 (by
  have : a * z = 1 * z := by rw [← e, one_mul]
  exact mul_right_cancel this)

theorem z_mem_centralizer_az (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (hd : Frame205Data d a) : z ∈ Subgroup.centralizer ({a * z} : Set G) := by
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc z * (a * z) = (z * a) * z := by group
    _ = (a * z) * z := by rw [a_comm_z d hd]

theorem t_mem_centralizer_az (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (hd : Frame205Data d a) : t ∈ Subgroup.centralizer ({a * z} : Set G) := by
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  have hat : a * t = t * a := d.s_comm_t hd.conf.hA
  have hzt : z * t = t * z := d.late_zt_comm
  calc t * (a * z) = (t * a) * z := by group
    _ = (a * t) * z := by rw [hat]
    _ = a * (t * z) := by group
    _ = a * (z * t) := by rw [hzt]
    _ = (a * z) * t := by group

theorem az_mem_B (d : Std20Frame K K' J S R R' W V z t) {a : G} (hd : Frame205Data d a) :
    a * z ∈ Subgroup.closure ({z, t, a} : Set G) :=
  (Subgroup.closure ({z, t, a} : Set G)).mul_mem (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))

theorem az_mem_trivialOnQuot_K (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (hd : Frame205Data d a) : a * z ∈ Balance.Bootstrap.trivialOnQuot K := by
  have haN : a ∈ Subgroup.normalizer (K : Set G) := d.cent_le_normalizer hd.conf.hA.1
  have hzN : z ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer (d.viol.hzK.mem)
  refine ⟨(Subgroup.normalizer (K : Set G)).mul_mem haN hzN, fun x hx => ?_⟩
  have hzx : z * x = x * z := d.viol.hzK.commute_of_mem hx
  have e : ⁅a * z, x⁆ = ⁅a, x⁆ := by
    simp only [commutatorElement_def]
    calc a * z * x * (a * z)⁻¹ * x⁻¹ = a * (z * x) * z⁻¹ * a⁻¹ * x⁻¹ := by group
      _ = a * (x * z) * z⁻¹ * a⁻¹ * x⁻¹ := by rw [hzx]
      _ = a * x * a⁻¹ * x⁻¹ := by group
  rw [e]
  exact d.s_comm_K hd.conf.hA hx

theorem az_mem_trivialOnQuot_K' (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (hd : Frame205Data d a) : a * z ∈ Balance.Bootstrap.trivialOnQuot K' := by
  have haN : a ∈ Subgroup.normalizer (K' : Set G) := d.cent_le_normalizer' hd.conf.hA.1
  have hzN : z ∈ Subgroup.normalizer (K' : Set G) :=
    Subgroup.le_normalizer (d.late_hzK'.mem)
  refine ⟨(Subgroup.normalizer (K' : Set G)).mul_mem haN hzN, fun x hx => ?_⟩
  have hzx : z * x = x * z := d.late_hzK'.commute_of_mem hx
  have e : ⁅a * z, x⁆ = ⁅a, x⁆ := by
    simp only [commutatorElement_def]
    calc a * z * x * (a * z)⁻¹ * x⁻¹ = a * (z * x) * z⁻¹ * a⁻¹ * x⁻¹ := by group
      _ = a * (x * z) * z⁻¹ * a⁻¹ * x⁻¹ := by rw [hzx]
      _ = a * x * a⁻¹ * x⁻¹ := by group
  rw [e]
  exact d.s_comm_K' hd.conf.hA hx

theorem R_le_centralizer_a (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (hd : Frame205Data d a) : R ≤ Subgroup.centralizer ({a} : Set G) :=
  (le_sup_of_le_left (le_sup_right : R ≤ _ ⊔ R) :
      R ≤ frameH20 (CoreAssembly.conjClass K) a R R').trans
    (frameH20_le_centralizer d hd.conf.hA.1)

theorem R'_le_centralizer_a (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (hd : Frame205Data d a) : R' ≤ Subgroup.centralizer ({a} : Set G) :=
  (le_sup_right : R' ≤ frameH20 (CoreAssembly.conjClass K) a R R').trans
    (frameH20_le_centralizer d hd.conf.hA.1)

theorem le_centralizer_az_of_le {P : Subgroup G} (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (hP : P ≤ (S : Subgroup G)) (hPa : P ≤ Subgroup.centralizer ({a} : Set G)) :
    P ≤ Subgroup.centralizer ({a * z} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp (hPa hx)
  have h2 : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (d.hSz (hP hx))
  calc x * (a * z) = (x * a) * z := by group
    _ = (a * x) * z := by rw [h1]
    _ = a * (x * z) := by group
    _ = a * (z * x) := by rw [h2]
    _ = (a * z) * x := by group

theorem R_le_centralizer_az (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (hd : Frame205Data d a) : R ≤ Subgroup.centralizer ({a * z} : Set G) :=
  le_centralizer_az_of_le d d.hRS (R_le_centralizer_a d hd)

theorem R'_le_centralizer_az (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (hd : Frame205Data d a) : R' ≤ Subgroup.centralizer ({a * z} : Set G) :=
  le_centralizer_az_of_le d d.hR'S (R'_le_centralizer_a d hd)

theorem t_mem_sup_R_R' (d : Std20Frame K K' J S R R' W V z t) : t ∈ R ⊔ R' := by
  rw [← d.late_S_inf_sup]
  exact ⟨d.t_mem_S, d.htKK⟩

theorem card_centralizer_az_lt (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (hd : Frame205Data d a) :
    Nat.card ↥(Subgroup.centralizer ({a * z} : Set G)) < Nat.card G := by
  have hCtop : Subgroup.centralizer ({a * z} : Set G) ≠ ⊤ := by
    intro htop
    have hac : a * z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
    rw [FrameCore.center d.nonabelian, Subgroup.mem_bot] at hac
    exact az_ne_one d hd hac
  exact lt_of_le_of_ne (Subgroup.card_le_card_group _)
    (fun h => hCtop ((Subgroup.card_eq_iff_eq_top _).mp h))

end Az

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
