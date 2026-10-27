module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Sp4Inn

public section

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists CFSG
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.Stage2.OddAut
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4

variable {K : Type} [Field K]

theorem commute_of_proj_eq_one {s : StatedSp 2 K} (h : proj 2 K s = 1) (y : StatedSp 2 K) :
    Commute s y := by
  have h' : (QuotientGroup.mk s : StatedSp 2 K ⧸ spScalars 2 K) = 1 := h
  have hs : s ∈ spScalars 2 K := (QuotientGroup.eq_one_iff s).mp h'
  rw [spScalars, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hs
  obtain ⟨c, hc⟩ := hs
  have hz : (s : GL (Fin 2 ⊕ Fin 2) K) ∈ Subgroup.center (GL (Fin 2 ⊕ Fin 2) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, hc⟩
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp hz (y : GL (Fin 2 ⊕ Fin 2) K)).symm

theorem eq_of_proj_eq_odd {n : ℕ} (hn : Odd n) {x y : StatedSp 2 K} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (h : proj 2 K x = proj 2 K y) : x = y := by
  have hs : proj 2 K (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have hsq := sq_eq_one_of_proj_eq_one hs
  have hcomm : Commute x (x⁻¹ * y) := (commute_of_proj_eq_one hs x).symm
  have hy' : y = x * (x⁻¹ * y) := by group
  have hpow : (x⁻¹ * y) ^ n = 1 := by
    have h1 : (x * (x⁻¹ * y)) ^ n = x ^ n * (x⁻¹ * y) ^ n := hcomm.mul_pow n
    rw [← hy', hy, hx, one_mul] at h1
    exact h1.symm
  obtain ⟨m, rfl⟩ := hn
  have h2 : x⁻¹ * y = 1 := by
    calc x⁻¹ * y = (x⁻¹ * y) ^ (2 * m + 1) := by rw [pow_succ, pow_mul, hsq, one_pow, one_mul]
      _ = 1 := hpow
  exact inv_mul_eq_one.mp h2

theorem commute_of_lifts {n : ℕ} (hn : Odd n) {x y : StatedSp 2 K} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (h : Commute (proj 2 K x) (proj 2 K y)) : Commute x y := by
  set s := x * y * x⁻¹ * y⁻¹ with hs
  have hs1 : proj 2 K s = 1 := by
    have h1 : ⁅proj 2 K x, proj 2 K y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h.eq
    rw [commutatorElement_def] at h1
    simpa [hs, map_mul, map_inv] using h1
  have hsq := sq_eq_one_of_proj_eq_one hs1
  have hcs : Commute s y := commute_of_proj_eq_one hs1 y
  have hxy : x * y * x⁻¹ = s * y := by rw [hs]; group
  have hpow : s ^ n = 1 := by
    have h1 : (x * y * x⁻¹) ^ n = x * y ^ n * x⁻¹ := conj_pow
    rw [hxy, hcs.mul_pow, hy, mul_one] at h1
    rw [h1]
    group
  obtain ⟨m, rfl⟩ := hn
  have h2 : s = 1 := by
    calc s = s ^ (2 * m + 1) := by rw [pow_succ, pow_mul, hsq, one_pow, one_mul]
      _ = 1 := hpow
  have h3 : x * y * x⁻¹ = y := by rw [hxy, h2, one_mul]
  show x * y = y * x
  calc x * y = (x * y * x⁻¹) * x := by group
    _ = y * x := by rw [h3]


section Lift

variable {r : ℕ} {V0 : Subgroup (StatedProj (StatedSp 2 K))} [IsElementaryAbelian r ↥V0]

theorem exists_lift_elem (hr : Odd r) (g : ↥V0) :
    ∃ u : StatedSp 2 K, proj 2 K u = (g : StatedProj (StatedSp 2 K)) ∧ u ^ r = 1 :=
  exists_lift_pow_eq_one hr (elemPow_eq_one_of_isElementaryAbelian (p := r) (A := V0) _ g.2)

@[expose] noncomputable def liftHom (hr : Odd r) : ↥V0 →* StatedSp 2 K where
  toFun g := Classical.choose (exists_lift_elem hr g)
  map_one' := by
    apply eq_of_proj_eq_odd hr (Classical.choose_spec (exists_lift_elem hr (1 : ↥V0))).2 (one_pow r)
    rw [(Classical.choose_spec (exists_lift_elem hr (1 : ↥V0))).1, map_one]
    rfl
  map_mul' g h := by
    set x := Classical.choose (exists_lift_elem hr g) with hx
    set y := Classical.choose (exists_lift_elem hr h) with hy
    set z := Classical.choose (exists_lift_elem hr (g * h)) with hz
    have hxs := Classical.choose_spec (exists_lift_elem hr g)
    have hys := Classical.choose_spec (exists_lift_elem hr h)
    have hzs := Classical.choose_spec (exists_lift_elem hr (g * h))
    have hcomm : Commute x y := by
      apply commute_of_lifts hr hxs.2 hys.2
      rw [hxs.1, hys.1]
      exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥V0)).comm g h)
    apply eq_of_proj_eq_odd hr hzs.2
    · rw [hcomm.mul_pow, hxs.2, hys.2, one_mul]
    · rw [hzs.1, map_mul, hxs.1, hys.1]
      rfl

theorem proj_liftHom (hr : Odd r) (g : ↥V0) :
    proj 2 K (liftHom hr g) = (g : StatedProj (StatedSp 2 K)) :=
  (Classical.choose_spec (exists_lift_elem hr g)).1

theorem liftHom_pow (hr : Odd r) (g : ↥V0) : liftHom hr g ^ r = 1 :=
  (Classical.choose_spec (exists_lift_elem hr g)).2

theorem liftHom_injective (hr : Odd r) : Function.Injective (liftHom hr (V0 := V0)) := by
  intro g h hgh
  apply Subtype.ext
  rw [← proj_liftHom hr g, ← proj_liftHom hr h, hgh]

end Lift

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Sp4
