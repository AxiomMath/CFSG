module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.PMData
public import CFSG.CGT.PushingUpLit.SolKNA.R4.QuatAlg

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Arith

variable {G : Type*} [Group G]

theorem conj_fixed_of_eq_mul {u a z : G} {M : ℕ} (hz : z = u ^ (4 * 2 ^ M)) (hzz : z * z = 1)
    (hau : a * u * a⁻¹ = z * u) : a * u ^ (2 * 2 ^ M) * a⁻¹ = u ^ (2 * 2 ^ M) := by
  have hzu : Commute z u := by
    rw [hz]
    exact (Commute.refl u).pow_left _
  rw [← conj_pow, hau, hzu.mul_pow]
  have hz2 : z ^ (2 * 2 ^ M) = 1 := by
    rw [pow_mul, sq, hzz, one_pow]
  rw [hz2, one_mul]

theorem exists_conj_fixed {u r a z : G} {M : ℕ} (hu : orderOf u = 8 * 2 ^ M)
    (hz : z = u ^ (4 * 2 ^ M)) (hau : a * u * a⁻¹ = z * u⁻¹) {i : ℤ}
    (har : a * r * a⁻¹ = u ^ i * r) (ha2 : a * a = 1) :
    ∃ j : ℤ, a * (u ^ j * r) * a⁻¹ = u ^ j * r := by
  set P : ℤ := 2 ^ M with hP
  have hzu : z * u⁻¹ = u ^ (4 * P - 1) := by
    rw [hz, zpow_sub, zpow_one, hP, ← zpow_natCast]
    push_cast
    rfl
  have hconj : ∀ j : ℤ, a * u ^ j * a⁻¹ = u ^ ((4 * P - 1) * j) := fun j => by
    rw [← conj_zpow, hau, hzu, ← zpow_mul]
  have hu1 : ∀ e : ℤ, u ^ e = 1 ↔ (8 * P) ∣ e := fun e => by
    rw [← orderOf_dvd_iff_zpow_eq_one, hu, hP]
    push_cast
    rfl
  have hii : u ^ ((4 * P - 1) * i + i) = 1 := by
    have h1 : a * (a * r * a⁻¹) * a⁻¹ = r := by
      calc a * (a * r * a⁻¹) * a⁻¹ = (a * a) * r * (a * a)⁻¹ := by group
        _ = r := by rw [ha2]; group
    rw [har, show a * (u ^ i * r) * a⁻¹ = (a * u ^ i * a⁻¹) * (a * r * a⁻¹) by group, hconj, har,
      ← mul_assoc, ← zpow_add] at h1
    exact mul_right_cancel (h1.trans (one_mul r).symm)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, i = 2 * m := by
    obtain ⟨c, hc⟩ := (hu1 _).mp hii
    refine ⟨c, ?_⟩
    have hP0 : (4 * P) ≠ 0 := by positivity
    have : (4 * P) * i = (4 * P) * (2 * c) := by linear_combination hc
    exact mul_left_cancel₀ hP0 this
  refine ⟨m * (2 * P + 1), ?_⟩
  rw [show a * (u ^ (m * (2 * P + 1)) * r) * a⁻¹ =
      (a * u ^ (m * (2 * P + 1)) * a⁻¹) * (a * r * a⁻¹) by group, hconj, har, ← mul_assoc,
    ← zpow_add]
  congr 1
  rw [← mul_inv_eq_one, ← zpow_sub, hu1]
  exact ⟨P * m, by rw [hm]; ring⟩

theorem exists_presentation {r : ℕ} (hr : 4 ≤ r) {Q U : Subgroup G}
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hUQ : U ≤ Q) (hUc : IsCyclic ↥U)
    (hUi : U.relIndex Q = 2) {z : G} (hzQ : z ∈ Q) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ u r₀ : G, u ∈ Q ∧ r₀ ∈ Q ∧ Subgroup.zpowers u = U ∧ orderOf u = 2 ^ (r - 1) ∧
      u ^ 2 ^ (r - 2) = z ∧ r₀ ∉ U ∧ r₀ * u * r₀⁻¹ = u⁻¹ ∧ r₀ * r₀ = z ∧
      ∀ q ∈ Q, q ∈ U ∨ ∃ i : ℤ, q = u ^ i * r₀ := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  have hUeq : U = QSub.xc e := QSub.eq_xc_of_cyclic_index_two e hr hUQ hUc hUi
  have hzA : z = ((e.symm (QuaternionGroup.a (2 ^ (r - 2))) : ↥Q) : G) :=
    (QSub.eq_of_mul_self_eq_one e hzQ hz2).resolve_left hz1
  have hu : ((e.symm (QuaternionGroup.a 1) : ↥Q) : G) ∈ Q := (e.symm _).2
  have hr₀ : ((e.symm (QuaternionGroup.xa 0) : ↥Q) : G) ∈ Q := (e.symm _).2
  have hzu : Subgroup.zpowers ((e.symm (QuaternionGroup.a 1) : ↥Q) : G) = U := by
    rw [hUeq, QSub.xc, MonoidHom.map_zpowers]
    rfl
  have hord : orderOf ((e.symm (QuaternionGroup.a 1) : ↥Q) : G) = 2 ^ (r - 1) := by
    rw [QSub.Alg.orderOf_coe_symm e, QuaternionGroup.orderOf_a_one,
      show r - 1 = (r - 2) + 1 by omega]
    ring
  have hpow : ((e.symm (QuaternionGroup.a 1) : ↥Q) : G) ^ 2 ^ (r - 2) = z := by
    rw [hzA, ← Subgroup.coe_pow, ← map_pow e.symm, QSub.Alg.a_pow, mul_one, QSub.Alg.nn_eq]
  have hr₀U : ((e.symm (QuaternionGroup.xa 0) : ↥Q) : G) ∉ U := by
    rw [hUeq, QSub.mem_xc_iff e]
    rintro ⟨i, hi⟩
    have h := (QSub.Alg.coe_symm_inj e).mp hi
    cases h
  have hconj : ((e.symm (QuaternionGroup.xa 0) : ↥Q) : G) *
      ((e.symm (QuaternionGroup.a 1) : ↥Q) : G) *
      ((e.symm (QuaternionGroup.xa 0) : ↥Q) : G)⁻¹ =
      ((e.symm (QuaternionGroup.a 1) : ↥Q) : G)⁻¹ := by
    have h : (e.symm (QuaternionGroup.xa 0) : ↥Q) * (e.symm (QuaternionGroup.a 1) : ↥Q) *
        (e.symm (QuaternionGroup.xa 0) : ↥Q)⁻¹ = (e.symm (QuaternionGroup.a 1) : ↥Q)⁻¹ := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [QuaternionGroup.xa_mul_a, QSub.Alg.inv_xa, QuaternionGroup.xa_mul_xa, QSub.Alg.inv_a]
      congr 1
      linear_combination QSub.Alg.n_add_n (n := 2 ^ (r - 2))
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val h
  have hxx : (QuaternionGroup.xa 0 * QuaternionGroup.xa 0 : QuaternionGroup (2 ^ (r - 2))) =
      QuaternionGroup.a (2 ^ (r - 2)) := by
    rw [QuaternionGroup.xa_mul_xa, add_zero, sub_zero, QSub.Alg.nn_eq]
  have hrr : ((e.symm (QuaternionGroup.xa 0) : ↥Q) : G) *
      ((e.symm (QuaternionGroup.xa 0) : ↥Q) : G) = z := by
    rw [QSub.Alg.coe_symm_mul e, hxx, hzA]
  have hcos : ∀ q ∈ Q, q ∈ U ∨ ∃ i : ℤ,
      q = ((e.symm (QuaternionGroup.a 1) : ↥Q) : G) ^ i *
        ((e.symm (QuaternionGroup.xa 0) : ↥Q) : G) := by
    intro q hq
    obtain ⟨y, rfl⟩ := QSub.Alg.exists_coe_symm e hq
    rcases y with i | j
    · left
      rw [hUeq]
      exact (QSub.mem_xc_iff e).mpr ⟨i, rfl⟩
    · right
      refine ⟨((-j).val : ℤ), ?_⟩
      have h1 : (QuaternionGroup.xa j : QuaternionGroup (2 ^ (r - 2))) =
          QuaternionGroup.a (-j) * QuaternionGroup.xa 0 := by
        rw [QuaternionGroup.a_mul_xa, zero_sub, neg_neg]
      have h2 : (e.symm (QuaternionGroup.xa j) : ↥Q) =
          (e.symm (QuaternionGroup.a 1) : ↥Q) ^ (-j).val *
            (e.symm (QuaternionGroup.xa 0) : ↥Q) := by
        rw [h1, map_mul, QSub.Alg.a_eq_pow (-j), map_pow]
      rw [zpow_natCast, h2, Subgroup.coe_mul, Subgroup.coe_pow]
  exact ⟨((e.symm (QuaternionGroup.a 1) : ↥Q) : G), ((e.symm (QuaternionGroup.xa 0) : ↥Q) : G),
    hu, hr₀, hzu, hord, hpow, hr₀U, hconj, hrr, hcos⟩

theorem exists_comm_sq_eq {r : ℕ} (hr : 4 ≤ r) {Q U : Subgroup G}
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hUQ : U ≤ Q) (hUc : IsCyclic ↥U)
    (hUi : U.relIndex Q = 2) {z : G} (hzQ : z ∈ Q) (hz2 : z * z = 1) (hz1 : z ≠ 1) {x : G}
    (hx : x ∈ Subgroup.normalizer (Q : Set G)) (hx2 : x * x = 1) (hxU : ¬ ActsPM U x) :
    ∃ w ∈ Q, w * x = x * w ∧ w * w = z := by
  obtain ⟨u, r₀, huQ, hr₀Q, hzu, hord, hpow, hr₀U, hr₀u, hr₀r₀, hcos⟩ :=
    exists_presentation hr e hUQ hUc hUi hzQ hz2 hz1
  have hxN : x ∈ Subgroup.normalizer (U : Set G) :=
    le_normalizer_of_isCyclic_of_relIndex_eq_two hr e hUQ hUc hUi hx
  have huU : u ∈ U := by
    rw [← hzu]
    exact Subgroup.mem_zpowers u
  have hxu : x * u * x⁻¹ ∈ Subgroup.zpowers u := by
    rw [hzu]
    exact (Subgroup.mem_normalizer_iff.mp hxN u).mp huU
  have hxU' : ¬ ActsPM (Subgroup.zpowers u) x := by
    rw [hzu]
    exact hxU
  have hu8 : orderOf u = 8 * 2 ^ (r - 4) := by
    rw [hord, show r - 1 = (r - 4) + 3 by omega, pow_add]
    ring
  have e2 : (2 : ℕ) ^ (r - 2) = 4 * 2 ^ (r - 4) := by
    rw [show r - 2 = (r - 4) + 2 by omega, pow_add]
    ring
  have hz4 : z = u ^ (4 * 2 ^ (r - 4)) := by
    rw [← hpow, e2]
  rcases conj_eq_mul_pow_or (show 3 ≤ r - 1 by omega) hord hxu hx2 hxU' with h | h
  ·
    rw [show r - 1 - 1 = r - 2 by omega, hpow] at h
    have hc := conj_fixed_of_eq_mul hz4 hz2 h
    refine ⟨u ^ (2 * 2 ^ (r - 4)), Q.pow_mem huQ _, (mul_inv_eq_iff_eq_mul.mp hc).symm, ?_⟩
    rw [← pow_add, hz4]
    congr 1
    ring
  ·
    rw [show r - 1 - 1 = r - 2 by omega, hpow] at h
    have hrQ : x * r₀ * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hx r₀).mp hr₀Q
    have hrU : x * r₀ * x⁻¹ ∉ U := fun hmem =>
      hr₀U ((Subgroup.mem_normalizer_iff.mp hxN r₀).mpr hmem)
    obtain ⟨i, hi⟩ : ∃ i : ℤ, x * r₀ * x⁻¹ = u ^ i * r₀ := (hcos _ hrQ).resolve_left hrU
    obtain ⟨j, hj⟩ := exists_conj_fixed hu8 hz4 h hi hx2
    refine ⟨u ^ j * r₀, Q.mul_mem (Q.zpow_mem huQ j) hr₀Q,
      (mul_inv_eq_iff_eq_mul.mp hj).symm, ?_⟩
    have hru : r₀ * u ^ j * r₀⁻¹ = (u ^ j)⁻¹ := by
      rw [← conj_zpow, hr₀u, inv_zpow]
    calc u ^ j * r₀ * (u ^ j * r₀) = u ^ j * (r₀ * u ^ j * r₀⁻¹) * (r₀ * r₀) := by group
      _ = z := by rw [hru, mul_inv_cancel, one_mul, hr₀r₀]

end Arith

variable {r : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem exists_order_four (hr : 4 ≤ r) {x : G} (hxS : x ∈ (S : Subgroup G)) (hx2 : x * x = 1)
    (hx : x ∉ pmSubgroup (K ⊓ W)) :
    ∃ w ∈ (S : Subgroup G) ⊓ K, w * x = x * w ∧ w * w = z ∧ orderOf w = 4 := by
  obtain ⟨e⟩ := hd.exists_quat_inf
  have hI := hd.tight.isUniqueInvolution
  obtain ⟨w, hwQ, hwx, hww⟩ := exists_comm_sq_eq hr e hd.inf_le_inf_core hd.isCyclic_inf
    hd.relIndex_inf hd.toTightSylowDataR.mem_inf hI.sq hI.ne_one
    (hd.toTightSylowDataR.le_normalizer_inf hxS) hx2 hx
  exact ⟨w, hwQ, hwx, hww, QSub.Alg.orderOf_eq_four_of_mul_self hww hI.sq hI.ne_one⟩

end TightSylowDataTR

end CFSG.CGT.PushingUpLit.SolKNA.R4
