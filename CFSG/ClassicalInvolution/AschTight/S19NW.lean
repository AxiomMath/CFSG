module

public import CFSG.ClassicalInvolution.AschTight.S19CData
public import CFSG.ClassicalInvolution.AschTight.S19CMir
public import CFSG.ClassicalInvolution.AschTight.S19LU

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

section Arith

variable {G : Type} [Group G]

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

theorem orderOf_eq_four {w z : G} (hw : w * w = z) (hz1 : z ≠ 1) (hzz : z * z = 1) :
    orderOf w = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : w ^ 4 = 1 := by
    calc w ^ 4 = (w * w) * (w * w) := by
          rw [pow_succ, pow_succ, pow_succ, pow_one]
          group
      _ = 1 := by rw [hw, hzz]
  have h2 : w ^ 2 ≠ 1 := by
    rw [sq, hw]
    exact hz1
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) (by simpa using h4)
  simpa using this

end Arith
variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem exists_order_four [IsSimpleGroup G] (hdT : Sec19DataT p f K z S W L t V) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1)
    (haH : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ∃ w ∈ (S : Subgroup G) ⊓ K, w * a = a * w ∧ w * w = z ∧ orderOf w = 4 := by
  have hd := hdT.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  obtain ⟨r, hrR, hrt⟩ := S1911.exists_conj_eq_mul hdT
  have hcomm := S1911.comm_of_mem hd
  have hrU : r ∉ K ⊓ W := by
    intro hr
    have h1 : r * t * r⁻¹ = t := by rw [hcomm r hr.2 t (S1911.mem_W hdT), mul_inv_cancel_right]
    rw [h1] at hrt
    exact hI.ne_one (by simpa using hrt)
  obtain ⟨u, K', hu, hdd⟩ := S19C.exists_dData_K_of hdT hrR hrU
  have haN : a ∈ Subgroup.normalizer (K : Set G) := (S1916.sd_normalizer_eq hd).ge (hd.hSz haS)
  have haW : a ∈ Subgroup.normalizer (W : Set G) := S19B.le_normalizer_W hdT haS
  have haU : ∀ x ∈ Subgroup.zpowers u, a * x * a⁻¹ ∈ Subgroup.zpowers u := by
    intro x hx
    rw [hu] at hx ⊢
    exact ⟨(Subgroup.mem_normalizer_iff.mp haN x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp haW x).mp hx.2⟩
  have haR : a * r * a⁻¹ ∈ (S : Subgroup G) ⊓ K :=
    ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem haS hrR.1) ((S : Subgroup G).inv_mem haS),
      (Subgroup.mem_normalizer_iff.mp haN r).mp hrR.2⟩
  have hnc : a * u * a⁻¹ ≠ u := by
    intro h
    apply S19L.not_forall_comm_of_not_mem hdT haS haH
    intro x hx
    rw [← hu] at hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : a * u ^ k * a⁻¹ = u ^ k := by rw [← conj_zpow, h]
    calc a * u ^ k = a * u ^ k * a⁻¹ * a := by group
      _ = u ^ k * a := by rw [h1]
  have hni : a * u * a⁻¹ ≠ u⁻¹ := by
    intro h
    apply S1916.not_forall_inv_of_not_mem hdT haS haH
    intro x hx
    rw [← hu] at hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, h, inv_zpow]
  obtain ⟨N, hN⟩ := hdd.orderOf_eq
  obtain ⟨h8, hor⟩ := S19L.conj_eq_z_mul_or hN hdd.four_le (haU u (Subgroup.mem_zpowers u)) ha2
    hnc hni
  rw [hdd.z_eq] at hor
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by
    by_contra h
    have : 2 ^ N ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega⟩
  have hu8 : orderOf u = 8 * 2 ^ M := by
    rw [hN, pow_add]
    ring
  have hz : z = u ^ (4 * 2 ^ M) := by
    rw [← hdd.z_eq, hu8]
    congr 1
    omega
  have huSK : u ∈ (S : Subgroup G) ⊓ K := by
    have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
    exact ⟨hd.hWS huKW.2, huKW.1⟩
  rcases hor with h | h
  ·
    refine ⟨u ^ (2 * 2 ^ M), Subgroup.pow_mem _ huSK _, ?_, ?_, ?_⟩
    · have h1 := conj_fixed_of_eq_mul hz hI.sq h
      calc u ^ (2 * 2 ^ M) * a = a * u ^ (2 * 2 ^ M) * a⁻¹ * a := by rw [h1]
        _ = a * u ^ (2 * 2 ^ M) := by group
    · rw [← pow_add, hz]
      congr 1
      ring
    · refine orderOf_eq_four (z := z) ?_ hI.ne_one hI.sq
      rw [← pow_add, hz]
      congr 1
      ring
  ·
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (S19C.mul_inv_mem_of_dData hdd ha2 haR haU)
    have har : a * r * a⁻¹ = u ^ i * r := by rw [hi]; group
    obtain ⟨j, hj⟩ := exists_conj_fixed hu8 hz h har ha2
    have hww : u ^ j * r * (u ^ j * r) = z := by
      have hru : r * u ^ j * r⁻¹ = (u ^ j)⁻¹ := by
        rw [← conj_zpow, hdd.conj_u, inv_zpow]
      calc u ^ j * r * (u ^ j * r) = u ^ j * (r * u ^ j * r⁻¹) * (r * r) := by group
        _ = z := by rw [hru, hdd.sq_r, mul_inv_cancel, one_mul]
    refine ⟨u ^ j * r, Subgroup.mul_mem _ (Subgroup.zpow_mem _ huSK _) hrR, ?_, hww,
      orderOf_eq_four hww hI.ne_one hI.sq⟩
    calc u ^ j * r * a = a * (u ^ j * r) * a⁻¹ * a := by rw [hj]
      _ = a * (u ^ j * r) := by group

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19N
