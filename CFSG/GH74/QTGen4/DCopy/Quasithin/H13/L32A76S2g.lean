module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32A76S2g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2b

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Q511 CFSG.Quasithin.H13.L32A.M76 CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H Y : Subgroup G} {γ γ' : F8.Geom T L H}
  {g : ↥((L ⊔ T) ⊔ H)}

namespace Ctx_F4
open CFSG.Quasithin.H13.L32A.S2.Ctx_F4

@[expose] noncomputable def Pe_F4 (C : Ctx_F4 G T L V H Y)
    (e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) : Subgroup G :=
  ((Subgroup.zpowers e).comap (FixR.rho C.h91_F4)).map H.subtype

variable (C : Ctx_F4 G T L V H Y)
include C

theorem mem_Pe_F4 {e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))} {x : G} :
    x ∈ C.Pe_F4 e ↔ ∃ hx : x ∈ H, FixR.rho C.h91_F4 ⟨x, hx⟩ ∈ Subgroup.zpowers e := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem Pe_le_H_F4 (e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) : C.Pe_F4 e ≤ H :=
  Subgroup.map_subtype_le _

theorem le_Q_of_isPGroup_F4 {e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (he5 : e ^ 5 = 1) {X : Subgroup G} (hX : X ≤ C.Pe_F4 e) (h2 : IsPGroup 2 X) :
    X ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro x hx
  obtain ⟨hxH, hxe⟩ := (C.mem_Pe_F4).mp (hX hx)
  obtain ⟨k, hk⟩ := h2 ⟨x, hx⟩
  have hx2 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set r := FixR.rho C.h91_F4 ⟨x, hxH⟩ with hr
  have hr5 : r ^ 5 = 1 := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxe
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he5, one_zpow]
  have hr2 : r ^ 2 ^ k = 1 := by
    rw [hr, ← map_pow]
    have : (⟨x, hxH⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hx2)
    rw [this, map_one]
  have hr1 : r = 1 := by
    have h1 : orderOf r ∣ 5 := orderOf_dvd_of_pow_eq_one hr5
    have h2' : orderOf r ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hr2
    have : orderOf r = 1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num))
      h1 h2'
    exact orderOf_eq_one_iff.mp this
  exact (FixR.rho_eq_one_iff C.h91_F4 ⟨x, hxH⟩).mp hr1

theorem pow_five_of_odd_F4 {e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (he5 : e ^ 5 = 1) {x : G} (hx : x ∈ C.Pe_F4 e) (ho : Odd (orderOf x)) : x ^ 5 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx5 : x ^ 5 ∈ pCoreOf 2 H := by
    have hle := C.le_Q_of_isPGroup_F4 he5 (X := Subgroup.zpowers (x ^ 5)) ?_ ?_
    · exact hle (Subgroup.mem_zpowers _)
    · exact Subgroup.zpowers_le.mpr ((C.Pe_F4 e).pow_mem hx 5)
    ·
      obtain ⟨hxH, hxe⟩ := (C.mem_Pe_F4).mp hx
      have hr5 : FixR.rho C.h91_F4 ⟨x, hxH⟩ ^ 5 = 1 := by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxe
        rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he5, one_zpow]
      have hq : x ^ 5 ∈ pCoreOf 2 H := by
        rw [← map_pow] at hr5
        simpa using (FixR.rho_eq_one_iff C.h91_F4 _).mp hr5
      exact (pCoreOf_isPGroup 2 H).to_le (Subgroup.zpowers_le.mpr hq)

  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hx5⟩
  have h1 : (x ^ 5) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hodd : Odd (orderOf (x ^ 5)) := Odd.of_dvd_nat ho (orderOf_pow_dvd 5)
  have h2 : orderOf (x ^ 5) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (x ^ 5) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)) dvd_rfl h2
  exact orderOf_eq_one_iff.mp h3

theorem exists_mem_K_F4 {e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))} (he5 : e ^ 5 = 1)
    (he1 : e ≠ 1)
    (heE : e ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H))) :
    ∃ z : ↥H, (z : G) ∈ oTwoUpper (C.Pe_F4 e) ∧ FixR.rho C.h91_F4 z ≠ 1 ∧
      FixR.rho C.h91_F4 z ∈ Subgroup.zpowers e ∧ e ∈ Subgroup.zpowers (FixR.rho C.h91_F4 z) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, -, rfl⟩ := (FixR.mem_autOn_tilde_iff C.h91_F4 C.hYH).mp heE
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hyP : (y : G) ∈ C.Pe_F4 (FixR.rho C.h91_F4 y) := (C.mem_Pe_F4).mpr ⟨y.2, Subgroup.mem_zpowers _⟩
  refine ⟨y ^ 2 ^ k, ?_, ?_, ?_, ?_⟩
  · refine mem_oTwoUpper_of_odd (by simpa using (C.Pe_F4 _).pow_mem hyP (2 ^ k)) ?_
    have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
    have : orderOf ((y : G) ^ 2 ^ k) = m := by
      rw [orderOf_pow' _ h2k, Subgroup.orderOf_coe, hkm, Nat.gcd_mul_right_left,
        Nat.mul_div_cancel_left _ (by positivity)]
    simpa [this] using hm
  · rw [map_pow]
    intro h1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_eq_prime he5 he1] at hdvd
    exact absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd))) (by norm_num)
  · rw [map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rw [map_pow]
    exact A4.mem_zpowers_pow_of_coprime (by
      rw [orderOf_eq_prime he5 he1]
      exact Nat.Coprime.pow_left k (by norm_num))

theorem mem_normalizer_Pe_F4 {e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))} (t : ↥H)
    (ht : FixR.rho C.h91_F4 t * e * (FixR.rho C.h91_F4 t)⁻¹ ∈ Subgroup.zpowers e) :
    (t : G) ∈ Subgroup.normalizer (C.Pe_F4 e : Set G) := by
  have key : ∀ x ∈ C.Pe_F4 e, (t : G) * x * (t : G)⁻¹ ∈ C.Pe_F4 e := by
    intro x hx
    obtain ⟨hxH, hxe⟩ := (C.mem_Pe_F4).mp hx
    refine (C.mem_Pe_F4).mpr ⟨H.mul_mem (H.mul_mem t.2 hxH) (H.inv_mem t.2), ?_⟩
    have e1 : FixR.rho C.h91_F4 ⟨(t : G) * x * (t : G)⁻¹,
        H.mul_mem (H.mul_mem t.2 hxH) (H.inv_mem t.2)⟩ =
        FixR.rho C.h91_F4 t * FixR.rho C.h91_F4 ⟨x, hxH⟩ * (FixR.rho C.h91_F4 t)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxe
    rw [← hj, ← conj_zpow]
    exact Subgroup.zpow_mem _ ht j
  exact Subgroup.mem_normalizer_fintype key

end Ctx_F4

end CFSG.Quasithin.H13.L32A.S2

end
