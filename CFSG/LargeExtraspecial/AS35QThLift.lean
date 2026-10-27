module

public import CFSG.LargeExtraspecial.AS35QThXb
public import CFSG.LargeExtraspecial.AS35QThSec2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QTh

open Subgroup QuadraticMap CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

structure ThLift (S : Setting G) extends ThSetup S where
  Zh : G
  hZhM : Zh ∈ S.M
  hZh : S.ρ ⟨Zh, hZhM⟩ = ζ
  hZt : Zh * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * Zh
  hZ3 : Zh ^ 3 = 1

theorem pow_four_pow_eq {H : Type*} [Monoid H] {x : H} (hx : x ^ 3 = 1) (j : ℕ) :
    x ^ (2 ^ j * 2 ^ j) = x := by
  have h41 : 4 ^ j % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [← mul_pow, show (2 * 2 : ℕ) = 4 by norm_num, ← Nat.div_add_mod (4 ^ j) 3, pow_add,
    pow_mul, hx, one_pow, one_mul, h41, pow_one]

theorem exists_lift (T : ThSetup S) (hS : S.SixHyp) : Nonempty (ThLift S) := by
  obtain ⟨⟨m, hmM⟩, hm⟩ := T.hXM T.hζX
  have htbM : S.ρ ⟨_, T.hgM⟩ ∈ S.Mbar := ⟨_, rfl⟩
  obtain ⟨m', hm'M, hm't, hρ⟩ := S.exists_commute_rho_eq_J hS T.hgD T.hgM hmM (by
    rw [hm]
    exact (T.hζM _ htbM).symm)
  rw [hm] at hρ
  have h3M : m' ^ 3 ∈ S.M := S.M.pow_mem hm'M 3
  have h3Q : m' ^ 3 ∈ S.QG := by
    have e : (⟨m' ^ 3, h3M⟩ : S.M) = ⟨m', hm'M⟩ ^ 3 := rfl
    have h1 : S.ρ ⟨m' ^ 3, h3M⟩ = 1 := by rw [e, map_pow, hρ, T.hζ3]
    exact (S.ρ_eq_one_iff _).mp h1
  obtain ⟨k, hk⟩ := S.isPGroup_QG ⟨m' ^ 3, h3Q⟩
  have hk' : (m' ^ 3) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have hZM : m' ^ (2 ^ j * 2 ^ j) ∈ S.M := S.M.pow_mem hm'M _
  refine ⟨{ T with
    Zh := m' ^ (2 ^ j * 2 ^ j)
    hZhM := hZM
    hZh := ?_
    hZt := (Commute.pow_left hm't _).eq
    hZ3 := ?_ }⟩
  · have e : (⟨m' ^ (2 ^ j * 2 ^ j), hZM⟩ : S.M) = ⟨m', hm'M⟩ ^ (2 ^ j * 2 ^ j) := rfl
    rw [e, map_pow, hρ, pow_four_pow_eq T.hζ3]
  · rw [← pow_mul, show 2 ^ j * 2 ^ j * 3 = 3 * 2 ^ j * 2 ^ j by ring, pow_mul, pow_mul, ← hj,
      pow_orderOf_eq_one, one_pow]

namespace ThLift

variable (T : ThLift S)

theorem rhoL_Zh (v : S.Qt) : S.rhoL T.hZhM v = (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
  rw [Setting.rhoL, T.hZh]

@[expose] noncomputable def secData : SecData S where
  ζ := (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap
  l := T.l
  hl := T.hl
  Zh := T.Zh
  hZhM := T.hZhM
  hZh := T.rhoL_Zh

theorem zeta_sq (v : S.Qt) :
    (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) +
      (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v + v = 0 :=
  T.secData.zeta_sq v

theorem zeta_cube (v : S.Qt) :
    (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) = v := by
  have := congrArg (fun s : S.O => (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) T.hζ3
  simp only [apply_pow_three] at this
  exact this

theorem eq_zero_of_zeta {v : S.Qt} (h : (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : v = 0 := by
  have := T.zeta_sq v
  rwa [h, h, add_self_zmod2, zero_add] at this

theorem eq_one_or_z_of_commute {x : G} (hx : x ∈ S.QG) (hc : x * T.Zh = T.Zh * x) :
    x = 1 ∨ x = S.z := by
  rw [← S.cl_eq_zero_iff hx]
  apply T.eq_zero_of_zeta
  rw [← T.rhoL_Zh, S.rhoL_cl T.hZhM hx, ← hc, mul_inv_cancel_right]

theorem Zh_inv : T.Zh⁻¹ = T.Zh * T.Zh :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact T.hZ3)

theorem exists_commute_rho_eq {m : G} (hm : m ∈ S.M) :
    ∃ m' : G, ∃ hm' : m' ∈ S.M, m' * T.Zh = T.Zh * m' ∧ S.ρ ⟨m', hm'⟩ = S.ρ ⟨m, hm⟩ := by
  have hZM := T.hZhM
  set x := m * T.Zh * m⁻¹ with hx
  have hxM : x ∈ S.M := S.M.mul_mem (S.M.mul_mem hm hZM) (S.M.inv_mem hm)
  have hρx : S.ρ ⟨x, hxM⟩ = T.ζ := by
    have e : (⟨x, hxM⟩ : S.M) = ⟨m, hm⟩ * ⟨T.Zh, hZM⟩ * ⟨m, hm⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, T.hZh, T.hζM _ ⟨_, rfl⟩, mul_inv_cancel_right]
  set u := T.Zh⁻¹ * x with hu
  have huM : u ∈ S.M := S.M.mul_mem (S.M.inv_mem hZM) hxM
  have huQ : u ∈ S.QG := by
    have e : (⟨u, huM⟩ : S.M) = (⟨T.Zh, hZM⟩ : S.M)⁻¹ * ⟨x, hxM⟩ := rfl
    have h1 : S.ρ ⟨u, huM⟩ = 1 := by rw [e, map_mul, map_inv, T.hZh, hρx, inv_mul_cancel]
    exact (S.ρ_eq_one_iff _).mp h1
  set w := S.cl u
  obtain ⟨q, hq, hcl⟩ :=
    S.exists_cl ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) w))
  have hconj : T.Zh * T.Zh * q * (T.Zh * T.Zh)⁻¹ = T.Zh⁻¹ * q * T.Zh := by
    rw [← T.Zh_inv, inv_inv]
  have hwQ : T.Zh⁻¹ * q * T.Zh * q⁻¹ ∈ S.QG := by
    rw [← hconj]
    exact S.QG.mul_mem (conj2_mem_QG hZM hq) (S.QG.inv_mem hq)
  have hc : S.cl u = S.cl (T.Zh⁻¹ * q * T.Zh * q⁻¹) := by
    rw [← hconj, S.cl_mul (conj2_mem_QG hZM hq) (S.QG.inv_mem hq), S.cl_inv hq,
      cl_conj2_Zh hZM hq, T.rhoL_Zh, T.rhoL_Zh, hcl, T.zeta_cube]
    have h := T.zeta_sq w
    calc w = (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) +
          (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) w + w + w := by rw [h, zero_add]
      _ = _ := by rw [add_assoc _ w w, add_self_zmod2, add_zero, add_comm]
  rcases (S.cl_eq_cl_iff huQ hwQ).mp hc with h | h
  · refine ⟨q⁻¹ * m, S.M.mul_mem (S.M.inv_mem (S.QG_le_M hq)) hm, ?_, ?_⟩
    · have h1 : q * T.Zh * q⁻¹ = x := by
        calc q * T.Zh * q⁻¹ = T.Zh * (T.Zh⁻¹ * q * T.Zh * q⁻¹) := by group
          _ = x := by rw [h, hu]; group
      calc q⁻¹ * m * T.Zh = q⁻¹ * x * m := by rw [hx]; group
        _ = T.Zh * (q⁻¹ * m) := by rw [← h1]; group
    · have e : (⟨q⁻¹ * m, S.M.mul_mem (S.M.inv_mem (S.QG_le_M hq)) hm⟩ : S.M) =
          (⟨q, S.QG_le_M hq⟩ : S.M)⁻¹ * ⟨m, hm⟩ := rfl
      rw [e, map_mul, map_inv, (S.ρ_eq_one_iff _).mpr hq, inv_one, one_mul]
  · exfalso
    have h1 : q * T.Zh * q⁻¹ = x * S.z := by
      calc q * T.Zh * q⁻¹ = T.Zh * (T.Zh⁻¹ * q * T.Zh * q⁻¹) := by group
        _ = x * S.z := by rw [h, hu]; group
    have h2 : (q * T.Zh * q⁻¹) ^ 3 = 1 := by
      rw [← MulAut.conj_apply, ← map_pow, T.hZ3, map_one]
    have hxz : x * S.z = S.z * x := S.z_comm hxM
    have h3 : (x * S.z) ^ 3 = S.z := by
      rw [(Commute.mul_pow hxz 3), hx, ← MulAut.conj_apply, ← map_pow, T.hZ3, map_one,
        one_mul, pow_three, S.z_mul_z, mul_one]
    rw [h1, h3] at h2
    exact S.z_ne_one h2

end ThLift

end CFSG.LargeExtraspecial.AS35QTh
