module

public import CFSG.LargeExtraspecial.AS35QThLift
public import CFSG.LargeExtraspecial.AS35QIxBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_lift (S : Setting G) {W x : G} (hWM : W ∈ S.M) (hxM : x ∈ S.M)
    (hW3 : W ^ 3 = 1) (hx3 : x ^ 3 = 1) (hρ : S.ρ ⟨x, hxM⟩ = S.ρ ⟨W, hWM⟩)
    (hfpf : ∀ v, S.rhoL hWM (S.rhoL hWM v) + S.rhoL hWM v + v = 0) :
    ∃ q ∈ S.QG, q * W * q⁻¹ = x := by
  set u := W⁻¹ * x with hu
  have huM : u ∈ S.M := S.M.mul_mem (S.M.inv_mem hWM) hxM
  have huQ : u ∈ S.QG := by
    have e : (⟨u, huM⟩ : S.M) = (⟨W, hWM⟩ : S.M)⁻¹ * ⟨x, hxM⟩ := rfl
    have h1 : S.ρ ⟨u, huM⟩ = 1 := by rw [e, map_mul, map_inv, hρ, inv_mul_cancel]
    exact (S.ρ_eq_one_iff _).mp h1
  set w := S.cl u
  obtain ⟨q, hq, hcl⟩ := S.exists_cl (S.rhoL hWM (S.rhoL hWM w))
  have hWinv : W⁻¹ = W * W := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hW3)
  have hconj : W * W * q * (W * W)⁻¹ = W⁻¹ * q * W := by rw [← hWinv, inv_inv]
  have hwQ : W⁻¹ * q * W * q⁻¹ ∈ S.QG := by
    rw [← hconj]
    exact S.QG.mul_mem (AS35QTh.conj2_mem_QG hWM hq) (S.QG.inv_mem hq)
  have hc : S.cl u = S.cl (W⁻¹ * q * W * q⁻¹) := by
    rw [← hconj, S.cl_mul (AS35QTh.conj2_mem_QG hWM hq) (S.QG.inv_mem hq), S.cl_inv hq,
      AS35QTh.cl_conj2_Zh hWM hq, hcl, zeta_cube hfpf]
    have h := hfpf w
    calc w = S.rhoL hWM (S.rhoL hWM w) + S.rhoL hWM w + w + w := by rw [h, zero_add]
      _ = _ := by rw [add_assoc _ w w, AS35QTh.add_self_V, add_zero, add_comm]
  rcases (S.cl_eq_cl_iff huQ hwQ).mp hc with h | h
  · refine ⟨q, hq, ?_⟩
    calc q * W * q⁻¹ = W * (W⁻¹ * q * W * q⁻¹) := by group
      _ = x := by rw [h, hu]; group
  · exfalso
    have h1 : q * W * q⁻¹ = x * S.z := by
      calc q * W * q⁻¹ = W * (W⁻¹ * q * W * q⁻¹) := by group
        _ = x * S.z := by rw [h, hu]; group
    have h2 : (q * W * q⁻¹) ^ 3 = 1 := by
      rw [← MulAut.conj_apply, ← map_pow, hW3, map_one]
    have hxz : x * S.z = S.z * x := S.z_comm hxM
    have h3 : (x * S.z) ^ 3 = S.z := by
      rw [Commute.mul_pow hxz 3, hx3, one_mul, pow_three, S.z_mul_z, mul_one]
    rw [h1, h3] at h2
    exact S.z_ne_one h2

variable {S : Setting G}

structure IxLift (S : Setting G) extends IxSetup S where
  Zh : G
  hZhM : Zh ∈ S.M
  hZh : S.ρ ⟨Zh, hZhM⟩ = ζ
  hZt : Zh * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * Zh
  hZ3 : Zh ^ 3 = 1

theorem IxSetup.exists_lift (T : IxSetup S) (hS : S.SixHyp) : Nonempty (IxLift S) := by
  obtain ⟨⟨m, hmM⟩, hm⟩ := T.hXM T.hζX
  obtain ⟨m', hm'M, hm't, hρ⟩ := S.exists_commute_rho_eq_J hS T.hgD T.hgM hmM (by
    rw [hm]
    exact T.hζt)
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
    rw [e, map_pow, hρ, AS35QTh.pow_four_pow_eq T.hζ3]
  · rw [← pow_mul, show 2 ^ j * 2 ^ j * 3 = 3 * 2 ^ j * 2 ^ j by ring, pow_mul, pow_mul, ← hj,
      pow_orderOf_eq_one, one_pow]

namespace IxLift

variable (T : IxLift S)

theorem rhoL_Zh (v : S.Qt) : S.rhoL T.hZhM v = (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
  rw [Setting.rhoL, T.hZh]

theorem Zh_t : T.Zh * T.t = T.t * T.Zh := T.hZt

theorem eq_one_or_z_of_commute {x : G} (hx : x ∈ S.QG) (hc : x * T.Zh = T.Zh * x) :
    x = 1 ∨ x = S.z := by
  rw [← S.cl_eq_zero_iff hx]
  apply T.zeta_fix
  rw [← T.rhoL_Zh, S.rhoL_cl T.hZhM hx, ← hc, mul_inv_cancel_right]

theorem Zh_inv_mem_M : T.Zh⁻¹ ∈ S.M := S.M.inv_mem T.hZhM

theorem rhoL_Zh_inv (v : S.Qt) : S.rhoL T.Zh_inv_mem_M v =
    ((T.ζ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
  rw [Setting.rhoL, show (⟨T.Zh⁻¹, T.Zh_inv_mem_M⟩ : S.M) = (⟨T.Zh, T.hZhM⟩ : S.M)⁻¹ from rfl,
    map_inv, T.hZh]

theorem zeta_inv_apply (v : S.Qt) : ((T.ζ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
    (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
  have e : T.ζ⁻¹ = T.ζ * T.ζ := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact T.hζ3)
  rw [e]
  rfl

@[expose] def InN (n : G) : Prop := n * T.Zh * n⁻¹ = T.Zh ∨ n * T.Zh * n⁻¹ = T.Zh⁻¹

theorem exists_mem_N {m : G} (hm : m ∈ S.M) : ∃ q ∈ S.QG, T.InN (q⁻¹ * m) := by
  have hxM : m * T.Zh * m⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hm T.hZhM) (S.M.inv_mem hm)
  have hx3 : (m * T.Zh * m⁻¹) ^ 3 = 1 := by
    rw [← MulAut.conj_apply, ← map_pow, T.hZ3, map_one]
  have hρx : S.ρ ⟨m * T.Zh * m⁻¹, hxM⟩ = S.ρ ⟨m, hm⟩ * T.ζ * (S.ρ ⟨m, hm⟩)⁻¹ := by
    rw [show (⟨m * T.Zh * m⁻¹, hxM⟩ : S.M) = ⟨m, hm⟩ * ⟨T.Zh, T.hZhM⟩ * (⟨m, hm⟩ : S.M)⁻¹
      from rfl, map_mul, map_mul, map_inv, T.hZh]
  have hZ3' : T.Zh⁻¹ ^ 3 = 1 := by rw [inv_pow, T.hZ3, inv_one]
  rcases T.conj_zeta (⟨_, rfl⟩ : S.ρ ⟨m, hm⟩ ∈ S.Mbar) with h | h
  · obtain ⟨q, hq, hqx⟩ := exists_conj_of_lift S T.hZhM hxM T.hZ3 hx3 (by rw [hρx, h, T.hZh])
      (fun v => by simp only [T.rhoL_Zh]; exact T.hζ2 v)
    refine ⟨q, hq, Or.inl ?_⟩
    calc q⁻¹ * m * T.Zh * (q⁻¹ * m)⁻¹ = q⁻¹ * (m * T.Zh * m⁻¹) * q := by group
      _ = T.Zh := by rw [← hqx]; group
  · obtain ⟨q, hq, hqx⟩ := exists_conj_of_lift S T.Zh_inv_mem_M hxM hZ3' hx3
      (by
        rw [hρx, h, show (⟨T.Zh⁻¹, T.Zh_inv_mem_M⟩ : S.M) = (⟨T.Zh, T.hZhM⟩ : S.M)⁻¹ from rfl,
          map_inv, T.hZh])
      (fun v => by
        simp only [T.rhoL_Zh_inv, T.zeta_inv_apply]
        rw [zeta_cube T.hζ2 ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v),
          add_comm ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v)]
        exact T.hζ2 v)
    refine ⟨q, hq, Or.inr ?_⟩
    calc q⁻¹ * m * T.Zh * (q⁻¹ * m)⁻¹ = q⁻¹ * (m * T.Zh * m⁻¹) * q := by group
      _ = q⁻¹ * (q * T.Zh⁻¹ * q⁻¹) * q := by rw [hqx]
      _ = T.Zh⁻¹ := by group

theorem InN.mul {n n' : G} (hn : T.InN n) (hn' : T.InN n') : T.InN (n * n') := by
  have e : n * n' * T.Zh * (n * n')⁻¹ = n * (n' * T.Zh * n'⁻¹) * n⁻¹ := by group
  have einv : n * T.Zh⁻¹ * n⁻¹ = (n * T.Zh * n⁻¹)⁻¹ := by group
  rcases hn' with h' | h' <;> rw [InN, e, h']
  · exact hn
  · rw [einv]
    rcases hn with h | h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h, inv_inv])

theorem InN.inv {n : G} (hn : T.InN n) : T.InN n⁻¹ := by
  rcases hn with h | h
  · left
    calc n⁻¹ * T.Zh * n⁻¹⁻¹ = n⁻¹ * (n * T.Zh * n⁻¹) * n⁻¹⁻¹ := by rw [h]
      _ = T.Zh := by group
  · right
    calc n⁻¹ * T.Zh * n⁻¹⁻¹ = n⁻¹ * (n * T.Zh * n⁻¹)⁻¹ * n⁻¹⁻¹ := by rw [h, inv_inv, inv_inv]
      _ = T.Zh⁻¹ := by group

theorem eq_one_or_z_of_mem_N {x : G} (hx : x ∈ S.QG) (hxN : T.InN x) : x = 1 ∨ x = S.z := by
  rcases hxN with h | h
  · exact T.eq_one_or_z_of_commute hx (by
      calc x * T.Zh = x * T.Zh * x⁻¹ * x := by group
        _ = T.Zh * x := by rw [h])
  · exfalso
    have hxM := S.QG_le_M hx
    have h1 : S.ρ ⟨x * T.Zh * x⁻¹, S.M.mul_mem (S.M.mul_mem hxM T.hZhM) (S.M.inv_mem hxM)⟩ =
        T.ζ := by
      rw [show (⟨x * T.Zh * x⁻¹, S.M.mul_mem (S.M.mul_mem hxM T.hZhM) (S.M.inv_mem hxM)⟩ : S.M)
        = ⟨x, hxM⟩ * ⟨T.Zh, T.hZhM⟩ * (⟨x, hxM⟩ : S.M)⁻¹ from rfl, map_mul, map_mul, map_inv,
        (S.ρ_eq_one_iff ⟨x, hxM⟩).mpr hx, T.hZh]
      group
    have h2 : S.ρ ⟨x * T.Zh * x⁻¹, S.M.mul_mem (S.M.mul_mem hxM T.hZhM) (S.M.inv_mem hxM)⟩ =
        T.ζ⁻¹ := by
      rw [show (⟨x * T.Zh * x⁻¹, S.M.mul_mem (S.M.mul_mem hxM T.hZhM) (S.M.inv_mem hxM)⟩ : S.M)
        = (⟨T.Zh, T.hZhM⟩ : S.M)⁻¹ from Subtype.ext h, map_inv, T.hZh]
    exact T.zeta_ne_inv (h1.symm.trans h2)

theorem comm_or_of_mem_N {n n' : G} (hn : n ∈ S.M) (hn' : n' ∈ S.M) (hnN : T.InN n)
    (hn'N : T.InN n') (hc : S.ρ ⟨n, hn⟩ * S.ρ ⟨n', hn'⟩ = S.ρ ⟨n', hn'⟩ * S.ρ ⟨n, hn⟩) :
    n * n' * n⁻¹ * n'⁻¹ = 1 ∨ n * n' * n⁻¹ * n'⁻¹ = S.z := by
  have hM : n * n' * n⁻¹ * n'⁻¹ ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem (S.M.mul_mem hn hn') (S.M.inv_mem hn)) (S.M.inv_mem hn')
  have hQ : n * n' * n⁻¹ * n'⁻¹ ∈ S.QG := by
    refine (S.ρ_eq_one_iff ⟨_, hM⟩).mp ?_
    rw [show (⟨n * n' * n⁻¹ * n'⁻¹, hM⟩ : S.M) = ⟨n, hn⟩ * ⟨n', hn'⟩ * (⟨n, hn⟩ : S.M)⁻¹ *
      (⟨n', hn'⟩ : S.M)⁻¹ from rfl, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  exact T.eq_one_or_z_of_mem_N hQ (((hnN.mul T hn'N).mul T hnN.inv).mul T hn'N.inv)

end IxLift

end CFSG.LargeExtraspecial.AS35QIx
