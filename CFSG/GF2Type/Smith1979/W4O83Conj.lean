module

public import CFSG.GF2Type.Smith1979.W4O83Plane
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.LargeExtraspecial.S6Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4O83

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.Open
open CFSG.RankThree.Literature.FSmith (zmod2_cases)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

@[expose] noncomputable def Ob (S : Setting G) : Subgroup S.O :=
  (timmesfeldOddCore S.Mbar).map S.Mbar.subtype

theorem normal_timmesfeldOddCore (K : Type*) [Group K] : (timmesfeldOddCore K).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

theorem odd_card_timmesfeldOddCore (K : Type*) [Group K] [Finite K] :
    Odd (Nat.card (timmesfeldOddCore K)) :=
  CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := K)

theorem conj_mem_Ob {x y : S.O} (hx : x ∈ S.Mbar) (hy : y ∈ Ob S) : x * y * x⁻¹ ∈ Ob S := by
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹, (normal_timmesfeldOddCore S.Mbar).conj_mem y' hy' ⟨x, hx⟩,
    rfl⟩

theorem odd_orderOf_of_mem_Ob {y : S.O} (hy : y ∈ Ob S) : Odd (orderOf y) := by
  obtain ⟨y', hy', rfl⟩ := hy
  have h1 : orderOf (⟨y', hy'⟩ : timmesfeldOddCore S.Mbar) ∣
      Nat.card (timmesfeldOddCore S.Mbar) := orderOf_dvd_natCard _
  have h2 := (odd_card_timmesfeldOddCore S.Mbar).of_dvd_nat h1
  rw [Subgroup.orderOf_mk] at h2
  rw [show orderOf (S.Mbar.subtype y') = orderOf y' from Subgroup.orderOf_coe y']
  exact h2

theorem eq_one_of_odd_orderOf {H : Type*} [Group H] {c : H} (hodd : Odd (orderOf c)) {n : ℕ}
    (h : c ^ 2 ^ n = 1) : c = 1 := by
  have h1 : orderOf c ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h
  have h2 : Nat.Coprime (orderOf c) (2 ^ n) := (Nat.coprime_two_right.mpr hodd).pow_right n
  exact orderOf_eq_one_iff.mp (h2.eq_one_of_dvd h1)

theorem Omega83Config.theta_mem_Ob (C : Omega83Config S) (i : Fin 4) : C.theta i ∈ Ob S :=
  C.theta_mem_oddCore i

theorem Omega83Pre.exists_lift (C : Omega83Pre S) (i : Fin 4) :
    ∃ θ₀ : S.M, S.ρ θ₀ = C.theta i ∧ (θ₀ : G) ^ 3 = 1 := by
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (C.theta_mem_Mbar i)
  have hm3 : S.ρ (m ^ 3) = 1 := by rw [map_pow, hm, C.theta_pow_three]
  have hmQ : m ^ 3 ∈ S.Q := S.mem_Q_of_ρ_eq_one hm3
  obtain ⟨j, hj⟩ := S.extraspecial.1 ⟨m ^ 3, hmQ⟩
  have hj' : (m ^ 3) ^ 2 ^ j = 1 := by
    have := congrArg (fun x : S.Q => ((x : S.M))) hj
    simpa using this
  have h44 : (4 : ℕ) ^ j = 2 ^ j * 2 ^ j := by
    rw [← mul_pow]
    norm_num
  refine ⟨m ^ 4 ^ j, ?_, ?_⟩
  · rw [map_pow, hm]
    have h4 : 4 ^ j % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    calc C.theta i ^ 4 ^ j = C.theta i ^ (3 * (4 ^ j / 3) + 4 ^ j % 3) := by
          rw [Nat.div_add_mod]
      _ = C.theta i := by
          rw [h4, pow_add, pow_mul, C.theta_pow_three, one_pow, one_mul, pow_one]
  · have h : (m ^ 4 ^ j) ^ 3 = 1 := by
      calc (m ^ 4 ^ j) ^ 3 = (m ^ 3) ^ 4 ^ j := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ = ((m ^ 3) ^ 2 ^ j) ^ 2 ^ j := by rw [h44, pow_mul]
        _ = 1 := by rw [hj', one_pow]
    simpa using congrArg Subtype.val h

theorem mul_comm_of_apply_eq {x y : G} (hxM : x ∈ S.M) (hx3 : x ^ 3 = 1) (hy : y ∈ S.QG)
    (h : (S.ρ ⟨x, hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) = S.cl y) : x * y = y * x := by
  have hxy : x * y * x⁻¹ ∈ S.QG := S.conj_mem_QG hxM hy
  rw [S.ρ_cl ⟨x, hxM⟩ hy] at h
  rcases (S.cl_eq_cl_iff hy hxy).mp h.symm with h2 | h2
  · calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h2]
  · exfalso
    have hz : x * S.z = S.z * x := S.z_comm hxM
    have hxz : x * S.z * x⁻¹ = S.z := by
      rw [hz]
      group
    have h3 : x ^ 2 * y * (x ^ 2)⁻¹ = y := by
      calc x ^ 2 * y * (x ^ 2)⁻¹ = x * (x * y * x⁻¹) * x⁻¹ := by
            rw [pow_two]
            group
        _ = x * (y * S.z) * x⁻¹ := by rw [h2]
        _ = (x * y * x⁻¹) * (x * S.z * x⁻¹) := by group
        _ = (y * S.z) * S.z := by rw [h2, hxz]
        _ = y := by rw [mul_assoc, S.z_mul_z, mul_one]
    have h4 : x ^ 2 * y = y * x ^ 2 := by
      calc x ^ 2 * y = (x ^ 2 * y * (x ^ 2)⁻¹) * x ^ 2 := by group
        _ = y * x ^ 2 := by rw [h3]
    have hxx : x = (x ^ 2) ^ 2 := by
      calc x = x * x ^ 3 := by rw [hx3, mul_one]
        _ = (x ^ 2) ^ 2 := by group
    have h5 : x * y = y * x := by
      have hc : Commute (x ^ 2) y := h4
      rw [hxx]
      exact (hc.pow_left 2).eq
    have h6 : x * y * x⁻¹ = y := by
      calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [h5]
        _ = y := by group
    rw [h6] at h2
    exact S.z_ne_one (by simpa using h2)

theorem commutator_mem_Q {θ₀ x₀ : S.M} (hθ : S.ρ θ₀ ∈ Ob S) {n : ℕ}
    (h2 : ((θ₀ * x₀ * θ₀⁻¹ * x₀⁻¹ : S.M) : G) ^ 2 ^ n = 1) :
    ((θ₀ * x₀ * θ₀⁻¹ * x₀⁻¹ : S.M) : G) ∈ S.QG := by
  rw [← S.ρ_eq_one_iff]
  have hmem : S.ρ (θ₀ * x₀ * θ₀⁻¹ * x₀⁻¹) ∈ Ob S := by
    have e : S.ρ (θ₀ * x₀ * θ₀⁻¹ * x₀⁻¹) =
        S.ρ θ₀ * (S.ρ x₀ * (S.ρ θ₀)⁻¹ * (S.ρ x₀)⁻¹) := by
      simp [map_mul, map_inv, mul_assoc]
    rw [e]
    exact mul_mem hθ (conj_mem_Ob ⟨x₀, rfl⟩ (inv_mem hθ))
  have hpow : S.ρ (θ₀ * x₀ * θ₀⁻¹ * x₀⁻¹) ^ 2 ^ n = 1 := by
    rw [← map_pow]
    have : (θ₀ * x₀ * θ₀⁻¹ * x₀⁻¹ : S.M) ^ 2 ^ n = 1 := Subtype.ext (by simpa using h2)
    rw [this, map_one]
  exact eq_one_of_odd_orderOf (odd_orderOf_of_mem_Ob hmem) hpow

theorem Lbar_conj_mem {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    {x : S.O} (hx : x ∈ S.Mbar)
    (hfix : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    {ℓ : S.O} (hℓ : ℓ ∈ S.Lbar g) : x * ℓ * x⁻¹ ∈ S.Lbar g := by
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hx
  have h1 : S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) = S.cl (g * S.z * g⁻¹) := by
    rw [← S4.ρ_cl_conj_z S m haQ]
    exact hfix
  have h2 := S4.Lbar_eq_of_cl_eq S haQ hne (S4.conj_mem_QG' S m.2 haQ) h1
  rw [S4.Lbar_mul S m g] at h2
  rw [← h2]
  exact Subgroup.mem_map.mpr ⟨ℓ, hℓ, rfl⟩

theorem Omega83Pre.apply_Lbar_comm (C : Omega83Pre S) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    {ℓ : S.O} (hℓ : ℓ ∈ S.Lbar g) (k : Fin 4) (hcomm : C.theta k * ℓ = ℓ * C.theta k) {p : S.Qt}
    (hp : p ∈ C.plane k) : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p := by
  refine C.eq_of_comm_th (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) ?_ ?_ hp
  · intro v
    have h := S.sq_eq_one_of_mem_Lbar haQ hℓ
    have := congrArg (fun x : S.O => ((x : S.Qt ≃ₗ[ZMod 2] S.Qt)) v) h
    simpa [pow_two] using this
  · intro v
    have := congrArg (fun x : S.O => ((x : S.Qt ≃ₗ[ZMod 2] S.Qt)) v) hcomm.symm
    simpa [Omega83Pre.th] using this

theorem Omega83Config.th_ne_cl_conj_z (C : Omega83Config S) {g : G} (H : Hyp4 S g) (k : Fin 4) :
    C.th k (S.cl (g * S.z * g⁻¹)) ≠ S.cl (g * S.z * g⁻¹) := by
  intro hfix
  have haQ := H.conj_mem
  have hne := H.conj_ne
  have hnorm : ∀ ℓ ∈ S.Lbar g, C.theta k * ℓ * (C.theta k)⁻¹ ∈ S.Lbar g := fun ℓ hℓ =>
    Lbar_conj_mem haQ hne (C.theta_mem_Mbar k) hfix hℓ
  have hcomm : ∀ ℓ ∈ S.Lbar g, C.theta k * ℓ = ℓ * C.theta k := by
    intro ℓ hℓ
    have hc1 : C.theta k * ℓ * (C.theta k)⁻¹ * ℓ⁻¹ ∈ S.Lbar g :=
      mul_mem (hnorm ℓ hℓ) (inv_mem hℓ)
    have hc2 : C.theta k * ℓ * (C.theta k)⁻¹ * ℓ⁻¹ ∈ Ob S := by
      have : C.theta k * ℓ * (C.theta k)⁻¹ * ℓ⁻¹ = C.theta k * (ℓ * (C.theta k)⁻¹ * ℓ⁻¹) := by
        group
      rw [this]
      exact mul_mem (C.theta_mem_Ob k)
        (conj_mem_Ob (S.Lbar_le_Mbar g hℓ) (inv_mem (C.theta_mem_Ob k)))
    have hc3 : (C.theta k * ℓ * (C.theta k)⁻¹ * ℓ⁻¹) ^ 2 ^ 1 = 1 := by
      simpa using S.sq_eq_one_of_mem_Lbar haQ hc1
    have h1 := eq_one_of_odd_orderOf (odd_orderOf_of_mem_Ob hc2) hc3
    calc C.theta k * ℓ = C.theta k * ℓ * (C.theta k)⁻¹ * ℓ⁻¹ * (ℓ * C.theta k) := by group
      _ = ℓ * C.theta k := by rw [h1, one_mul]
  have hle : C.plane k ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    intro p hp
    rw [← H.fixSub_eq, mem_fixSub]
    exact fun ℓ hℓ => C.apply_Lbar_comm haQ hℓ k (hcomm ℓ hℓ) hp
  have h1 := Submodule.finrank_mono hle
  rw [C.finrank_plane k, finrank_span_singleton (cl_conj_z_ne_zero S haQ hne)] at h1
  omega

theorem Omega83Config.eq_one_of_comm_th (C : Omega83Config S) {g : G} (H : Hyp4 S g)
    (Cn : Cons311 S g) {ℓ : S.O} (hℓ : ℓ ∈ S.Lbar g) (k : Fin 4)
    (hcomm : C.theta k * ℓ = ℓ * C.theta k) : ℓ = 1 := by
  have haQ := H.conj_mem
  apply Cn.faithful ℓ hℓ
  intro v hv
  have h1 := S6.Lbar_apply_sub_mem_span' haQ hv hℓ
  have h2 : ∀ w ∈ C.plane k, polar S.q ((ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) w = 0 := by
    intro w hw
    have h3 := polar_apply_O ℓ v w
    rw [C.apply_Lbar_comm haQ hℓ k hcomm hw] at h3
    rw [polar_sub_left, h3, sub_self]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
  rcases zmod2_cases c with rfl | rfl
  · rw [zero_smul] at hc
    exact sub_eq_zero.mp hc.symm
  · exfalso
    rw [one_smul] at hc
    apply C.th_ne_cl_conj_z H k
    have h3 := (C.th_eq_iff k _).mpr (C.prL_eq_zero_of_polar h2)
    rwa [← hc] at h3

theorem Omega83Pre.exists_apply_prL (C : Omega83Pre S) {u w : S.Qt}
    (hu : ∀ k, C.th k u ≠ u) (hw : ∀ k, C.th k w ≠ w) (k : Fin 4) :
    ∃ y : S.O, y ∈ S.Mbar ∧ (∀ j, j ≠ k → ∀ v ∈ C.plane j, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) ∧
      (∀ v ∈ C.plane k, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ C.plane k) ∧
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (C.prL k u) = C.prL k w := by
  have hq0 : C.prL k u ≠ 0 := (C.th_ne_iff k u).mp (hu k)
  have hw0 : C.prL k w ≠ 0 := (C.th_ne_iff k w).mp (hw k)
  rcases C.mem_orbit (C.prL_mem_plane k u) hq0 (C.prL_mem_plane k w) with h | h | h | h
  · exact absurd h hw0
  · exact ⟨1, one_mem _, fun j _ v _ => rfl, fun v hv => hv, by simpa using h.symm⟩
  · exact ⟨C.theta k, C.theta_mem_Mbar k, fun j hj v hv => C.apply_theta_of_ne k j hj.symm v hv,
      fun v hv => C.th_mem_plane hv, h.symm⟩
  · refine ⟨C.theta k ^ 2, pow_mem (C.theta_mem_Mbar k) 2, fun j hj v hv => ?_,
      fun v hv => ?_, ?_⟩
    · simp only [pow_two, Subgroup.coe_mul, LinearEquiv.mul_apply]
      rw [C.apply_theta_of_ne k j hj.symm v hv, C.apply_theta_of_ne k j hj.symm v hv]
    · simp only [pow_two, Subgroup.coe_mul, LinearEquiv.mul_apply]
      exact C.th_mem_plane (C.th_mem_plane hv)
    · simp only [pow_two, Subgroup.coe_mul, LinearEquiv.mul_apply]
      exact h.symm

theorem Omega83Pre.exists_apply_eq (C : Omega83Pre S) {u w : S.Qt}
    (hu : ∀ k, C.th k u ≠ u) (hw : ∀ k, C.th k w ≠ w) :
    ∃ x ∈ S.Mbar, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u = w := by
  choose y hyM hyfix hyinv hyapp using fun k => C.exists_apply_prL hu hw k
  have key : ∀ k : Fin 4, ∀ v ∈ C.plane k,
      ((y 0 * y 1 * y 2 * y 3 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
        (y k : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
    intro k v hv
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
    fin_cases k
    · rw [hyfix 3 0 (by decide) v hv, hyfix 2 0 (by decide) v hv, hyfix 1 0 (by decide) v hv]
      rfl
    · rw [hyfix 3 1 (by decide) v hv, hyfix 2 1 (by decide) v hv,
        hyfix 0 1 (by decide) _ (hyinv 1 v hv)]
      rfl
    · rw [hyfix 3 2 (by decide) v hv, hyfix 1 2 (by decide) _ (hyinv 2 v hv),
        hyfix 0 2 (by decide) _ (hyinv 2 v hv)]
      rfl
    · rw [hyfix 2 3 (by decide) _ (hyinv 3 v hv), hyfix 1 3 (by decide) _ (hyinv 3 v hv),
        hyfix 0 3 (by decide) _ (hyinv 3 v hv)]
      rfl
  refine ⟨y 0 * y 1 * y 2 * y 3, mul_mem (mul_mem (mul_mem (hyM 0) (hyM 1)) (hyM 2)) (hyM 3),
    ?_⟩
  conv_lhs => rw [← C.sum_prL u]
  rw [map_sum]
  conv_rhs => rw [← C.sum_prL w]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [key k _ (C.prL_mem_plane k u), hyapp k]

theorem Omega83Pre.exists_conj_of_full (C : Omega83Pre S) {g : G} (H : Hyp4 S g)
    (hg : ∀ k, C.th k (S.cl (g * S.z * g⁻¹)) ≠ S.cl (g * S.z * g⁻¹)) {y : G}
    (hy : y ∈ S.QG) (hfull : ∀ k, C.th k (S.cl y) ≠ S.cl y) :
    ∃ k : G, y = k * S.z * k⁻¹ := by
  obtain ⟨x, hx, hxy⟩ := C.exists_apply_eq hg hfull
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [S4.ρ_cl_conj_z S m H.conj_mem] at hxy
  have hbQ := S4.conj_mem_QG' S m.2 H.conj_mem
  have hy0 : S.cl y ≠ 0 := fun h => hfull 0 (by rw [h, map_zero])
  rcases (S.cl_eq_cl_iff hbQ hy).mp hxy with h | h
  · exact ⟨(m : G) * g, h⟩
  · have hbz : (m : G) * g * S.z * ((m : G) * g)⁻¹ ≠ S.z := by
      intro hb
      apply hy0
      rw [← hxy, hb, S.cl_z]
    obtain ⟨u, -, hub⟩ := S.exists_conj_eq_mul_z hbQ (S4.conj_z_ne_one S ((m : G) * g)) hbz
    refine ⟨u * ((m : G) * g), ?_⟩
    rw [h, ← hub]
    group

theorem Omega83Config.exists_conj_of_full (C : Omega83Config S) {g : G} (H : Hyp4 S g) {y : G}
    (hy : y ∈ S.QG) (hfull : ∀ k, C.th k (S.cl y) ≠ S.cl y) :
    ∃ k : G, y = k * S.z * k⁻¹ :=
  C.toOmega83Pre.exists_conj_of_full H (C.th_ne_cl_conj_z H) hy hfull

end CFSG.GF2Type.Smith1979.W4O83
