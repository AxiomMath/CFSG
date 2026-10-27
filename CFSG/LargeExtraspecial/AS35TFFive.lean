module

public import CFSG.LargeExtraspecial.AS35TPBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

namespace AS35T

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem commute_of_mem_zConj_of_mem_DSet (hS : S.SixHyp) {t h : G} (ht : t ∈ S.DSet)
    (hh : h * S.z * h⁻¹ = t) {a b : G} (ha : a ∈ S.zConj (S.HAt h))
    (hb : b ∈ S.zConj (S.HAt h)) : a * b = b * a := by
  obtain ⟨⟨_, _, -, hcomm, -⟩, -⟩ := (hS.sixFour _ (S.isHStar_of_mem_ESet ht.1 hh).1).1
  exact hcomm a ha b hb

theorem commute_of_fix_commSpace {σ τ : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hσ : σ ∈ TauCeti.QuadraticMap.orthogonalGroup S.q)
    (hτ : τ ∈ TauCeti.QuadraticMap.orthogonalGroup S.q)
    (hfix : ∀ v ∈ commSpace τ, σ v = v) (v : S.Qt) : σ (τ v) = τ (σ v) := by
  have hperp : σ v - v ∈ fixSpace τ := by
    rw [S.fixSpace_eq_orthogonal_commSpace_of_isometry hτ, LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    change polar S.q u (σ v - v) = 0
    rw [QuadraticMap.polar_sub_right]
    nth_rewrite 1 [← hfix u hu]
    rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hσ, sub_self]
  have h1 := hfix _ (sub_mem_commSpace τ v)
  have h2 := mem_fixSpace.mp hperp
  rw [map_sub] at h1 h2
  rw [sub_eq_iff_eq_add] at h1 h2
  rw [h1, h2]
  abel

theorem fiveFive (hS : S.SixHyp) {t : G} (ht : t ∈ S.DSet) {x : G} (hxM : x ∈ S.M)
    (hx : ∀ q ∈ S.QG, x * (t * q * t⁻¹ * q⁻¹) = (t * q * t⁻¹ * q⁻¹) * x) : x * t = t * x := by
  obtain ⟨h, hh⟩ := S.exists_conj_of_mem_DSet ht
  have hS4 := hS.sixFour
  have htM := S.mem_M_of_mem_ESet hS4 ht.1
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hfix : ∀ v ∈ commSpace (S.rhoL htM), S.rhoL hxM v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
    obtain ⟨q, hq, rfl⟩ := S.exists_cl u
    have hcQ : t * q * t⁻¹ * q⁻¹ ∈ S.QG := S.QG.mul_mem (S.conj_mem_QG htM hq) (S.QG.inv_mem hq)
    have hc : S.rhoL htM (S.cl q) - S.cl q = S.cl (t * q * t⁻¹ * q⁻¹) := by
      rw [S.rhoL_cl htM hq, S.cl_mul (S.conj_mem_QG htM hq) (S.QG.inv_mem hq), S.cl_inv hq,
        sub_eq_add_vec (ZMod 2)]
    rw [hc, S.rhoL_cl hxM hcQ, hx q hq]
    congr 1
    group
  have hcO : S.ρ ⟨x, hxM⟩ * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * S.ρ ⟨x, hxM⟩ :=
    Subtype.ext (LinearEquiv.ext
      (AS35T.commute_of_fix_commSpace S (S.rhoL_mem hxM) (S.rhoL_mem htM) hfix))
  have hsD : x * t * x⁻¹ ∈ S.DSet := S.conj_mem_DSet hxM ht
  have hsM : x * t * x⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hxM htM) (S.M.inv_mem hxM)
  have hρs : S.ρ ⟨x * t * x⁻¹, hsM⟩ = S.ρ ⟨t, htM⟩ := by
    have e : (⟨x * t * x⁻¹, hsM⟩ : S.M) = ⟨x, hxM⟩ * ⟨t, htM⟩ * ⟨x, hxM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hcO]
    group
  have hsH := S.mem_zConj_of_rho_eq hS hsD ht hh hsM htM hρs
  by_cases hst : x * t * x⁻¹ = t
  · calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [hst]
  exfalso
  obtain ⟨b, hbH, hbz, hbt, hbs⟩ : ∃ b ∈ S.zConj (S.HAt h), b ≠ S.z ∧ b ≠ t ∧
      b ≠ x * t * x⁻¹ := by
    obtain ⟨p, p', hpH, hpz, hpt, hp'H, hp'z, hp't, hne⟩ := S.exists_two_mem_delta_J ht hh
    by_cases hps : p = x * t * x⁻¹
    · exact ⟨p', hp'H, hp'z, hp't, fun h' => hne (hps.trans h'.symm)⟩
    · exact ⟨p, hpH, hpz, hpt, hps⟩
  obtain ⟨q, hq, hqb⟩ := S.exists_conj_eq_of_mem_zConj hS ht hh hbH hbz
  have htH := S.mem_zConj_of_mem_ESet ht.1 hh
  have hzH := Asc77.self_mem_conjIn S.z (S.HAt h)
  have htb : t * b = b * t := AS35T.commute_of_mem_zConj_of_mem_DSet S hS ht hh htH hbH
  have hzb : S.z * b = b * S.z := AS35T.commute_of_mem_zConj_of_mem_DSet S hS ht hh hzH hbH
  have hzt : S.z * t = t * S.z := AS35T.commute_of_mem_zConj_of_mem_DSet S hS ht hh hzH htH
  have hxtb : x * (t * b) * x⁻¹ = t * b := by
    have e : t * q * t⁻¹ * q⁻¹ = t * b := by
      rw [← hqb, htinv]
      group
    rw [← e, hx q hq]
    group
  have hxb : x * b * x⁻¹ = x * t * x⁻¹ * (t * b) := by
    calc x * b * x⁻¹ = x * (t * t) * b * x⁻¹ := by rw [htt, mul_one]
      _ = x * t * x⁻¹ * (x * (t * b) * x⁻¹) := by group
      _ = x * t * x⁻¹ * (t * b) := by rw [hxtb]
  have htQt : t ∈ S.Qa h := hh ▸ S.conj_z_mem_Qa h
  have h1 : x * t * x⁻¹ * S.z ∈ S.Qa h := S.mul_z_mem_Qa_of_mem_zConj hS ht hh hsH hst
  have h2 : b * S.z ∈ S.Qa h := S.mul_z_mem_Qa_of_mem_zConj hS ht hh hbH hbt
  have e : x * t * x⁻¹ * S.z * t * (b * S.z) = x * t * x⁻¹ * (t * b) := by
    calc x * t * x⁻¹ * S.z * t * (b * S.z) = x * t * x⁻¹ * (S.z * t) * (b * S.z) := by group
      _ = x * t * x⁻¹ * (t * S.z) * (S.z * b) := by rw [hzt, hzb]
      _ = x * t * x⁻¹ * t * (S.z * S.z) * b := by group
      _ = x * t * x⁻¹ * (t * b) := by rw [S.z_mul_z]; group
  have hxbQ : x * b * x⁻¹ ∈ S.Qa h := by
    rw [hxb, ← e]
    exact (S.Qa h).mul_mem ((S.Qa h).mul_mem h1 htQt) h2
  obtain ⟨k, -, hk⟩ := hbH
  have hw := AS35T.conj_eq_of_conj_mem_Qa S hS.weak (g := h) (k := x * k) (by
    rw [show x * k * S.z * (x * k)⁻¹ = x * (k * S.z * k⁻¹) * x⁻¹ by group, hk]
    exact hxbQ)
  rw [show x * k * S.z * (x * k)⁻¹ = x * (k * S.z * k⁻¹) * x⁻¹ by group, hk, hh, hxb] at hw
  apply hbs
  calc b = t * (t * b) * b * b := by rw [← mul_assoc, htt, one_mul, mul_assoc, ← mul_assoc b,
          S.mul_self_of_isConj (isConj_iff.mpr ⟨k, hk⟩), one_mul]
    _ = x * t * x⁻¹ * (t * b) * (t * b) * b * b := by rw [hw]
    _ = x * t * x⁻¹ * (t * (b * t) * b) * b * b := by group
    _ = x * t * x⁻¹ := by
      rw [← htb, show t * (t * b) * b = (t * t) * (b * b) by group, htt,
        S.mul_self_of_isConj (isConj_iff.mpr ⟨k, hk⟩), mul_one, mul_one, mul_assoc,
        S.mul_self_of_isConj (isConj_iff.mpr ⟨k, hk⟩), mul_one]

end AS35T

end Setting

end CFSG.LargeExtraspecial
