module

public import CFSG.LargeExtraspecial.S11MbBasic
public import CFSG.LargeExtraspecial.S11MbComm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

variable (hy : Hyp S g) (K : Conf S g t τ u) {kb : G} (hb : kb * S.z * kb⁻¹ ∈ S.QG ⊓ S.Qa u)
  (hbs : S.cl (kb * S.z * kb⁻¹) ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹))
include hy K hb hbs

theorem Conf.exists_mem_Qa_commute :
    ∃ h' ∈ S.Qa u, h' * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * h' ∧
      h' * (kb * S.z * kb⁻¹) ≠ kb * S.z * kb⁻¹ * h' := by
  set T := S.conjBy u with hT
  have hTz : T.z = (τ : G) := K.conj_eq.symm
  have haT : g * S.z * g⁻¹ ∈ T.QG := K.mem_Qa
  have hbT : kb * S.z * kb⁻¹ ∈ T.QG := (mem_inf.mp hb).2
  have hτQ : (τ : G) ∉ S.QG := K.not_mem_QG
  have hb0 : T.cl (kb * S.z * kb⁻¹) ≠ 0 := by
    rw [Ne, T.cl_eq_zero_iff hbT, hTz]
    rintro (h | h)
    · exact conj_z_ne_one S kb h
    · exact hτQ (h ▸ (mem_inf.mp hb).1)
  have hba : T.cl (kb * S.z * kb⁻¹) ≠ T.cl (g * S.z * g⁻¹) := by
    rw [Ne, T.cl_eq_cl_iff hbT haT, hTz]
    rintro (h | h)
    · apply hbs
      rw [h]
      exact Submodule.mem_span_singleton_self _
    · apply hτQ
      have e : (kb * S.z * kb⁻¹)⁻¹ * (g * S.z * g⁻¹) = (τ : G) := by
        rw [h]
        group
      rw [← e]
      exact S.QG.mul_mem (S.QG.inv_mem (mem_inf.mp hb).1) hy.hyp4.conj_mem
  obtain ⟨w, hw0, hw1⟩ := T.exists_polar_eq_zero_eq_one hb0 hba
  obtain ⟨h', hh', rfl⟩ := T.exists_cl w
  exact ⟨h', hh', ((T.polar_cl_eq_zero_iff hh' haT).mp hw0),
    (T.polar_cl_eq_one_iff hh' hbT).mp hw1⟩

variable {h' : G} (hh' : h' ∈ S.Qa u) (hha : h' * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * h')
  (hhb : h' * (kb * S.z * kb⁻¹) ≠ kb * S.z * kb⁻¹ * h')
include hh' hha hhb

omit hy hbs hha in
theorem Conf.conj_b_eq : (h' * kb) * S.z * (h' * kb)⁻¹ = (τ : G) * (kb * S.z * kb⁻¹) := by
  rcases K.conj_eq_or' hh' (mem_inf.mp hb).2 with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact absurd h2 hhb
  · rw [← h1]
    group

variable (hCE : CentralExtInput.{u_G}) (hn : 6 ≤ S.width)
include hCE hn

omit hbs in
theorem Conf.yData_conj : YData S g t τ u kb (h' * S.z * h'⁻¹) h' := by
  have hyM := K.conj_mem_M hh' hy
  have hyQ := K.conj_not_mem_QG hh' hy hCE hb hhb
  have haE := K.a_mem_E hy
  have haB : g * S.z * g⁻¹ ∈ S.Qa h' := (K.mem_Qa_conj_iff hh' haE).mpr hha
  have hbB : kb * S.z * kb⁻¹ ∉ S.Qa h' := fun h => hhb ((K.mem_Qa_conj_iff hh' hb).mp h)
  have hk : g * S.z * g⁻¹ ∈ S.QG ⊓ S.Qa u ⊓ S.Qa h' := mem_inf.mpr ⟨haE, haB⟩
  have hyN := K.rho_conj_mem_Nbar hh' hy hyQ hk
  have hτh : Commute h' (τ : G) := K.commute_of_mem_Qa hh'
  have hzτ : Commute S.z (τ : G) := (S.z_comm τ.2).symm
  have hyτ : Commute (h' * S.z * h'⁻¹) (τ : G) := (hτh.mul_left hzτ).mul_left hτh.inv_left
  have hbQ : kb * S.z * kb⁻¹ ∈ S.QG := (mem_inf.mp hb).1
  have hbz : kb * S.z * kb⁻¹ ≠ S.z := (K.base_of_mem hb).1
  refine ⟨rfl, hyM, hyQ, fun e he => K.conj_commute_of_mem hh' he, hyτ.eq, haB, hbB, ?_, ?_,
    fun w hw => K.apply_sub_mem_Vt_of_commute hy hCE hn hyM
      (fun e he => K.conj_commute_of_mem hh' he) hyN
      (fun ℓ hℓ => K.rho_conj_commute hh' hy hCE hℓ) hw⟩
  · rw [← K.conj_b_eq hb hh' hhb, show (h' * kb) * S.z * (h' * kb)⁻¹ =
      h' * (kb * S.z * kb⁻¹) * h'⁻¹ by group]
    have := conj_mem_Qa_mul S (h := h') (g := 1) (x := kb * S.z * kb⁻¹)
      (by rw [S.Qa_one]; exact hbQ)
    rwa [mul_one] at this
  ·
    intro hyτQ
    apply hbB
    have hyz : h' * S.z * h'⁻¹ * S.z ∈ S.Qa u := by
      rw [show h' * S.z * h'⁻¹ * S.z = h' * (S.z * h'⁻¹ * S.z⁻¹) by rw [S.z_inv]; group]
      exact mul_mem hh' (K.z_conj_mem_Qa (inv_mem hh'))
    have hτu : (τ : G) ∈ S.Qa u := by rw [K.conj_eq]; exact S.conj_z_mem_Qa u
    have he : h' * S.z * h'⁻¹ * S.z * τ ∈ S.QG ⊓ S.Qa u := by
      refine mem_inf.mpr ⟨?_, mul_mem hyz hτu⟩
      rw [mul_assoc, ← S.z_comm τ.2, ← mul_assoc]
      exact S.QG.mul_mem hyτQ S.z_mem_QG
    have hτb : (τ : G) ∈ S.Qa kb := by
      have hne : kb * S.z * kb⁻¹ ≠ u * S.z * u⁻¹ := fun h =>
        K.not_mem_QG (by rw [K.conj_eq, ← h]; exact hbQ)
      rw [K.conj_eq]
      exact S.mem_Qa_symm hne (mem_inf.mp hb).2
    have hyb : h' * S.z * h'⁻¹ ∈ S.Qa kb := by
      have e : h' * S.z * h'⁻¹ = (h' * S.z * h'⁻¹ * S.z * τ) * τ * S.z := by
        calc h' * S.z * h'⁻¹ = h' * S.z * h'⁻¹ * (S.z * S.z) * ((τ : G) * τ) := by
              rw [K.tau_mul_self, S.z_mul_z, mul_one, mul_one]
          _ = h' * S.z * h'⁻¹ * S.z * (S.z * τ) * τ := by group
          _ = h' * S.z * h'⁻¹ * S.z * (τ * S.z) * τ := by rw [S.z_comm τ.2]
          _ = h' * S.z * h'⁻¹ * S.z * τ * (S.z * τ) := by group
          _ = h' * S.z * h'⁻¹ * S.z * τ * (τ * S.z) := by rw [S.z_comm τ.2]
          _ = _ := by group
      rw [e]
      exact mul_mem (mul_mem (K.mem_Qa_of_mem_E hy hb he) hτb) (S.z_mem_Qa hbQ hbz)
    exact S.mem_Qa_symm (fun h => hyQ (by rw [h]; exact hbQ)) hyb

omit hbs in
theorem Conf.yData_mul : ∃ u₃ : G,
    YData S g t τ u kb (h' * S.z * h'⁻¹ * ((τ : G) * (kb * S.z * kb⁻¹))) u₃ := by
  have Y := K.yData_conj hy hb hh' hha hhb hCE hn
  have hkd := K.conj_b_eq hb hh' hhb
  set y := h' * S.z * h'⁻¹ with hy_def
  set d := (τ : G) * (kb * S.z * kb⁻¹) with hd_def
  have hbQ : kb * S.z * kb⁻¹ ∈ S.QG := (mem_inf.mp hb).1
  have haE := K.a_mem_E hy
  have hτb : (τ : G) * (kb * S.z * kb⁻¹) = kb * S.z * kb⁻¹ * τ :=
    (K.commute_of_mem_Qa (mem_inf.mp hb).2).symm
  have hdτ : d * τ = kb * S.z * kb⁻¹ := by
    rw [hd_def, hτb, mul_assoc, K.tau_mul_self, mul_one]
  have hyd : y ≠ d := fun h => Y.mul_tau_not_mem (by rw [h, hdτ]; exact hbQ)
  have hyQd : y ∈ S.Qa (h' * kb) :=
    S.mem_Qa_symm (g₁ := h' * kb) (g₂ := h') (by rw [hkd]; exact hyd.symm)
      (by rw [hkd]; exact Y.tau_b_mem)
  have hdd : d ∈ S.Qa (h' * kb) := by rw [← hkd]; exact S.conj_z_mem_Qa _
  have hmemd : ∀ x, h'⁻¹ * x * h' ∈ S.Qa kb → x ∈ S.Qa (h' * kb) := fun x hx =>
    S.mem_Qa_mul_iff.mpr hx
  have hτQb : (τ : G) ∈ S.Qa kb := by
    have hne : kb * S.z * kb⁻¹ ≠ u * S.z * u⁻¹ := fun h =>
      K.not_mem_QG (by rw [K.conj_eq, ← h]; exact hbQ)
    rw [K.conj_eq]
    exact S.mem_Qa_symm hne (mem_inf.mp hb).2
  have hbb : kb * S.z * kb⁻¹ ∈ S.Qa kb := S.conj_z_mem_Qa kb
  have had : g * S.z * g⁻¹ ∈ S.Qa (h' * kb) := hmemd _ (by
    rw [show h'⁻¹ * (g * S.z * g⁻¹) * h' = g * S.z * g⁻¹ by
      rw [mul_assoc, ← hha]; group]
    exact K.mem_Qa_of_mem_E hy hb haE)
  have hbd : kb * S.z * kb⁻¹ ∈ S.Qa (h' * kb) := hmemd _ (by
    rcases K.conj_eq_or hh' (mem_inf.mp hb).2 with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact absurd h2 hhb
    · rw [h1]
      exact mul_mem hτQb hbb)
  obtain ⟨q, hq, hqy, hle⟩ := exists_conj_inf_le hyQd (by rw [hkd]; exact hyd)
  rw [hkd] at hqy
  have hconj : y * d = (q * h') * S.z * (q * h')⁻¹ := by
    calc y * d = q * y * q⁻¹ := hqy.symm
      _ = (q * h') * S.z * (q * h')⁻¹ := by rw [hy_def]; group
  have hdd1 : d * d = 1 := by
    have := conj_z_mul_self S (h' * kb)
    rwa [hkd] at this
  have hM3 : y * d ∈ S.M := S.M.mul_mem Y.mem_M (S.M.mul_mem τ.2 (S.QG_le_M hbQ))
  have hne : u * S.z * u⁻¹ ≠ S.z := fun h => K.not_mem_QG (by rw [K.conj_eq, h]; exact S.z_mem_QG)
  have hyQ := K.conj_not_mem_QG hh' hy hCE hb hhb
  have hk : g * S.z * g⁻¹ ∈ S.QG ⊓ S.Qa u ⊓ S.Qa h' := mem_inf.mpr ⟨haE, Y.a_mem⟩
  have hyN := K.rho_conj_mem_Nbar hh' hy hyQ hk
  refine ⟨q * h', hconj, hM3, fun h => Y.mul_tau_not_mem ?_, fun e he => ?_, ?_,
    hle _ ⟨Y.a_mem, had⟩, fun hbq => ?_, hle _ ⟨Y.tau_b_mem, hdd⟩, ?_, fun w hw => ?_⟩
  · have := S.QG.mul_mem h (S.QG.inv_mem hbQ)
    rwa [hd_def, ← mul_assoc, mul_inv_cancel_right] at this
  · have h1 : Commute y e := Y.comm e he
    have h2 : Commute (τ : G) e := (K.commute_of_mem_Qa (mem_inf.mp he).2).symm
    have h3 : Commute (kb * S.z * kb⁻¹) e := S.QG_inf_Qa_comm hne hb he
    exact (h1.mul_left (h2.mul_left h3)).eq
  · have h1 : Commute y (τ : G) := Y.comm_tau
    have h3 : Commute (kb * S.z * kb⁻¹) (τ : G) := hτb.symm
    exact (h1.mul_left ((Commute.refl (τ : G)).mul_left h3)).eq
  · have hy3d : (q * h') * S.z * (q * h')⁻¹ ∈ S.Qa (h' * kb) := by
      rw [← hconj]
      exact mul_mem hyQd hdd
    have hne3 : (q * h') * S.z * (q * h')⁻¹ ≠ (h' * kb) * S.z * (h' * kb)⁻¹ := by
      rw [← hconj, hkd]
      intro h
      apply conj_z_ne_one S h'
      calc h' * S.z * h'⁻¹ = y * d * d⁻¹ := by rw [mul_inv_cancel_right]
        _ = 1 := by rw [h, mul_inv_cancel]
    obtain ⟨q', -, hq'y, hle'⟩ := exists_conj_inf_le hy3d hne3
    have hyy : (q' * (q * h')) * S.z * (q' * (q * h'))⁻¹ = h' * S.z * h'⁻¹ := by
      calc (q' * (q * h')) * S.z * (q' * (q * h'))⁻¹ =
            q' * ((q * h') * S.z * (q * h')⁻¹) * q'⁻¹ := by group
        _ = (q * h') * S.z * (q * h')⁻¹ * ((h' * kb) * S.z * (h' * kb)⁻¹) := hq'y
        _ = y * d * d := by rw [← hconj, hkd]
        _ = h' * S.z * h'⁻¹ := by rw [mul_assoc, hdd1, mul_one]
    have := hle' _ ⟨hbq, hbd⟩
    rw [S.Qa_eq_of_conj_eq hyy] at this
    exact Y.b_not_mem this
  · rw [mul_assoc, hdτ]
    intro h
    apply Y.not_mem_QG
    have := S.QG.mul_mem h (S.QG.inv_mem hbQ)
    rwa [mul_inv_cancel_right] at this
  · have hρ : S.ρ ⟨y * d, hM3⟩ = S.ρ ⟨y, Y.mem_M⟩ * t := by
      have e : (⟨y * d, hM3⟩ : S.M) =
          ⟨y, Y.mem_M⟩ * (τ * ⟨kb * S.z * kb⁻¹, S.QG_le_M hbQ⟩) := Subtype.ext rfl
      rw [e, map_mul, map_mul, K.rho_eq,
        (S.ρ_eq_one_iff ⟨kb * S.z * kb⁻¹, S.QG_le_M hbQ⟩).mpr hbQ, mul_one]
    rw [hρ, coe_mul_apply]
    have h1 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
      rw [← K.timmesfeld_11_7 hy hCE]
      exact sub_mem_Tt hw
    have h2 := (mem_Nbar.mp hyN).2 _ h1
    have e : (S.ρ ⟨y, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - w =
        (S.ρ ⟨y, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) +
          ((S.ρ ⟨y, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by
      rw [map_sub]
      abel
    rw [e, h2]
    exact add_mem h1 (Y.apply_sub_mem w hw)

end CFSG.LargeExtraspecial.S11
