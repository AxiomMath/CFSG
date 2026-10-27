module

public import CFSG.GF2Type.Smith1979.CaseIIA3
public import CFSG.GF2Type.Smith1979.CaseIIA2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

@[expose] def Tk (t k : S.O) (hkt : k * t = t * k) (htt : t * t = 1) : Subgroup S.O where
  carrier := {r | r * t = t * r ∧ (r * k * r⁻¹ = k ∨ r * k * r⁻¹ = k * t)}
  mul_mem' := by
    rintro r r' ⟨hr, hrk⟩ ⟨hr', hrk'⟩
    refine ⟨by rw [mul_assoc, hr', ← mul_assoc, hr, mul_assoc], ?_⟩
    have hrt : r * t * r⁻¹ = t := by rw [hr]; group
    have e : r * r' * k * (r * r')⁻¹ = r * (r' * k * r'⁻¹) * r⁻¹ := by group
    rw [e]
    rcases hrk' with h | h
    · rw [h]
      exact hrk
    · rw [h]
      have e2 : r * (k * t) * r⁻¹ = (r * k * r⁻¹) * (r * t * r⁻¹) := by group
      rw [e2, hrt]
      rcases hrk with h2 | h2
      · right
        rw [h2]
      · left
        rw [h2, mul_assoc, htt, mul_one]
  one_mem' := ⟨by simp, Or.inl (by simp)⟩
  inv_mem' := by
    rintro r ⟨hr, hrk⟩
    have hr' : r⁻¹ * t = t * r⁻¹ := by
      calc r⁻¹ * t = r⁻¹ * (t * r) * r⁻¹ := by group
        _ = r⁻¹ * (r * t) * r⁻¹ := by rw [hr]
        _ = t * r⁻¹ := by group
    refine ⟨hr', ?_⟩
    have e : r⁻¹ * k * r⁻¹⁻¹ = r⁻¹ * k * r := by group
    rw [e]
    have hrt : r⁻¹ * t * r = t := by rw [hr']; group
    rcases hrk with h | h
    · left
      calc r⁻¹ * k * r = r⁻¹ * (r * k * r⁻¹) * r := by rw [h]
        _ = k := by group
    · right
      have hk' : (r * k * r⁻¹) * t = k := by rw [h, mul_assoc, htt, mul_one]
      calc r⁻¹ * k * r = r⁻¹ * ((r * k * r⁻¹) * t) * r := by rw [hk']
        _ = (r⁻¹ * (r * k * r⁻¹) * r) * (r⁻¹ * t * r) := by group
        _ = k * t := by rw [show r⁻¹ * (r * k * r⁻¹) * r = k by group, hrt]

namespace Data

variable (D : Data S g t)
include D

theorem htt' : t * t = 1 := mul_self_of_mem_Lbar S D.H.conj_mem D.ht

theorem eq_one_or_eq_t_of_conj {h : S.M} (hr : S.ρ h ∈ Rbar S g t) {z : S.O}
    (hzX : z ∈ S.Lbar ((h : G) * g)) (hz : IsK t z) : z = 1 ∨ z = t := by
  have hX := Lbar_mul S h g
  rw [hX] at hzX
  obtain ⟨l', hl', hzl'⟩ := hzX
  have hcomm : S.ρ h * t = t * S.ρ h := commute_of_mem_Rbar D.H.conj_mem hr
  have hcomm' : (S.ρ h)⁻¹ * t = t * (S.ρ h)⁻¹ :=
    calc (S.ρ h)⁻¹ * t = (S.ρ h)⁻¹ * (t * S.ρ h) * (S.ρ h)⁻¹ := by group
      _ = (S.ρ h)⁻¹ * (S.ρ h * t) * (S.ρ h)⁻¹ := by rw [hcomm]
      _ = t * (S.ρ h)⁻¹ := by group
  have hzl : z = S.ρ h * l' * (S.ρ h)⁻¹ := hzl'.symm
  have hfix : ∀ v ∈ Ea S g ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (l' : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro v hv
    have h1 : ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      apply_mem_commSpace_of_commute hcomm hv.2
    have h2 := hz.fix _ h1
    rw [hzl] at h2
    have h3 : l' = (S.ρ h)⁻¹ * z * S.ρ h := by rw [hzl]; group
    rw [h3, coe_mul_apply, coe_mul_apply, hz.fix _ h1]
    exact inv_apply_apply_O _ v
  rcases D.eq_one_or_eq_t hl' hfix with h1 | h1
  · left
    rw [hzl, h1]
    group
  · right
    rw [hzl, h1]
    calc S.ρ h * t * (S.ρ h)⁻¹ = t * S.ρ h * (S.ρ h)⁻¹ := by rw [hcomm]
      _ = t := by group

theorem mem_Tk_gen {k : S.O} (hkM : k ∈ S.Mbar) (hk : IsK t k) {r l : S.O}
    (hr : r ∈ Rbar S g t) (hl : l ∈ S.Lbar g) : r * l * r⁻¹ ∈ Tk t k hk.comm D.htt' := by
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
  have hX := Lbar_mul S h g
  have hfix : ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) =
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
    have h1 := hk.fix _ (Vt_le_commSpace D.H D.ht1
      (apply_mem_Vt_of_mem_Rbar D.H.conj_mem hr (cl_a_mem_Vt D.ht)))
    rwa [ρ_cl_conj_z S h D.H.conj_mem] at h1
  have hnorm := mem_normalizer_of_fix D.H.conj_mem D.H.conj_ne hkM hfix
  have hu : S.ρ h * l * (S.ρ h)⁻¹ ∈ S.Lbar ((h : G) * g) := by
    rw [hX]
    exact ⟨l, hl, rfl⟩
  have hkuX : k * (S.ρ h * l * (S.ρ h)⁻¹) * k⁻¹ ∈ S.Lbar ((h : G) * g) :=
    (mem_normalizer_iff.mp hnorm _).mp hu
  have hzX : k * (S.ρ h * l * (S.ρ h)⁻¹) * k⁻¹ * (S.ρ h * l * (S.ρ h)⁻¹)⁻¹ ∈
      S.Lbar ((h : G) * g) := mul_mem hkuX (inv_mem hu)
  have hRu : S.ρ h * l * (S.ρ h)⁻¹ ∈ Rbar S g t :=
    mul_mem (mul_mem hr (Lbar_le_Rbar D.ht hl)) (inv_mem hr)
  have hcu : S.ρ h * l * (S.ρ h)⁻¹ ∈ centralizer ({t} : Set S.O) :=
    Rbar_le_centralizer D.H.conj_mem hRu
  have hck : k ∈ centralizer ({t} : Set S.O) := mem_centralizer_singleton_iff.mpr hk.comm
  have hcz : k * (S.ρ h * l * (S.ρ h)⁻¹) * k⁻¹ * (S.ρ h * l * (S.ρ h)⁻¹)⁻¹ ∈
      centralizer ({t} : Set S.O) :=
    mul_mem (mul_mem (mul_mem hck hcu) (inv_mem hck)) (inv_mem hcu)
  have hzK : IsK t (k * (S.ρ h * l * (S.ρ h)⁻¹) * k⁻¹ * (S.ρ h * l * (S.ρ h)⁻¹)⁻¹) := by
    refine ⟨mem_centralizer_singleton_iff.mp hcz, fun w hw => ?_⟩
    have hw1 : (((S.ρ h * l * (S.ρ h)⁻¹)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈
        commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      apply_mem_commSpace_of_commute (commute_of_mem_Rbar D.H.conj_mem (inv_mem hRu)) hw
    have hk' := (IsK.inv hk).fix _ hw1
    rw [coe_mul_apply, coe_mul_apply, coe_mul_apply, hk', apply_inv_apply_O]
    exact hk.fix w hw
  have hz := D.eq_one_or_eq_t_of_conj hr hzX hzK
  have hcomm_t : S.ρ h * l * (S.ρ h)⁻¹ * t = t * (S.ρ h * l * (S.ρ h)⁻¹) :=
    mem_centralizer_singleton_iff.mp hcu
  refine ⟨hcomm_t, ?_⟩
  have e : S.ρ h * l * (S.ρ h)⁻¹ * k * (S.ρ h * l * (S.ρ h)⁻¹)⁻¹ =
      (k * (S.ρ h * l * (S.ρ h)⁻¹) * k⁻¹ * (S.ρ h * l * (S.ρ h)⁻¹)⁻¹)⁻¹ * k := by group
  rw [e]
  rcases hz with h1 | h1
  · left
    rw [h1]
    simp
  · right
    rw [h1]
    have htt := D.htt'
    have : t⁻¹ = t := by
      calc t⁻¹ = t⁻¹ * (t * t) := by rw [htt, mul_one]
        _ = t := by group
    rw [this]
    exact hk.comm.symm

theorem eq_one_or_eq_t_of_K {k : S.O} (hkM : k ∈ S.Mbar) (hk : IsK t k) : k = 1 ∨ k = t := by
  have hRle : Rbar S g t ≤ Tk t k hk.comm D.htt' := by
    refine (Rbar_le_closure_conj (dtEqConj_of_linCase D.H D.hL)).trans ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨r, hr, l, hl, rfl⟩
    exact D.mem_Tk_gen hkM hk hr hl
  exact D.K1 hk fun r hr => (hRle hr).2

end Data

end CFSG.GF2Type.Smith1979.Case2
