module

public import CFSG.LargeExtraspecial.S10EightB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

section Centre

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem conj_mem_centreGroup {c : U} {e : U ≃ₗ[ZMod 2] U} (he : e ∈ centreGroup U c)
    (γ : U ≃ₗ[ZMod 2] U) : γ * e * γ⁻¹ ∈ centreGroup U (γ c) := by
  intro u
  have h1 := he (γ⁻¹ u)
  have e1 : (γ * e * γ⁻¹) u - u = γ (e (γ⁻¹ u) - γ⁻¹ u) := by
    rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    congr 1
    exact (LinearEquiv.apply_symm_apply γ u).symm
  rw [e1]
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp h1
  rw [← hk, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem eq_one_of_mem_centreGroup {c c' : U} (hcc : c ≠ c')
    {e : U ≃ₗ[ZMod 2] U} (he : e ∈ centreGroup U c) (he' : e ∈ centreGroup U c') : e = 1 := by
  refine LinearEquiv.ext fun u => ?_
  have h1 := OrthoF2.mem_span_singleton_iff.mp (he u)
  have h2 := OrthoF2.mem_span_singleton_iff.mp (he' u)
  have h0 : e u - u = 0 := by
    rcases h1 with h1 | h1
    · exact h1
    · rcases h2 with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hcc
  exact sub_eq_zero.mp h0

end Centre

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem Ebar_le_Nbar_of_linCase (hCE : CentralExtInput.{u}) {τ : S.O}
    (hτ : τ ∈ S.Lbar g ⊓ Xb) (hL : LinCase S g hτ.1) : S.Lbar g ⊓ Xb ≤ Nbar S g τ := by
  obtain ⟨k, hkY', -, hne, -, -⟩ := D.exists_d hCE
  have hkY := ((D.dec.mem_commutator_iff).mp hkY').1
  have hkR := D.Yb_le_Rbar hτ hkY
  intro x hx
  have hxR := Lbar_le_Rbar hτ.1 hx.1
  set rx := resV X.haQ τ ⟨x, hxR⟩ with hrx
  set rd := resV X.haQ τ ⟨S.ρ k, hkR⟩ with hrd
  have h1 : rx ∈ centreGroup (Vt S g τ) (aV hτ.1) := by
    rw [← hL.LmodN_eq]
    exact ⟨x, hx.1, fun v => rfl⟩
  have hcomm : rx = rd * rx * rd⁻¹ := by
    have e : (⟨S.ρ k, hkR⟩ : Rbar S g τ) * ⟨x, hxR⟩ * (⟨S.ρ k, hkR⟩)⁻¹ = ⟨x, hxR⟩ := by
      refine Subtype.ext ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← D.dec.comm x hx.2 _ hkY]
      group
    rw [hrx, hrd, ← map_inv, ← map_mul, ← map_mul, e]
  have h2 : rx ∈ centreGroup (Vt S g τ) (rd (aV hτ.1)) := by
    rw [hcomm]
    exact conj_mem_centreGroup h1 rd
  have hrdv : ((rd (aV hτ.1) : Vt S g τ) : S.Qt) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
    rw [hrd, coe_resV_apply]
    exact ρ_cl_conj_z S k X.haQ
  have hneq : aV hτ.1 ≠ rd (aV hτ.1) := fun h => hne (by rw [← hrdv, ← h]; rfl)
  have hone := eq_one_of_mem_centreGroup hneq h1 h2
  exact (resV_eq_one_iff X.haQ ⟨x, hxR⟩).mp hone

theorem finrank_Vt_of_linCase (hCE : CentralExtInput.{u}) {τ : S.O}
    (hτ : τ ∈ S.Lbar g ⊓ Xb) (hL : LinCase S g hτ.1) : finrank (ZMod 2) (Vt S g τ) = 2 := by
  have hle : S.Lbar g ⊓ Xb ≤ S.Lbar g ⊓ Nbar S g τ :=
    le_inf inf_le_left (D.Ebar_le_Nbar_of_linCase hCE hτ hL)
  have h1 := Subgroup.card_le_of_le hle
  have h2 := D.two_mul_card_Ebar hCE
  have h3 := card_Lbar_eq_mul X.haQ hτ.1
  rw [hL.LmodN_eq, card_centreGroup (aV_ne_zero X.H hτ.1)] at h3
  have hpos : 0 < Nat.card (S.Lbar g ⊓ Nbar S g τ : Subgroup S.O) := Nat.card_pos
  have h4 : 2 ^ (finrank (ZMod 2) (Vt S g τ) - 1) ≤ 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have h5 := hL.two_le_finrank
  by_contra hne
  have h6 : 2 ≤ finrank (ZMod 2) (Vt S g τ) - 1 := by omega
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h6
  omega

theorem Rbar_eq_of_linCase (hCE : CentralExtInput.{u}) {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb)
    (hL : LinCase S g hτ.1) : Rbar S g τ = (S.Lbar g ⊓ Xb) ⊔ Yb := by
  refine le_antisymm ?_ (D.sup_le_Rbar hτ)
  obtain ⟨k, hkY', -, hne, -, hsum⟩ := D.exists_d hCE
  have hkY := ((D.dec.mem_commutator_iff).mp hkY').1
  have hkkY : S.ρ (k * k) ∈ Yb := by rw [map_mul]; exact mul_mem hkY hkY
  have hdim := D.finrank_Vt_of_linCase hCE hτ hL
  set a := S.cl (g * S.z * g⁻¹) with ha
  set α := S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) with hα
  have ha0 : a ≠ 0 := cl_conj_z_ne_zero S X.haQ X.H.conj_ne
  have hα0 : α ≠ 0 := cl_conj_z_ne_zero S (conj_mem_QG' S k.2 X.haQ) (conj_ne_z' S k.2 X.H.conj_ne)
  have hli : LinearIndependent (ZMod 2) ![a, α] :=
    OrthoF2.linearIndependent_pair_iff.mpr ⟨ha0, hα0, Ne.symm hne⟩
  have hspan : Submodule.span (ZMod 2) {a, α} ≤ Vt S g τ := by
    rw [Submodule.span_le]
    rintro v (rfl | rfl)
    · exact cl_a_mem_Vt hτ.1
    · exact cl_mem_Vt (D.mem_Lbar_mul hτ hkY)
  have heq : Submodule.span (ZMod 2) {a, α} = Vt S g τ :=
    Submodule.eq_of_le_of_finrank_eq hspan (by rw [OrthoF2.finrank_span_pair hli, hdim])
  refine sSup_le fun Z hZ => ?_
  obtain ⟨h, rfl, hτZ⟩ := hZ
  have hc := cl_mem_Vt hτZ
  rw [← heq, Submodule.mem_span_pair] at hc
  obtain ⟨c₁, c₂, hc⟩ := hc
  have hcQ := conj_mem_QG' S h.2 X.haQ
  have hc0 := cl_conj_z_ne_zero S hcQ (conj_ne_z' S h.2 X.H.conj_ne)
  rcases OrthoF2.zmod2_eq_zero_or_eq_one c₁ with rfl | rfl <;>
    rcases OrthoF2.zmod2_eq_zero_or_eq_one c₂ with rfl | rfl
  · exact absurd (by rw [← hc]; simp) hc0
  · rw [zero_smul, zero_add, one_smul] at hc
    rw [Lbar_eq_of_cl_eq S (conj_mem_QG' S k.2 X.haQ) (conj_ne_z' S k.2 X.H.conj_ne) hcQ
      hc.symm]
    exact D.Lbar_mul_le_sup hCE hkY
  · rw [one_smul, zero_smul, add_zero] at hc
    rw [Lbar_eq_of_cl_eq S X.haQ X.H.conj_ne hcQ hc.symm]
    exact D.Lbar_le_sup hCE
  · rw [one_smul, one_smul, hsum] at hc
    rw [Lbar_eq_of_cl_eq S (conj_mem_QG' S (k * k).2 X.haQ) (conj_ne_z' S (k * k).2 X.H.conj_ne)
      hcQ hc.symm]
    exact D.Lbar_mul_le_sup hCE hkkY

end Dec108

end CFSG.LargeExtraspecial.S10
