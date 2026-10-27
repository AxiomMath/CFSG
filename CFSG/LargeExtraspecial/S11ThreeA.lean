module

public import CFSG.LargeExtraspecial.S11Key
public import CFSG.LargeExtraspecial.S11Gen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem zmod2_add_eq_zero {a b : ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0) : a + b = 0 := by
  rw [zmod2_eq_one_of_ne_zero ha, zmod2_eq_one_of_ne_zero hb]
  rfl

theorem polar_eq_zero_of_sub_mem (hy : Hyp S g) {j : G} (hjQ : j * S.z * j⁻¹ ∈ S.QG)
    (hjz : j * S.z * j⁻¹ ≠ S.z) {t : S.O} (ht : t ∈ S.Lbar j) (ht1 : t ≠ 1) {w : S.Qt}
    (hw : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ S.clSub (S.QG ⊓ S.Qa j)) :
    polar S.q (S.cl (j * S.z * j⁻¹)) w = 0 := by
  set P := S.clSub (S.QG ⊓ S.Qa j) with hP
  set tl := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with htl
  have C := hy.cons_of hjQ hjz
  have htt := mul_self_of_mem_Lbar S hjQ ht
  by_contra hpw
  have hperp : ∀ v, polar S.q (S.cl (j * S.z * j⁻¹)) v = 0 → tl v - v ∈ P := by
    intro v hv
    obtain ⟨x, hxQ, rfl⟩ := S.exists_cl v
    have hxc : x * (j * S.z * j⁻¹) = j * S.z * j⁻¹ * x := by
      rw [polar_comm] at hv
      exact (S.polar_cl_eq_zero_iff hxQ hjQ).mp hv
    exact C.comm_le x ⟨hxQ, mem_centralizer_singleton_iff.mpr hxc⟩ t ht
  have hU : commSpace tl ≤ P := by
    intro v hv
    obtain ⟨v', rfl⟩ := mem_commSpace.mp hv
    by_cases hv' : polar S.q (S.cl (j * S.z * j⁻¹)) v' = 0
    · exact hperp v' hv'
    · have h1 := hperp (v' + w) (by rw [polar_add_right]; exact zmod2_add_eq_zero hv' hpw)
      have e : tl v' - v' = (tl (v' + w) - (v' + w)) - (tl w - w) := by
        rw [map_add]
        abel
      rw [e]
      exact sub_mem h1 hw
  have hPP : LinearMap.BilinForm.orthogonal S.q.polarBilin P = P :=
    orthogonal_clSub_eq hjQ hjz C.card_QG_inf_Qa
  have hfix : P ≤ fixSpace tl := by
    rw [fixSpace_eq_orthogonal_commSpace S.q_nondegenerate t.2 (coe_mul_self htt), ← hPP]
    exact LinearMap.BilinForm.orthogonal_le hU
  exact ht1 (C.faithful t ht fun v hv => mem_fixSpace.mp (hfix hv))

variable {t : S.O} {τ : S.M} {u : G}

theorem Conf.mul_self (K : Conf S g t τ u) : t * t = 1 := by
  have h2 : τ * τ = 1 := by
    apply Subtype.ext
    show (τ : G) * τ = 1
    rw [K.conj_eq]
    exact conj_z_mul_self S u
  rw [← K.rho_eq, ← map_mul, h2, map_one]

theorem finrank_span_singleton_le_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x : V) :
    finrank (ZMod 2) ((ZMod 2) ∙ x) ≤ 1 := by
  by_cases hx : x = 0
  · rw [hx, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
    omega
  · rw [finrank_span_singleton hx]

theorem Conf.q_eq_zero (hy : Hyp S g) (K : Conf S g t τ u) {v : S.Qt}
    (hv : v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.q v = 0 :=
  (isTypeA_of_linCase hy.hyp4 K.ne_one K.lin).2.2.2.2 v hv

theorem Conf.polar_eq_zero (K : Conf S g t τ u) {v w : S.Qt}
    (hv : v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hw : w ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : polar S.q v w = 0 := by
  have h1 : w ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    commSpace_le_fixSpace (coe_mul_self K.mul_self) hw
  rw [fixSpace_eq_orthogonal_commSpace S.q_nondegenerate t.2 (coe_mul_self K.mul_self)] at h1
  exact (LinearMap.BilinForm.mem_orthogonal_iff.mp h1) v hv

theorem Conf.exists_coimage (hy : Hyp S g) (K : Conf S g t τ u) {v : S.Qt}
    (hv : v ∈ Vt S g t) (hv0 : v ≠ 0) :
    ∃ b k : G, b ∈ S.QG ⊓ S.Qa u ∧ k * S.z * k⁻¹ = b ∧ S.cl b = v := by
  obtain ⟨b, hbE, hbQ, hbv⟩ := S.mem_clSub_iff.mp (K.Vt_le hy hv)
  have hbV : b ∈ V S g t := S.mem_clPre.mpr ⟨hbQ, hbv ▸ hv⟩
  have hb1 : b ≠ 1 := fun h => hv0 (by rw [← hbv, h, S.cl_one])
  obtain ⟨k, hk⟩ := exists_conj_eq_of_mem_V hy.hyp4 K.lin hbV hb1
  exact ⟨b, k, hbE, hk, hbv⟩

theorem Conf.base_of_mem (K : Conf S g t τ u) {k : G}
    (hb : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u) :
    k * S.z * k⁻¹ ≠ S.z ∧ t ∈ S.Lbar k := by
  refine ⟨fun h => K.z_not_mem (h ▸ hb.2), ?_⟩
  have hne : k * S.z * k⁻¹ ≠ u * S.z * u⁻¹ := by
    rw [← K.conj_eq]
    intro h
    exact K.not_mem_QG (h ▸ hb.1)
  have hτk : (τ : G) ∈ S.Qa k := by
    rw [K.conj_eq]
    exact S.mem_Qa_symm hne hb.2
  rw [← K.rho_eq]
  exact S.ρ_mem_Lbar ⟨hτk, τ.2⟩

theorem Conf.mem_Tt_of_forall (hy : Hyp S g) (K : Conf S g t τ u) {v : S.Qt}
    (hv : v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (h : ∀ k : G, k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u → S.cl (k * S.z * k⁻¹) ∈ Vt S g t →
      v ∈ S.clSub (S.QG ⊓ S.Qa k)) : v ∈ Tt S g t := by
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  refine sub_mem_Tt (mem_Wt.mpr fun v' hv' => ?_)
  by_cases hv0 : v' = 0
  · rw [hv0, polar_zero_left]
  obtain ⟨b, k, hbE, hk, rfl⟩ := K.exists_coimage hy hv' hv0
  subst hk
  obtain ⟨hkz, htk⟩ := K.base_of_mem hbE
  exact polar_eq_zero_of_sub_mem hy hbE.1 hkz htk K.ne_one (h k hbE hv')

theorem Conf.inf_commSpace_le_Tt (hy : Hyp S g) (K : Conf S g t τ u) :
    S.clSub (S.QG ⊓ S.Qa u) ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Tt S g t := by
  rintro v ⟨hvE, hvU⟩
  obtain ⟨α, hα, hαQ, rfl⟩ := S.mem_clSub_iff.mp hvE
  refine K.mem_Tt_of_forall hy hvU fun k hb _ => ?_
  obtain ⟨hkz, -⟩ := K.base_of_mem hb
  have hτQ : u * S.z * u⁻¹ ∉ S.QG := K.conj_eq ▸ K.not_mem_QG
  have hne : u * S.z * u⁻¹ ≠ S.z := fun h => hτQ (by rw [h]; exact S.z_mem_QG)
  have hαb := S.QG_inf_Qa_comm hne hα hb
  exact S.cl_mem_clSub ⟨hαQ, hy.mem_Qa_of_commute hb.1 hkz hτQ hb.2 hα hαb⟩ hαQ

theorem polar_sub_apply_comm {t : S.O} (htt : t * t = 1) (w w' : S.Qt) :
    polar S.q ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w' - w') w =
      polar S.q w' ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by
  have h1 : polar S.q ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w') w =
      polar S.q w' ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
    have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup t.2 w'
      ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w)
    rwa [apply_apply_of_mul_self (coe_mul_self htt)] at this
  rw [polar_sub_left, polar_sub_right, h1]

theorem Conf.exists_orth_of_mem_Tt (hy : Hyp S g) (K : Conf S g t τ u) {α' v : S.Qt}
    (hα : α' ∈ Tt S g t) (hv : v ∈ Vt S g t) :
    ∃ w, polar S.q α' w = 0 ∧ (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w = v := by
  obtain ⟨w, rfl⟩ :=
    mem_commSpace.mp (Tt_le_commSpace (Vt_le_Tt hy.hyp4 hy.noA2' K.ne_one K.lin hv))
  refine ⟨w, ?_, rfl⟩
  obtain ⟨w', hw', rfl⟩ := mem_Tt.mp hα
  rw [polar_sub_apply_comm K.mul_self, polar_comm]
  exact mem_Wt.mp hw' _ hv

theorem exists_orth_of_not_mem_commSpace {t : S.O} (htt : t * t = 1) {α' v : S.Qt}
    (hα : α' ∉ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hv : v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    ∃ w, polar S.q α' w = 0 ∧ (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w = v := by
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  by_cases h : polar S.q α' w = 0
  · exact ⟨w, h, rfl⟩
  rw [← orthogonal_fixSpace htt, LinearMap.BilinForm.mem_orthogonal_iff] at hα
  push Not at hα
  obtain ⟨f, hf, hfα⟩ := hα
  have hfα' : polar S.q α' f ≠ 0 := by
    rw [polar_comm]
    exact hfα
  refine ⟨w + f, ?_, ?_⟩
  · rw [polar_add_right]
    exact zmod2_add_eq_zero h hfα'
  · rw [map_add, mem_fixSpace.mp hf]
    abel

theorem Conf.exists_sub_not_mem_Tt (hy : Hyp S g) (K : Conf S g t τ u) {α' : S.Qt}
    (hα0 : α' ≠ 0) :
    ∃ w, polar S.q α' w = 0 ∧ (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∉ Tt S g t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, polar S.q α' w₁ ≠ 0 := by
    by_contra h
    push Not at h
    exact hα0 (S.q_nondegenerate.1 α' fun y => by rw [polarBilin_apply_apply]; exact h y)
  have hle : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      Tt S g t ⊔ (ZMod 2) ∙ ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁ - w₁) := by
    intro v hv
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    by_cases h : polar S.q α' w = 0
    · exact Submodule.mem_sup_left (hcon w h)
    · have h1 := hcon (w + w₁) (by rw [polar_add_right]; exact zmod2_add_eq_zero h hw₁)
      have e : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
          ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) (w + w₁) - (w + w₁)) -
            ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁ - w₁) := by
        rw [map_add]
        abel
      rw [e]
      exact sub_mem (Submodule.mem_sup_left h1)
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (Tt S g t)
    ((ZMod 2) ∙ ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁ - w₁))
  have h3 := finrank_span_singleton_le_one ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w₁ - w₁)
  have h4 := finrank_commSpace_eq hy.hyp4 K.mem_Lbar K.ne_one
  have h5 := K.lin.two_le_finrank
  omega

end CFSG.LargeExtraspecial.S11
