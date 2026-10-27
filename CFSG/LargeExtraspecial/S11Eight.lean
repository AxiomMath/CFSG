module

public import CFSG.LargeExtraspecial.S11EightD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

theorem exists_mem_not_mem_span {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {W : Submodule (ZMod 2) V} (hW : 2 ≤ finrank (ZMod 2) W) (a : V) :
    ∃ v ∈ W, v ∉ (ZMod 2) ∙ a := by
  by_contra h
  push Not at h
  have h1 := Submodule.finrank_mono (show W ≤ (ZMod 2) ∙ a from fun v hv => h v hv)
  have h2 := finrank_span_singleton_le_one a
  omega

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

variable (hy : Hyp S g) (K : Conf S g t τ u)
include hy K

theorem Conf.false_of_forall_not_mem (hCE : CentralExtInput.{u_G}) (hn : 6 ≤ S.width)
    {h' : G} (hh' : h' ∈ S.Qa u) (hyQ : h' * S.z * h'⁻¹ ∉ S.QG) {k₁ k₂ : G}
    (hk₁ : k₁ * S.z * k₁⁻¹ ∈ S.QG ⊓ S.Qa u ⊓ S.Qa h')
    (hk₂ : k₂ * S.z * k₂⁻¹ ∈ S.QG ⊓ S.Qa u ⊓ S.Qa h')
    (hks : S.cl (k₂ * S.z * k₂⁻¹) ∉ (ZMod 2) ∙ S.cl (k₁ * S.z * k₁⁻¹)) {α₀ : G}
    (hα₀ : α₀ ∈ S.QG ⊓ S.Qa u) (hα₀h : h' * α₀ ≠ α₀ * h')
    (hcase : ∀ α ∈ S.QG ⊓ S.Qa u, h' * α ≠ α * h' → ∀ w ∈ Wt S g t,
      (S.ρ ⟨h' * S.z * h'⁻¹, K.conj_mem_M hh' hy⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ≠ S.cl α) :
    False := by
  set y := h' * S.z * h'⁻¹ with hydef
  have hyM : y ∈ S.M := K.conj_mem_M hh' hy
  set yb := S.ρ ⟨y, hyM⟩ with hyb
  have hk₁E : k₁ * S.z * k₁⁻¹ ∈ S.QG ⊓ S.Qa u := (mem_inf.mp hk₁).1
  have hk₂E : k₂ * S.z * k₂⁻¹ ∈ S.QG ⊓ S.Qa u := (mem_inf.mp hk₂).1
  have hybN : yb ∈ Nbar S g t := K.rho_conj_mem_Nbar hh' hy hyQ hk₁
  have hyk : ∀ {k : G}, k * S.z * k⁻¹ ∈ S.QG → k * S.z * k⁻¹ ∈ S.Qa h' → y ∈ S.Qa k :=
    fun hkQ hkh => S.mem_Qa_symm (fun h => hyQ (by rw [hydef, ← h]; exact hkQ)) hkh
  have hWV : ∀ w ∈ Wt S g t, (yb : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
    set W := (Vt S g t).comap (((yb : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)
      with hW
    have hmem : ∀ v, v ∈ W ↔ (yb : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t := fun v => by
      rw [hW, Submodule.mem_comap, LinearMap.sub_apply]
      rfl
    intro w hw
    refine (hmem w).mp (K.Wt_le hy hCE (fun v hv => (hmem v).mpr ?_)
      (fun k hk v hv => (hmem v).mpr ?_) hw)
    · exact K.apply_sub_mem_Vt_of_mem_fixSpace hy hCE hn hybN hv
    · by_cases hkh : h' * (k * S.z * k⁻¹) = k * S.z * k⁻¹ * h'
      · have h1 := Lbar_apply_sub_mem_span' hk.1 hv
          (S.ρ_mem_Lbar ⟨hyk hk.1 ((K.mem_Qa_conj_iff hh' hk).mpr hkh), hyM⟩)
        refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_ h1
        rw [← K.timmesfeld_11_3 hy]
        exact S.cl_mem_clSub hk hk.1
      · by_contra hnot
        have hvP : (yb : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ S.clSub (S.QG ⊓ S.Qa k) := by
          refine sub_mem ?_ hv
          obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
          rw [hyb, S.ρ_cl _ hxQ]
          refine S.cl_mem_clSub (mem_inf.mpr ⟨S.conj_mem_QG hyM hxQ, ?_⟩)
            (S.conj_mem_QG hyM hxQ)
          exact conj_mem_Qa_of_commute' (mem_inf.mp hx).2 (K.conj_commute_of_mem hh' hk)
        obtain ⟨w, hw, hwe⟩ := K.exists_apply_sub_eq hy hk
          (fun ℓ hℓ => K.rho_conj_commute hh' hy hCE hℓ.2) hv hvP hnot
        exact hcase _ hk hkh w hw hwe
  have hX : (Wt S g t).map (((yb : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) <
      Vt S g t := by
    refine lt_of_le_of_ne ?_ fun heq => ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact hWV w hw
    · have h1 : S.cl α₀ ∈ Vt S g t := by
        rw [← K.timmesfeld_11_3 hy]
        exact S.cl_mem_clSub hα₀ hα₀.1
      rw [← heq] at h1
      obtain ⟨w, hw, hwe⟩ := h1
      exact hcase α₀ hα₀ hα₀h w hw hwe
  have hXdim := Submodule.finrank_lt_finrank_of_lt hX
  have h1 := finrank_commSpace_add_le (yb : S.Qt ≃ₗ[ZMod 2] S.Qt) (Wt S g t)
  have h2 := finrank_Wt (S := S) (g := g) (t := t)
  have hk₁z := (K.base_of_mem hk₁E).1
  have hy₁ := hy.of_conj hk₁E.1 hk₁z
  have hR : Rbar S k₁ yb ≠ S.Lbar k₁ := hy₁.Rbar_ne_of_mem_Lbar hk₂E.1
    (K.base_of_mem hk₂E).1 (S.ρ_mem_Lbar ⟨hyk hk₂E.1 (mem_inf.mp hk₂).2, hyM⟩) hks
  have Ky : Conf S k₁ yb ⟨y, hyM⟩ h' := hy₁.conf rfl hyQ (hyk hk₁E.1 (mem_inf.mp hk₁).2) hR
  have h3 := finrank_commSpace_eq hy₁.hyp4 Ky.mem_Lbar Ky.ne_one
  rw [Ky.timmesfeld_11_7 hy₁ hCE] at h3
  have hdimB := K.finrank_Vt_le hh' hy hα₀ hα₀h
  have hBle : S.clSub (S.QG ⊓ S.Qa u ⊓ S.Qa h') ≤ Vt S k₁ yb := by
    rw [← Ky.timmesfeld_11_3 hy₁]
    exact S.clSub_mono fun x hx =>
      mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hx).1).1, (mem_inf.mp hx).2⟩
  have h4 := Submodule.finrank_mono hBle
  have hBeq : S.clSub (S.QG ⊓ S.Qa u ⊓ S.Qa h') = Vt S k₁ yb :=
    Submodule.eq_of_le_of_finrank_eq hBle (by omega)
  have htN : t ∈ Nbar S k₁ yb := by
    refine mem_Nbar.mpr ⟨Lbar_le_Rbar Ky.mem_Lbar (K.base_of_mem hk₁E).2, fun v hv => ?_⟩
    rw [← hBeq] at hv
    have hvV : v ∈ Vt S g t := by
      rw [← K.timmesfeld_11_3 hy]
      exact S.clSub_mono inf_le_left hv
    exact mem_fixSpace.mp (commSpace_le_fixSpace (coe_mul_self K.mul_self)
      (Vt_le_commSpace hy.hyp4 K.ne_one hvV))
  have htL : ∀ k : G, k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa h' → t ∈ S.Lbar k := by
    intro k hk
    have hcl : S.cl (k * S.z * k⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa u ⊓ S.Qa h') := by
      rw [hBeq, ← Ky.timmesfeld_11_3 hy₁]
      exact S.cl_mem_clSub hk hk.1
    obtain ⟨b, hb, hbQ, hbe⟩ := S.mem_clSub_iff.mp hcl
    rcases (S.cl_eq_cl_iff hbQ hk.1).mp hbe with h | h
    · refine (K.base_of_mem ?_).2
      rw [h]
      exact (mem_inf.mp hb).1
    · exfalso
      have hzh : S.z ∈ S.Qa h' := by
        have := mul_mem (inv_mem (mem_inf.mp hb).2) (mem_inf.mp hk).2
        rwa [h, ← mul_assoc, inv_mul_cancel, one_mul] at this
      have hne : (1 : G) * S.z * (1 : G)⁻¹ ≠ h' * S.z * h'⁻¹ := by
        rw [one_mul, inv_one, mul_one]
        intro e
        exact hyQ (by rw [hydef, ← e]; exact S.z_mem_QG)
      have h5 := S.mem_Qa_symm hne (by rw [one_mul, inv_one, mul_one]; exact hzh)
      rw [S.Qa_one] at h5
      exact hyQ h5
  have h5 : (Wt S k₁ yb).map (((t : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤
      Vt S k₁ yb := by
    rintro _ ⟨w, hw, rfl⟩
    exact Ky.apply_sub_mem_Vt_of_forall hy₁ hCE hn htN htL hw
  have h6 := Submodule.finrank_mono h5
  have h7 := finrank_commSpace_add_le (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (Wt S k₁ yb)
  have h8 := finrank_Wt (S := S) (g := k₁) (t := yb)
  have h9 := finrank_commSpace_eq hy.hyp4 K.mem_Lbar K.ne_one
  rw [K.timmesfeld_11_7 hy hCE] at h9
  omega

theorem Conf.timmesfeld_11_8_of_three_le (hCE : CentralExtInput.{u_G}) (hn : 6 ≤ S.width)
    (hm : 3 ≤ finrank (ZMod 2) (Vt S g t)) :
    finrank (ZMod 2) (Vt S g t) = 3 ∧ S.width = 6 := by
  suffices hw6 : S.width = 6 by
    have h8 := finrank_commSpace_eq hy.hyp4 K.mem_Lbar K.ne_one
    have h9 := Submodule.finrank_mono (Vt_le_Tt hy.hyp4 hy.noA2' K.ne_one K.lin)
    have h10 := K.finrank_commSpace_le
    exact ⟨by omega, hw6⟩
  obtain ⟨h', hh', α₀, hα₀, hα₀h⟩ :
      ∃ h' ∈ S.Qa u, ∃ α₀ ∈ S.QG ⊓ S.Qa u, h' * α₀ ≠ α₀ * h' := by
    obtain ⟨k₀, hk₀, -⟩ := K.exists_base_ne hy
    by_contra hcon
    push Not at hcon
    rcases (S.conjBy u).eq_one_or_z_of_commute (mem_inf.mp hk₀).2
      (fun x hx => (hcon x hx _ hk₀).symm) with h | h
    · exact conj_z_ne_one S k₀ h
    · have h2 : k₀ * S.z * k₀⁻¹ = u * S.z * u⁻¹ := h
      exact K.not_mem_QG (by rw [K.conj_eq, ← h2]; exact (mem_inf.mp hk₀).1)
  have hyQ := K.conj_not_mem_QG hh' hy hCE hα₀ hα₀h
  have hdimB := K.finrank_Vt_le hh' hy hα₀ hα₀h
  obtain ⟨k₁, k₂, hk₁, hk₂, hks⟩ : ∃ k₁ k₂ : G, k₁ * S.z * k₁⁻¹ ∈ S.QG ⊓ S.Qa u ⊓ S.Qa h' ∧
      k₂ * S.z * k₂⁻¹ ∈ S.QG ⊓ S.Qa u ⊓ S.Qa h' ∧
      S.cl (k₂ * S.z * k₂⁻¹) ∉ (ZMod 2) ∙ S.cl (k₁ * S.z * k₁⁻¹) := by
    have hB2 : 2 ≤ finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa u ⊓ S.Qa h')) := by omega
    obtain ⟨v₁, hv₁, hv₁0⟩ := exists_mem_not_mem_span hB2 0
    obtain ⟨v₂, hv₂, hv₂s⟩ := exists_mem_not_mem_span hB2 v₁
    obtain ⟨b₁, hb₁, hb₁Q, rfl⟩ := S.mem_clSub_iff.mp hv₁
    obtain ⟨b₂, hb₂, hb₂Q, rfl⟩ := S.mem_clSub_iff.mp hv₂
    have hb₁1 : b₁ ≠ 1 := fun h => hv₁0 (by rw [h, S.cl_one]; exact zero_mem _)
    have hb₂1 : b₂ ≠ 1 := fun h => hv₂s (by rw [h, S.cl_one]; exact zero_mem _)
    obtain ⟨k₁, hk₁⟩ := K.exists_conj hy (mem_inf.mp hb₁).1 hb₁1
    obtain ⟨k₂, hk₂⟩ := K.exists_conj hy (mem_inf.mp hb₂).1 hb₂1
    exact ⟨k₁, k₂, hk₁ ▸ hb₁, hk₂ ▸ hb₂, by rw [hk₁, hk₂]; exact hv₂s⟩
  have hk12 : k₂ * S.z * k₂⁻¹ ≠ k₁ * S.z * k₁⁻¹ := fun h =>
    hks (by rw [h]; exact Submodule.mem_span_singleton_self _)
  by_cases hcase : ∃ α ∈ S.QG ⊓ S.Qa u, h' * α ≠ α * h' ∧ ∃ w ∈ Wt S g t,
      (S.ρ ⟨h' * S.z * h'⁻¹, K.conj_mem_M hh' hy⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w = S.cl α
  ·
    obtain ⟨α, hα, hαh, w, -, hwα⟩ := hcase
    obtain ⟨q, hqQ, rfl⟩ := S.exists_cl w
    rw [← S.cl_commutator (K.conj_mem_M hh' hy) hqQ] at hwα
    have hcQ : h' * S.z * h'⁻¹ * q * (h' * S.z * h'⁻¹)⁻¹ * q⁻¹ ∈ S.QG :=
      S.QG.mul_mem (S.conj_mem_QG (K.conj_mem_M hh' hy) hqQ) (S.QG.inv_mem hqQ)
    exact K.width_eq_six_of_commutator hy hCE hn hh' hyQ hk₁ hk₂ hk12 hα hαh
      ((S.cl_eq_cl_iff hα.1 hcQ).mp hwα.symm)
  ·
    push Not at hcase
    exact (K.false_of_forall_not_mem hy hCE hn hh' hyQ hk₁ hk₂ hks hα₀ hα₀h hcase).elim

end CFSG.LargeExtraspecial.S11
