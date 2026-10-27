module

public import CFSG.LargeExtraspecial.S11ThreeA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

omit [Finite G] in
theorem inv_mul_conj_z (w k : G) :
    (w⁻¹ * k) * S.z * (w⁻¹ * k)⁻¹ = w⁻¹ * (k * S.z * k⁻¹) * w := by group

omit [Finite G] in
theorem conj_mem_Qa_inv_mul {w k x : G} (hx : x ∈ S.Qa k) : w⁻¹ * x * w ∈ S.Qa (w⁻¹ * k) := by
  have := conj_mem_Qa_mul S (h := w⁻¹) hx
  simpa using this

theorem Hyp.conf_conj (hy : Hyp S g) {w σ g₁ u₁ d₁ : G}
    (hσc : σ * (w * S.z * w⁻¹) = w * S.z * w⁻¹ * σ) (hσQ : σ ∉ S.Qa w)
    (hσu : σ = u₁ * S.z * u₁⁻¹) (hb : g₁ * S.z * g₁⁻¹ ∈ S.Qa w)
    (hbc : g₁ * S.z * g₁⁻¹ ≠ w * S.z * w⁻¹) (hσb : σ ∈ S.Qa g₁)
    (hd : d₁ * S.z * d₁⁻¹ ∈ S.Qa w) (hdb : d₁ * S.z * d₁⁻¹ ≠ g₁ * S.z * g₁⁻¹)
    (hdbc : d₁ * S.z * d₁⁻¹ ≠ g₁ * S.z * g₁⁻¹ * (w * S.z * w⁻¹)) (hσd : σ ∈ S.Qa d₁) :
    ∃ hM : w⁻¹ * σ * w ∈ S.M,
      Conf S (w⁻¹ * g₁) (S.ρ ⟨w⁻¹ * σ * w, hM⟩) ⟨w⁻¹ * σ * w, hM⟩ (w⁻¹ * u₁) := by
  have hM : w⁻¹ * σ * w ∈ S.M := by
    rw [S.mem_M_iff]
    calc w⁻¹ * σ * w * S.z = w⁻¹ * (σ * (w * S.z * w⁻¹)) * w := by group
      _ = w⁻¹ * (w * S.z * w⁻¹ * σ) * w := by rw [hσc]
      _ = S.z * (w⁻¹ * σ * w) := by group
  refine ⟨hM, ?_⟩
  have hb'Q : (w⁻¹ * g₁) * S.z * (w⁻¹ * g₁)⁻¹ ∈ S.QG := by
    rw [inv_mul_conj_z]
    exact (S11.mem_Qa_iff S w _).mp hb
  have hconj_inj : ∀ x y : G, w⁻¹ * x * w = w⁻¹ * y * w → x = y := fun x y h => by
    have := congrArg (fun v => w * v * w⁻¹) h
    simpa [mul_assoc] using this
  have hb'z : (w⁻¹ * g₁) * S.z * (w⁻¹ * g₁)⁻¹ ≠ S.z := by
    rw [inv_mul_conj_z]
    intro h
    apply hbc
    exact hconj_inj _ _ (h.trans (by group))
  have hy' := hy.of_conj hb'Q hb'z
  have hτ' : w⁻¹ * σ * w ∈ S.Qa (w⁻¹ * g₁) := conj_mem_Qa_inv_mul hσb
  have ht : S.ρ ⟨w⁻¹ * σ * w, hM⟩ ∈ S.Lbar (w⁻¹ * g₁) := S.ρ_mem_Lbar ⟨hτ', hM⟩
  have ht1 : S.ρ ⟨w⁻¹ * σ * w, hM⟩ ≠ 1 := by
    intro h
    apply hσQ
    have h1 := (S.ρ_eq_one_iff _).mp h
    rw [S11.mem_Qa_iff S w σ]
    exact h1
  have hd'Q : (w⁻¹ * d₁) * S.z * (w⁻¹ * d₁)⁻¹ ∈ S.QG := by
    rw [inv_mul_conj_z]
    exact (S11.mem_Qa_iff S w _).mp hd
  have hd'z : (w⁻¹ * d₁) * S.z * (w⁻¹ * d₁)⁻¹ ≠ S.z := by
    rw [inv_mul_conj_z]
    intro h
    have h2 : d₁ * S.z * d₁⁻¹ = w * S.z * w⁻¹ := hconj_inj _ _ (h.trans (by group))
    exact hσQ (by rw [← S.Qa_eq_of_conj_eq h2]; exact hσd)
  obtain ⟨m, hm, hmd⟩ := hy'.fusion (w⁻¹ * d₁) hd'Q hd'z
  have hc : ((⟨m, hm⟩ : S.M) : G) * (w⁻¹ * g₁) * S.z * (((⟨m, hm⟩ : S.M) : G) * (w⁻¹ * g₁))⁻¹ =
      (w⁻¹ * d₁) * S.z * (w⁻¹ * d₁)⁻¹ := by
    rw [mul_conj_z S]
    exact hmd
  have htm : S.ρ ⟨w⁻¹ * σ * w, hM⟩ ∈ S.Lbar (((⟨m, hm⟩ : S.M) : G) * (w⁻¹ * g₁)) := by
    rw [S.Lbar_eq_of_conj_eq hc]
    exact S.ρ_mem_Lbar ⟨conj_mem_Qa_inv_mul hσd, hM⟩
  have hdV := cl_mem_Vt htm
  rw [hc] at hdV
  have hR : Rbar S (w⁻¹ * g₁) (S.ρ ⟨w⁻¹ * σ * w, hM⟩) ≠ S.Lbar (w⁻¹ * g₁) := by
    intro hR
    have h1 := Vt_le_span_of_Rbar_eq hy'.hyp4 hy'.cons hR hdV
    rcases mem_span_cl_iff.mp h1 with h0 | h0
    · rcases (S.cl_eq_zero_iff hd'Q).mp h0 with h2 | h2
      · exact conj_z_ne_one S _ h2
      · exact hd'z h2
    · rcases (S.cl_eq_cl_iff hb'Q hd'Q).mp h0.symm with h2 | h2
      · apply hdb
        rw [inv_mul_conj_z, inv_mul_conj_z] at h2
        exact hconj_inj _ _ h2
      · apply hdbc
        rw [inv_mul_conj_z, inv_mul_conj_z] at h2
        apply hconj_inj
        rw [h2]
        group
  refine ⟨ht, ht1, (hy'.lin ht ht1).resolve_left hR, rfl, ?_, ?_⟩
  · change w⁻¹ * σ * w = (w⁻¹ * u₁) * S.z * (w⁻¹ * u₁)⁻¹
    rw [hσu]
    group
  · rw [inv_mul_conj_z]
    apply conj_mem_Qa_inv_mul
    have hne : σ ≠ g₁ * S.z * g₁⁻¹ := fun h => hσQ (h ▸ hb)
    rw [hσu] at hσb hne
    exact S.mem_Qa_symm hne hσb

variable {t : S.O} {τ : S.M} {u : G}

theorem Conf.exists_base_ne (hy : Hyp S g) (K : Conf S g t τ u) :
    ∃ k : G, k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u ∧
      S.cl (k * S.z * k⁻¹) ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  obtain ⟨v, hv, hvs⟩ : ∃ v ∈ Vt S g t, v ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    by_contra h
    push Not at h
    have h3 := Submodule.finrank_mono (show Vt S g t ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)
      from fun v hv => h v hv)
    have h4 := finrank_span_singleton_le_one (S.cl (g * S.z * g⁻¹))
    have h5 := K.lin.two_le_finrank
    omega
  have hv0 : v ≠ 0 := fun h => hvs (h ▸ zero_mem _)
  obtain ⟨b, k, hbE, hk, hbv⟩ := K.exists_coimage hy hv hv0
  subst hk
  exact ⟨k, hbE, hbv ▸ hvs⟩

theorem Conf.dual (hy : Hyp S g) (K : Conf S g t τ u) :
    ∃ hM : u⁻¹ * S.z * u ∈ S.M,
      Conf S (u⁻¹ * g) (S.ρ ⟨u⁻¹ * S.z * u, hM⟩) ⟨u⁻¹ * S.z * u, hM⟩ u⁻¹ := by
  obtain ⟨k, hkE, hks⟩ := K.exists_base_ne hy
  have hτQ : u * S.z * u⁻¹ ∉ S.QG := K.conj_eq ▸ K.not_mem_QG
  have hσc : S.z * (u * S.z * u⁻¹) = u * S.z * u⁻¹ * S.z := by
    rw [← K.conj_eq]
    exact (S.z_comm τ.2).symm
  have hbc : g * S.z * g⁻¹ ≠ u * S.z * u⁻¹ := fun h => hτQ (h ▸ hy.hyp4.conj_mem)
  have hdb : k * S.z * k⁻¹ ≠ g * S.z * g⁻¹ := fun h => hks (by
    rw [h]
    exact Submodule.mem_span_singleton_self _)
  have hdbc : k * S.z * k⁻¹ ≠ g * S.z * g⁻¹ * (u * S.z * u⁻¹) := by
    intro h
    apply hτQ
    have := mul_mem (inv_mem hy.hyp4.conj_mem) (h ▸ hkE.1)
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  have hkz : k * S.z * k⁻¹ ≠ S.z := fun h => K.z_not_mem (h ▸ hkE.2)
  obtain ⟨hM, K'⟩ := hy.conf_conj (w := u) (σ := S.z) (g₁ := g) (u₁ := 1) (d₁ := k) hσc
    K.z_not_mem (by group) K.mem_Qa hbc (S.z_mem_Qa hy.hyp4.conj_mem hy.hyp4.conj_ne)
    hkE.2 hdb hdbc (S.z_mem_Qa hkE.1 hkz)
  rw [mul_one] at K'
  exact ⟨hM, K'⟩

theorem Conf.mul_z (hy : Hyp S g) (K : Conf S g t τ u) {k : G}
    (hk : k * S.z * k⁻¹ = (τ : G) * S.z) :
    Conf S g t ⟨(τ : G) * S.z, S.M.mul_mem τ.2 S.z_mem_M⟩ k := by
  have hρ : S.ρ ⟨(τ : G) * S.z, S.M.mul_mem τ.2 S.z_mem_M⟩ = t := by
    rw [show (⟨(τ : G) * S.z, S.M.mul_mem τ.2 S.z_mem_M⟩ : S.M) = τ * S.zM from rfl, map_mul,
      (S.ρ_eq_one_iff S.zM).mpr S.z_mem_QG, mul_one, K.rho_eq]
  refine ⟨K.mem_Lbar, K.ne_one, K.lin, hρ, hk.symm, ?_⟩
  have hτa : (τ : G) ∈ S.Qa g := by
    have hne : g * S.z * g⁻¹ ≠ u * S.z * u⁻¹ := by
      rw [← K.conj_eq]
      intro h
      exact K.not_mem_QG (h ▸ hy.hyp4.conj_mem)
    rw [K.conj_eq]
    exact S.mem_Qa_symm hne K.mem_Qa
  have hτz : (τ : G) * S.z ∈ S.Qa g :=
    mul_mem hτa (S.z_mem_Qa hy.hyp4.conj_mem hy.hyp4.conj_ne)
  have hne : k * S.z * k⁻¹ ≠ g * S.z * g⁻¹ := by
    rw [hk]
    intro h
    apply K.not_mem_QG
    have := mul_mem (h ▸ hy.hyp4.conj_mem) S.z_mem_QG
    rwa [mul_assoc, S.z_mul_z, mul_one] at this
  exact S.mem_Qa_symm hne (hk ▸ hτz)

end CFSG.LargeExtraspecial.S11
