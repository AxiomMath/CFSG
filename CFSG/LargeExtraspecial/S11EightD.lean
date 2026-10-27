module

public import CFSG.LargeExtraspecial.S11EightC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

theorem finrank_commSpace_add_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (e : V ≃ₗ[ZMod 2] V) (W : Submodule (ZMod 2) V) :
    finrank (ZMod 2) (commSpace e) + finrank (ZMod 2) W ≤
      finrank (ZMod 2) (W.map ((e : V →ₗ[ZMod 2] V) - 1)) + finrank (ZMod 2) V := by
  have h1 := finrank_commSpace_add_finrank_fixSpace e
  have h2 := S2.finrank_map_sub_one_add e W
  have h3 := Submodule.finrank_mono (inf_le_right : W ⊓ fixSpace e ≤ fixSpace e)
  omega

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

theorem Hyp.width_eq_six_of_conj (hy : Hyp S g) (hCE : CentralExtInput.{u_G})
    (hn : 6 ≤ S.width) {w σ g₁ u₁ d₁ x : G}
    (hσc : σ * (w * S.z * w⁻¹) = w * S.z * w⁻¹ * σ) (hσQ : σ ∉ S.Qa w)
    (hσu : σ = u₁ * S.z * u₁⁻¹) (hb : g₁ * S.z * g₁⁻¹ ∈ S.Qa w)
    (hbc : g₁ * S.z * g₁⁻¹ ≠ w * S.z * w⁻¹) (hσb : σ ∈ S.Qa g₁)
    (hd : d₁ * S.z * d₁⁻¹ ∈ S.Qa w) (hdb : d₁ * S.z * d₁⁻¹ ≠ g₁ * S.z * g₁⁻¹)
    (hdbc : d₁ * S.z * d₁⁻¹ ≠ g₁ * S.z * g₁⁻¹ * (w * S.z * w⁻¹)) (hσd : σ ∈ S.Qa d₁)
    (hx : x * σ * x⁻¹ = σ * (w * S.z * w⁻¹)) : S.width = 6 := by
  obtain ⟨hM, K'⟩ := hy.conf_conj hσc hσQ hσu hb hbc hσb hd hdb hdbc hσd
  have hb'Q : (w⁻¹ * g₁) * S.z * (w⁻¹ * g₁)⁻¹ ∈ S.QG := by
    rw [inv_mul_conj_z]
    exact (S11.mem_Qa_iff S w _).mp hb
  have hb'z : (w⁻¹ * g₁) * S.z * (w⁻¹ * g₁)⁻¹ ≠ S.z := by
    rw [inv_mul_conj_z]
    intro h
    apply hbc
    calc g₁ * S.z * g₁⁻¹ = w * (w⁻¹ * (g₁ * S.z * g₁⁻¹) * w) * w⁻¹ := by group
      _ = w * S.z * w⁻¹ := by rw [h]
  refine (K'.timmesfeld_11_6 (hy.of_conj hb'Q hb'z) hCE hn (x := w⁻¹ * x * w) ?_).2
  change w⁻¹ * x * w * (w⁻¹ * σ * w) * (w⁻¹ * x * w)⁻¹ = w⁻¹ * σ * w * S.z
  calc w⁻¹ * x * w * (w⁻¹ * σ * w) * (w⁻¹ * x * w)⁻¹ = w⁻¹ * (x * σ * x⁻¹) * w := by group
    _ = w⁻¹ * (σ * (w * S.z * w⁻¹)) * w := by rw [hx]
    _ = w⁻¹ * σ * w * S.z := by group

variable (hy : Hyp S g) (K : Conf S g t τ u)
include hy K

theorem Conf.mem_Qa_of_mem_E {k : G} (hk : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u) {b : G}
    (hb : b ∈ S.QG ⊓ S.Qa u) : b ∈ S.Qa k := by
  have hτQ : u * S.z * u⁻¹ ∉ S.QG := K.conj_eq ▸ K.not_mem_QG
  have hne : u * S.z * u⁻¹ ≠ S.z := fun h => hτQ (by rw [h]; exact S.z_mem_QG)
  exact hy.mem_Qa_of_commute hk.1 (K.base_of_mem hk).1 hτQ hk.2 hb (S.QG_inf_Qa_comm hne hb hk)

theorem Conf.width_eq_six_of_commutator (hCE : CentralExtInput.{u_G}) (hn : 6 ≤ S.width)
    {h' : G} (hh' : h' ∈ S.Qa u) (hyQ : h' * S.z * h'⁻¹ ∉ S.QG) {k₁ k₂ : G}
    (hk₁ : k₁ * S.z * k₁⁻¹ ∈ S.QG ⊓ S.Qa u ⊓ S.Qa h')
    (hk₂ : k₂ * S.z * k₂⁻¹ ∈ S.QG ⊓ S.Qa u ⊓ S.Qa h')
    (hk12 : k₂ * S.z * k₂⁻¹ ≠ k₁ * S.z * k₁⁻¹) {α : G} (hα : α ∈ S.QG ⊓ S.Qa u)
    (hαh : h' * α ≠ α * h') {q : G}
    (hqy : h' * S.z * h'⁻¹ * q * (h' * S.z * h'⁻¹)⁻¹ * q⁻¹ = α ∨
      h' * S.z * h'⁻¹ * q * (h' * S.z * h'⁻¹)⁻¹ * q⁻¹ = α * S.z) :
    S.width = 6 := by
  set y := h' * S.z * h'⁻¹ with hydef
  have hyM : y ∈ S.M := K.conj_mem_M hh' hy
  have hyz : y * S.z = S.z * y := S.mem_M_iff.mp hyM
  have hk₁E : k₁ * S.z * k₁⁻¹ ∈ S.QG ⊓ S.Qa u := (mem_inf.mp hk₁).1
  have hk₂E : k₂ * S.z * k₂⁻¹ ∈ S.QG ⊓ S.Qa u := (mem_inf.mp hk₂).1
  have hyk₁ : y ∈ S.Qa k₁ := S.mem_Qa_symm (fun h => hyQ (by rw [hydef, ← h]; exact hk₁E.1))
    (mem_inf.mp hk₁).2
  have hyk₂ : y ∈ S.Qa k₂ := S.mem_Qa_symm (fun h => hyQ (by rw [hydef, ← h]; exact hk₂E.1))
    (mem_inf.mp hk₂).2
  have hαB : α ∉ S.Qa h' := fun h => hαh ((K.mem_Qa_conj_iff hh' hα).mp h)
  have hyα : y * α = α * y := K.conj_commute_of_mem hh' hα
  have hzu : S.z ∉ S.Qa u := K.z_not_mem
  have hα2 : α * α = 1 := by
    obtain ⟨w, hw⟩ := K.exists_conj hy hα (fun h => hαh (by rw [h, mul_one, one_mul]))
    rw [← hw]
    exact conj_z_mul_self S w
  have hconj : ∀ c : G, c * c = 1 → y * c = c * y → y * q * y⁻¹ * q⁻¹ = c →
      q * y * q⁻¹ = y * c := fun c hc2 hcy hc => by
    have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
    calc q * y * q⁻¹ = (y * q * y⁻¹ * q⁻¹)⁻¹ * y := by group
      _ = y * c := by rw [hc, hcinv, hcy]
  have hk₁α : k₁ * S.z * k₁⁻¹ ≠ α := fun h => hαB (h ▸ (mem_inf.mp hk₁).2)
  rcases hqy with hc | hc
  ·
    obtain ⟨w, hw⟩ := K.exists_conj hy hα (fun h => hαh (by rw [h, mul_one, one_mul]))
    have hwE : w * S.z * w⁻¹ ∈ S.QG ⊓ S.Qa u := hw ▸ hα
    refine hy.width_eq_six_of_conj hCE hn (w := w) (σ := y) (g₁ := k₁) (u₁ := h') (d₁ := k₂)
      (x := q) ?_ ?_ rfl (K.mem_Qa_of_mem_E hy hwE hk₁E) (by rw [hw]; exact hk₁α) hyk₁
      (K.mem_Qa_of_mem_E hy hwE hk₂E) hk12 ?_ hyk₂ ?_
    · rw [hw]
      exact hyα
    · intro hyw
      apply hαB
      rw [← hw]
      exact S.mem_Qa_symm (fun h => hyQ (by rw [hydef, h, hw]; exact hα.1)) hyw
    · rw [hw]
      intro h
      apply hαB
      have : α = (k₁ * S.z * k₁⁻¹)⁻¹ * (k₂ * S.z * k₂⁻¹) := by rw [h]; group
      rw [this]
      exact mul_mem (inv_mem (mem_inf.mp hk₁).2) (mem_inf.mp hk₂).2
    · rw [hw]
      exact hconj α hα2 hyα hc
  ·
    have hαz1 : α * S.z ≠ 1 := fun h => hzu (by
      rw [← inv_eq_of_mul_eq_one_right h]
      exact inv_mem hα.2)
    have hαzV : α * S.z ∈ V S g t := by
      refine S.mem_clPre.mpr ⟨S.QG.mul_mem hα.1 S.z_mem_QG, ?_⟩
      rw [S.cl_mul hα.1 S.z_mem_QG, S.cl_z, add_zero, ← K.timmesfeld_11_3 hy]
      exact S.cl_mem_clSub hα hα.1
    obtain ⟨w, hw⟩ := exists_conj_eq_of_mem_V hy.hyp4 K.lin hαzV hαz1
    have hαzu : α * S.z ∉ S.Qa u := fun h => hzu (by
      have := mul_mem (inv_mem (mem_inf.mp hα).2) h
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)
    have hmem : ∀ {k : G}, k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u → k * S.z * k⁻¹ ∈ S.Qa w := by
      intro k hk
      have h1 : α * S.z ∈ S.Qa k :=
        mul_mem (K.mem_Qa_of_mem_E hy hk hα) (S.z_mem_Qa hk.1 (K.base_of_mem hk).1)
      rw [← hw] at h1
      exact S.mem_Qa_symm (fun h => hαzu (by rw [← hw, h]; exact (mem_inf.mp hk).2)) h1
    have hyαz : y * (α * S.z) = α * S.z * y := by
      rw [← mul_assoc, hyα, mul_assoc, hyz, ← mul_assoc]
    have hαz2 : α * S.z * (α * S.z) = 1 := by
      rw [show α * S.z * (α * S.z) = α * α * (S.z * S.z) by
        rw [mul_assoc α S.z, ← mul_assoc S.z α, ← S.z_comm_QG hα.1]; group, hα2, S.z_mul_z,
        one_mul]
    refine hy.width_eq_six_of_conj hCE hn (w := w) (σ := y) (g₁ := k₁) (u₁ := h') (d₁ := k₂)
      (x := q) ?_ ?_ rfl (hmem hk₁E) ?_ hyk₁ (hmem hk₂E) hk12 ?_ hyk₂ ?_
    · rw [hw]
      exact hyαz
    · intro hyw
      apply K.mul_z_not_mem_Qa_conj hh' hy hCE hα hαh
      rw [← hw]
      exact S.mem_Qa_symm
        (fun h => hyQ (by rw [hydef, h, hw]; exact S.QG.mul_mem hα.1 S.z_mem_QG)) hyw
    · rw [hw]
      exact fun h => hαzu (h ▸ hk₁E.2)
    · rw [hw]
      intro h
      apply hαzu
      have : α * S.z = (k₁ * S.z * k₁⁻¹)⁻¹ * (k₂ * S.z * k₂⁻¹) := by rw [h]; group
      rw [this]
      exact mul_mem (inv_mem hk₁E.2) hk₂E.2
    · rw [hw]
      exact hconj (α * S.z) hαz2 hyαz hc

end CFSG.LargeExtraspecial.S11
