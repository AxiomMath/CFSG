module

public import CFSG.LargeExtraspecial.S11EightB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

theorem Hyp.Rbar_ne_of_mem_Lbar (hy : Hyp S g) {x : S.O} {k : G} (hkQ : k * S.z * k⁻¹ ∈ S.QG)
    (hkz : k * S.z * k⁻¹ ≠ S.z) (hxk : x ∈ S.Lbar k)
    (hks : S.cl (k * S.z * k⁻¹) ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) :
    Rbar S g x ≠ S.Lbar g := by
  obtain ⟨m, hm, hmk⟩ := hy.fusion k hkQ hkz
  have hc : ((⟨m, hm⟩ : S.M) : G) * g * S.z * (((⟨m, hm⟩ : S.M) : G) * g)⁻¹ =
      k * S.z * k⁻¹ := by
    rw [mul_conj_z S]
    exact hmk
  have hxm : x ∈ S.Lbar (((⟨m, hm⟩ : S.M) : G) * g) := by
    rw [S.Lbar_eq_of_conj_eq hc]
    exact hxk
  have hkV := cl_mem_Vt hxm
  rw [hc] at hkV
  intro hR
  exact hks (Vt_le_span_of_Rbar_eq hy.hyp4 hy.cons hR hkV)

section Conj

variable (K : Conf S g t τ u) {h' : G} (hh' : h' ∈ S.Qa u)
include K hh'

omit hh' in
theorem Conf.z_conj_mem_Qa {x : G} (hx : x ∈ S.Qa u) : S.z * x * S.z⁻¹ ∈ S.Qa u :=
  conj_mem_Qa_of_commute' hx (by rw [← K.conj_eq]; exact (S.z_comm τ.2).symm)

omit hh' in
theorem Conf.tau_mul_self : (τ : G) * τ = 1 := by
  rw [K.conj_eq]
  calc u * S.z * u⁻¹ * (u * S.z * u⁻¹) = u * (S.z * S.z) * u⁻¹ := by group
    _ = 1 := by rw [S.z_mul_z]; group

omit hh' in
theorem Conf.commute_of_mem_Qa {x : G} (hx : x ∈ S.Qa u) : x * τ = τ * x := by
  rw [K.conj_eq]
  exact commute_of_mem_Qa' hx

omit hh' in
theorem Conf.conj_eq_or {h e : G} (hh : h ∈ S.Qa u) (he : e ∈ S.Qa u) :
    (h⁻¹ * e * h = e ∧ h * e = e * h) ∨ (h⁻¹ * e * h = τ * e ∧ h * e ≠ e * h) := by
  have hτ : (S.conjBy u).z = τ := K.conj_eq.symm
  rcases (S.conjBy u).commutator_eq_one_or_z (inv_mem hh) he with h1 | h1
  · left
    have h2 : h⁻¹ * e * h = e := by
      calc h⁻¹ * e * h = h⁻¹ * e * h⁻¹⁻¹ * e⁻¹ * e := by group
        _ = e := by rw [h1, one_mul]
    refine ⟨h2, ?_⟩
    calc h * e = h * (h⁻¹ * e * h) := by rw [h2]
      _ = e * h := by group
  · right
    rw [hτ] at h1
    have h2 : h⁻¹ * e * h = τ * e := by
      calc h⁻¹ * e * h = h⁻¹ * e * h⁻¹⁻¹ * e⁻¹ * e := by group
        _ = τ * e := by rw [h1]
    refine ⟨h2, fun h3 => ?_⟩
    have h4 : h⁻¹ * e * h = e := by
      calc h⁻¹ * e * h = h⁻¹ * (e * h) := by group
        _ = h⁻¹ * (h * e) := by rw [h3]
        _ = e := by group
    have h5 : (τ : G) = 1 := by
      have := h4.symm.trans h2
      calc (τ : G) = τ * e * e⁻¹ := by group
        _ = 1 := by rw [← this]; group
    exact K.ne_one (by rw [← K.rho_eq, show τ = 1 from Subtype.ext h5, map_one])

omit hh' in
theorem Conf.conj_eq_or' {h e : G} (hh : h ∈ S.Qa u) (he : e ∈ S.Qa u) :
    (h * e * h⁻¹ = e ∧ h * e = e * h) ∨ (h * e * h⁻¹ = τ * e ∧ h * e ≠ e * h) := by
  rcases K.conj_eq_or (inv_mem hh) he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [inv_inv] at h1
    refine ⟨h1, ?_⟩
    calc h * e = h * e * h⁻¹ * h := by group
      _ = e * h := by rw [h1]
  · right
    rw [inv_inv] at h1
    refine ⟨h1, fun h3 => h2 ?_⟩
    calc h⁻¹ * e = h⁻¹ * (e * h) * h⁻¹ := by group
      _ = h⁻¹ * (h * e) * h⁻¹ := by rw [h3]
      _ = e * h⁻¹ := by group

theorem Conf.conj_mem_M (hy : Hyp S g) : h' * S.z * h'⁻¹ ∈ S.M := by
  have hc : Commute (S.z * h' * S.z⁻¹ * h'⁻¹) S.z := K.dual_commutator_commute hy hh'
  have h1 := hc.inv_left.eq
  rw [S.mem_M_iff]
  calc h' * S.z * h'⁻¹ * S.z = (S.z * h' * S.z⁻¹ * h'⁻¹)⁻¹ * S.z * S.z := by group
    _ = S.z * (S.z * h' * S.z⁻¹ * h'⁻¹)⁻¹ * S.z := by rw [h1]
    _ = S.z * (h' * S.z * h'⁻¹) := by group

theorem Conf.conj_commute_of_mem {e : G} (he : e ∈ S.QG ⊓ S.Qa u) :
    h' * S.z * h'⁻¹ * e = e * (h' * S.z * h'⁻¹) := by
  have hcomm : S.z * (h'⁻¹ * e * h') = (h'⁻¹ * e * h') * S.z := by
    have hez : e * S.z = S.z * e := S.z_comm_QG he.1
    rcases K.conj_eq_or hh' he.2 with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1, hez]
    · rw [h1, mul_assoc, hez, ← mul_assoc, ← mul_assoc, ← S.z_comm τ.2]
  calc h' * S.z * h'⁻¹ * e = h' * (S.z * (h'⁻¹ * e * h')) * h'⁻¹ := by group
    _ = h' * ((h'⁻¹ * e * h') * S.z) * h'⁻¹ := by rw [hcomm]
    _ = e * (h' * S.z * h'⁻¹) := by group

theorem Conf.mem_Qa_conj_iff {e : G} (he : e ∈ S.QG ⊓ S.Qa u) :
    e ∈ S.Qa h' ↔ h' * e = e * h' := by
  rw [S11.mem_Qa_iff S h' e]
  rcases K.conj_eq_or hh' he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]
    exact iff_of_true he.1 h2
  · rw [h1]
    refine iff_of_false (fun h3 => K.not_mem_QG ?_) h2
    have := S.QG.mul_mem h3 (S.QG.inv_mem he.1)
    rwa [mul_inv_cancel_right] at this

theorem Conf.finrank_Vt_le (hy : Hyp S g) {α₀ : G} (hα₀ : α₀ ∈ S.QG ⊓ S.Qa u)
    (hα₀h : h' * α₀ ≠ α₀ * h') :
    finrank (ZMod 2) (Vt S g t) ≤
      finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa u ⊓ S.Qa h')) + 1 := by
  have hle : Vt S g t ≤ S.clSub (S.QG ⊓ S.Qa u ⊓ S.Qa h') ⊔ (ZMod 2) ∙ S.cl α₀ := by
    rw [← K.timmesfeld_11_3 hy]
    intro v hv
    obtain ⟨e, he, heQ, rfl⟩ := S.mem_clSub_iff.mp hv
    by_cases heB : h' * e = e * h'
    · exact Submodule.mem_sup_left
        (S.cl_mem_clSub (mem_inf.mpr ⟨he, (K.mem_Qa_conj_iff hh' he).mpr heB⟩) heQ)
    ·
      have h1 : h' * (α₀ * e) = (α₀ * e) * h' := by
        rcases K.conj_eq_or' hh' hα₀.2 with ⟨-, h2⟩ | ⟨h2, -⟩
        · exact absurd h2 hα₀h
        rcases K.conj_eq_or' hh' he.2 with ⟨-, h3⟩ | ⟨h3, -⟩
        · exact absurd h3 heB
        have hτα : (τ : G) * α₀ = α₀ * τ := (K.commute_of_mem_Qa hα₀.2).symm
        have hττ : (τ : G) * τ = 1 := K.tau_mul_self
        calc h' * (α₀ * e) = (h' * α₀ * h'⁻¹) * (h' * e * h'⁻¹) * h' := by group
          _ = τ * α₀ * (τ * e) * h' := by rw [h2, h3]
          _ = α₀ * (τ * τ) * e * h' := by rw [hτα]; group
          _ = (α₀ * e) * h' := by rw [hττ]; group
      have hαe : α₀ * e ∈ S.QG ⊓ S.Qa u ⊓ S.Qa h' :=
        mem_inf.mpr ⟨mul_mem hα₀ he, (K.mem_Qa_conj_iff hh' (mul_mem hα₀ he)).mpr h1⟩
      have h2 : S.cl e = S.cl α₀ + S.cl (α₀ * e) := by
        rw [S.cl_mul hα₀.1 heQ, ← add_assoc, ZModModule.add_self, zero_add]
      rw [h2, add_comm]
      exact Submodule.add_mem_sup (S.cl_mem_clSub hαe (mul_mem hα₀.1 heQ))
        (Submodule.mem_span_singleton_self _)
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (S.clSub (S.QG ⊓ S.Qa u ⊓ S.Qa h'))
    ((ZMod 2) ∙ S.cl α₀)
  have h3 := finrank_span_singleton_le_one (S.cl α₀)
  omega

theorem Conf.conj_not_mem_QG (hy : Hyp S g) (hCE : CentralExtInput.{u_G}) {α₀ : G}
    (hα₀ : α₀ ∈ S.QG ⊓ S.Qa u) (hα₀h : h' * α₀ ≠ α₀ * h') : h' * S.z * h'⁻¹ ∉ S.QG := by
  intro hyQ
  have hc : S.z * h' * S.z⁻¹ * h'⁻¹ ∈ S.QG ⊓ S.Qa u := by
    refine mem_inf.mpr ⟨?_, mul_mem (K.z_conj_mem_Qa hh') (inv_mem hh')⟩
    rw [show S.z * h' * S.z⁻¹ * h'⁻¹ = S.z * (h' * S.z * h'⁻¹)⁻¹ by group]
    exact S.QG.mul_mem S.z_mem_QG (S.QG.inv_mem hyQ)
  exact hα₀h (K.dual_commute_of_commutator_mem hy hCE hh' hc (Or.inl rfl) hα₀)

theorem Conf.rho_conj_mem_Nbar (hy : Hyp S g) (hyQ : h' * S.z * h'⁻¹ ∉ S.QG) {k : G}
    (hk : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u ⊓ S.Qa h') :
    S.ρ ⟨h' * S.z * h'⁻¹, K.conj_mem_M hh' hy⟩ ∈ Nbar S g t := by
  have hkE : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u := (mem_inf.mp hk).1
  obtain ⟨hkz, htk⟩ := K.base_of_mem hkE
  have hyk : h' * S.z * h'⁻¹ ∈ S.Qa k :=
    S.mem_Qa_symm (fun h => hyQ (h ▸ hkE.1)) (mem_inf.mp hk).2
  refine mem_Nbar.mpr ⟨?_, fun v hv => ?_⟩
  · rw [← hy.Rbar_eq hkE.1 hkz t]
    exact Lbar_le_Rbar htk (S.ρ_mem_Lbar ⟨hyk, K.conj_mem_M hh' hy⟩)
  · rw [← K.timmesfeld_11_3 hy] at hv
    obtain ⟨e, he, heQ, rfl⟩ := S.mem_clSub_iff.mp hv
    rw [S.ρ_cl _ heQ]
    congr 1
    change h' * S.z * h'⁻¹ * e * (h' * S.z * h'⁻¹)⁻¹ = e
    rw [K.conj_commute_of_mem hh' he, mul_inv_cancel_right]

theorem Conf.rho_conj_commute (hy : Hyp S g) (hCE : CentralExtInput.{u_G}) {ℓ : S.O}
    (hℓ : ℓ ∈ Nbar S g t) :
    ℓ * S.ρ ⟨h' * S.z * h'⁻¹, K.conj_mem_M hh' hy⟩ =
      S.ρ ⟨h' * S.z * h'⁻¹, K.conj_mem_M hh' hy⟩ * ℓ := by
  obtain ⟨x0, hx0, rfl⟩ := (S4.mem_Lbar S).mp (K.timmesfeld_11_5 hy hCE hℓ)
  have hc : Commute (S.z * h' * S.z⁻¹ * h'⁻¹) x0 :=
    K.dual_commutator_commute_of_mem hy hh' (mem_inf.mpr ⟨(mem_inf.mp hx0).1, x0.2⟩)
  have hz : Commute S.z (x0 : G) := (S.z_comm x0.2).symm
  have h1 : Commute (h' * S.z * h'⁻¹) (x0 : G) := by
    have h2 : h' * S.z * h'⁻¹ = (S.z * h' * S.z⁻¹ * h'⁻¹)⁻¹ * S.z := by group
    rw [h2]
    exact hc.inv_left.mul_left hz
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h1.symm.eq

theorem Conf.mul_z_not_mem_Qa_conj (hy : Hyp S g) (hCE : CentralExtInput.{u_G}) {α : G}
    (hα : α ∈ S.QG ⊓ S.Qa u) (hαh : h' * α ≠ α * h') : α * S.z ∉ S.Qa h' := by
  intro hmem
  have hq := (S11.mem_Qa_iff S h' _).mp hmem
  have hcomm : h'⁻¹ * α * h' = τ * α := by
    rcases K.conj_eq_or hh' hα.2 with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact absurd h2 hαh
    · exact h1
  set c := S.z * h'⁻¹ * S.z⁻¹ * h' with hc
  have hcu : c ∈ S.Qa u := mul_mem (K.z_conj_mem_Qa (inv_mem hh')) hh'
  have hτu : (τ : G) ∈ S.Qa u := by rw [K.conj_eq]; exact S.conj_z_mem_Qa u
  have he_eq : (τ : G) * α * c⁻¹ = h'⁻¹ * (α * S.z) * h' * S.z⁻¹ := by
    rw [← hcomm, hc]
    group
  have he : (τ : G) * α * c⁻¹ ∈ S.QG ⊓ S.Qa u := by
    refine mem_inf.mpr ⟨?_, mul_mem (mul_mem hτu hα.2) (inv_mem hcu)⟩
    rw [he_eq]
    exact S.QG.mul_mem hq (S.QG.inv_mem S.z_mem_QG)
  have hc' : S.z * h'⁻¹ * S.z⁻¹ * h'⁻¹⁻¹ = ((τ : G) * α * c⁻¹)⁻¹ * α * τ := by
    rw [inv_inv, ← hc]
    have hτα : (τ : G) * α = α * τ := (K.commute_of_mem_Qa hα.2).symm
    calc c = ((τ : G) * α * c⁻¹)⁻¹ * τ * α := by group
      _ = ((τ : G) * α * c⁻¹)⁻¹ * α * τ := by rw [mul_assoc _ (τ : G) α, hτα, ← mul_assoc]
  have h1 := K.dual_commute_of_commutator_mem hy hCE (inv_mem hh')
    (mul_mem (inv_mem he) hα) (Or.inr hc') hα
  apply hαh
  calc h' * α = h' * (α * h'⁻¹) * h' := by group
    _ = h' * (h'⁻¹ * α) * h' := by rw [h1]
    _ = α * h' := by group

end Conj

end CFSG.LargeExtraspecial.S11
