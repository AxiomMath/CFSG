module

public import CFSG.LargeExtraspecial.S11Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
theorem mem_Qa_iff (k x : G) : x ∈ S.Qa k ↔ k⁻¹ * x * k ∈ S.QG := by
  have h := S.mem_Qa_mul_iff (g := 1) (h := k) (x := x)
  rwa [mul_one, S.Qa_one] at h

theorem Hyp.mem_Qa_of_commute (hy : Hyp S g) {k u α : G} (hkQ : k * S.z * k⁻¹ ∈ S.QG)
    (hkz : k * S.z * k⁻¹ ≠ S.z) (hτQ : u * S.z * u⁻¹ ∉ S.QG) (hku : k * S.z * k⁻¹ ∈ S.Qa u)
    (hα : α ∈ S.QG ⊓ S.Qa u) (hαk : α * (k * S.z * k⁻¹) = k * S.z * k⁻¹ * α) :
    α ∈ S.Qa k := by
  by_contra hαQ
  have hzk : S.z ∈ S.Qa k := S.z_mem_Qa_of_mem_QG rfl hkQ hkz
  have hbQ : k⁻¹ * S.z * k⁻¹⁻¹ ∈ S.QG := by
    rw [inv_inv]
    exact (mem_Qa_iff S k S.z).mp hzk
  have hbz : k⁻¹ * S.z * k⁻¹⁻¹ ≠ S.z := by
    rw [inv_inv]
    intro h
    apply hkz
    calc k * S.z * k⁻¹ = k * (k⁻¹ * S.z * k) * k⁻¹ := by rw [h]
      _ = S.z := by group
  have hyL : k⁻¹ * α * k ∈ S.L0 k⁻¹ := by
    refine ⟨?_, ?_⟩
    · have := conj_mem_Qa_mul S (h := k⁻¹) (g := 1) (x := α) (by rw [S.Qa_one]; exact hα.1)
      simpa [mul_assoc] using this
    · show k⁻¹ * α * k ∈ S.M
      rw [S.mem_M_iff]
      calc k⁻¹ * α * k * S.z = k⁻¹ * (α * (k * S.z * k⁻¹)) * k := by group
        _ = k⁻¹ * (k * S.z * k⁻¹ * α) * k := by rw [hαk]
        _ = S.z * (k⁻¹ * α * k) := by group
  have hyQ : k⁻¹ * α * k ∉ S.QG := fun h => hαQ ((mem_Qa_iff S k α).mpr h)
  have hd : (k⁻¹ * u) * S.z * (k⁻¹ * u)⁻¹ = k⁻¹ * (u * S.z * u⁻¹) * k := by group
  have hne : k * S.z * k⁻¹ ≠ u * S.z * u⁻¹ := fun h => hτQ (h ▸ hkQ)
  have hτk : u * S.z * u⁻¹ ∈ S.Qa k := S.mem_Qa_symm hne hku
  have hdQ : (k⁻¹ * u) * S.z * (k⁻¹ * u)⁻¹ ∈ S.QG := by
    rw [hd]
    exact (mem_Qa_iff S k _).mp hτk
  have hdz : (k⁻¹ * u) * S.z * (k⁻¹ * u)⁻¹ ≠ S.z := by
    rw [hd]
    intro h
    apply hne
    calc k * S.z * k⁻¹ = k * (k⁻¹ * (u * S.z * u⁻¹) * k) * k⁻¹ := by rw [h]
      _ = u * S.z * u⁻¹ := by group
  have hyj : k⁻¹ * α * k ∈ S.La (k⁻¹ * u) := by
    refine (L0_le_La S _) ⟨?_, hyL.2⟩
    have := conj_mem_Qa_mul S (h := k⁻¹) hα.2
    simpa [mul_assoc] using this
  have h1 := hy.mem_Qa_of_mem_La hbQ hbz hyL hyQ hdQ hdz hyj
  rw [hd] at h1
  apply hτQ
  have h2 := conj_mem_Qa_mul S (h := k) h1
  rw [mul_inv_cancel, S.Qa_one] at h2
  simpa [mul_assoc] using h2

variable {t : S.O} {τ : S.M} {u : G}

theorem Conf.cl_mem_Vt_of_conj (hy : Hyp S g) (K : Conf S g t τ u) {γ j : G}
    (hγ : γ ∈ S.QG ⊓ S.Qa u) (hj : j * S.z * j⁻¹ = γ) : S.cl γ ∈ Vt S g t := by
  have hγz : γ ≠ S.z := fun h => K.z_not_mem (h ▸ hγ.2)
  obtain ⟨m, hm, hmγ⟩ := hy.fusion j (hj ▸ hγ.1) (hj ▸ hγz)
  have hc : ((⟨m, hm⟩ : S.M) : G) * g * S.z * (((⟨m, hm⟩ : S.M) : G) * g)⁻¹ = γ := by
    rw [mul_conj_z S]
    exact hmγ.trans hj
  have hne : j * S.z * j⁻¹ ≠ u * S.z * u⁻¹ := by
    rw [hj, ← K.conj_eq]
    intro h
    exact K.not_mem_QG (h ▸ hγ.1)
  have hτj : (τ : G) ∈ S.Qa j := by
    rw [K.conj_eq]
    exact S.mem_Qa_symm hne (hj ▸ hγ.2)
  have ht : t ∈ S.Lbar (((⟨m, hm⟩ : S.M) : G) * g) := by
    rw [S.Lbar_eq_of_conj_eq (hc.trans hj.symm), ← K.rho_eq]
    exact S.ρ_mem_Lbar ⟨hτj, τ.2⟩
  have := cl_mem_Vt ht
  rwa [hc] at this

theorem Conf.cl_mem_Vt_of_mem_La (hy : Hyp S g) (K : Conf S g t τ u) {j : G}
    (hjQ : j * S.z * j⁻¹ ∈ S.QG) (hjz : j * S.z * j⁻¹ ≠ S.z) (hτj : (τ : G) ∈ S.La j) :
    S.cl (j * S.z * j⁻¹) ∈ Vt S g t := by
  obtain ⟨m, hm, hmj⟩ := hy.fusion j hjQ hjz
  have hc : ((⟨m, hm⟩ : S.M) : G) * g * S.z * (((⟨m, hm⟩ : S.M) : G) * g)⁻¹ =
      j * S.z * j⁻¹ := by
    rw [mul_conj_z S]
    exact hmj
  have ht : t ∈ S.Lbar (((⟨m, hm⟩ : S.M) : G) * g) := by
    rw [S.Lbar_eq_of_conj_eq hc, ← S.map_La_eq_Lbar j, ← K.rho_eq]
    exact ⟨τ, mem_subgroupOf.mpr hτj, rfl⟩
  have := cl_mem_Vt ht
  rwa [hc] at this

end CFSG.LargeExtraspecial.S11
