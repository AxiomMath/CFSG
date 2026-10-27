module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLocal2

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

theorem le_normalizer_elemBaumannIn {H : Type*} [Group H] [Finite H] (R : Subgroup H) :
    R ≤ Subgroup.normalizer ((elemBaumannIn 2 R : Subgroup H) : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSR : elemBaumannIn 2 R ≤ R := elemBaumannIn_le 2 R
  have hchar := characteristic_elemBaumannIn R
  have hSnorm : ((elemBaumannIn 2 R).subgroupOf R).Normal := inferInstance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hSR).mp hSnorm

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

namespace WreathHyp

include h

theorem ker_rho_le_M : h.rho.ker ≤ M := by
  rw [h.ker_rho_eq_centralizer_V]
  intro x hx
  have := h.frattini.2.2.2.1 hx 1 (Subgroup.mem_top _)
  simpa using this

theorem mem_M_of_rho_mem_T0 {x : H} (hx : h.rho x ∈ h.T0) : x ∈ M := by
  obtain ⟨t, ht⟩ := h.exists_t
  rw [← h.rho_S_eq_T0 ht] at hx
  obtain ⟨s, hs, hsx⟩ := hx
  have h1 : s⁻¹ * x ∈ h.rho.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsx]
    group
  have h2 : x = s * (s⁻¹ * x) := by group
  rw [h2]
  exact M.mul_mem (h.S_le_M hs) (h.ker_rho_le_M h1)

omit [Finite H] in
theorem T0_le_normalizer_Dat (i : Fin r) :
    h.T0 ≤ Subgroup.normalizer (h.Dat i : Set (MulAut ↥W)) := by
  intro g hg
  obtain ⟨⟨x, hxR, rfl⟩, hgB⟩ := hg
  have hpi : h.piH x = 1 := (h.piH_eq_one_iff x).mpr hgB
  have hpi' : h.piH x⁻¹ = 1 := by rw [map_inv, hpi, inv_one]
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · intro hd
    have := h.conj_Dat_mem x hd
    rwa [hpi] at this
  · intro hd
    have := h.conj_Dat_mem x⁻¹ hd
    rw [hpi', map_inv, inv_inv] at this
    simpa [mul_assoc] using this

variable {h} {i : Fin r} {P : Subgroup H} (hP : h.IsSelected i P)

include hP

theorem IsSelected.map_rho_le : P.map h.rho ≤ h.Dat i ⊔ h.T0 := by
  obtain ⟨t, ht⟩ := h.exists_t
  calc P.map h.rho ≤ (h.Yi i ⊔ elemBaumannIn 2 R).map h.rho := Subgroup.map_mono hP.P_le
    _ = (h.Yi i).map h.rho ⊔ (elemBaumannIn 2 R).map h.rho := Subgroup.map_sup _ _ _
    _ = h.Dat i ⊔ h.T0 := by rw [h.rho_map_Yi, h.rho_S_eq_T0 ht]

theorem IsSelected.T0_le_map : h.T0 ≤ P.map h.rho := by
  obtain ⟨t, ht⟩ := h.exists_t
  rw [← h.rho_S_eq_T0 ht]
  exact Subgroup.map_mono hP.S_le

theorem IsSelected.not_map_le_T0 : ¬ P.map h.rho ≤ h.T0 := fun hle =>
  hP.not_le_M fun x hx => h.mem_M_of_rho_mem_T0 (hle ⟨x, hx, rfl⟩)

theorem IsSelected.Dat_le_map : h.Dat i ≤ P.map h.rho := by
  let _ := h.cg
  obtain ⟨g, hgP, hgT⟩ : ∃ g ∈ P.map h.rho, g ∉ h.T0 := by
    by_contra hcon
    push Not at hcon
    exact hP.not_map_le_T0 hcon
  obtain ⟨d, hd, b, hb, rfl⟩ := Layer.mem_sup_mul (h.T0_le_normalizer_Dat i) (hP.map_rho_le hgP)
  have hdP : d ∈ P.map h.rho := by
    have : d = (d * b) * b⁻¹ := by group
    rw [this]
    exact (P.map h.rho).mul_mem hgP ((P.map h.rho).inv_mem (hP.T0_le_map hb))
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hgT (by simpa using hb)
  have hnt := exists_ne_of_cubeAt_ne_one h.planeFamily hd hd1
  exact (cubeAt_le_zpowers h.planeFamily hd hnt).trans ((Subgroup.zpowers_le).mpr hdP)

theorem IsSelected.map_rho : P.map h.rho = h.Dat i ⊔ h.T0 :=
  le_antisymm hP.map_rho_le (sup_le hP.Dat_le_map hP.T0_le_map)

end WreathHyp

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
