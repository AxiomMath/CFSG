module

public import CFSG.GH74.E2.TermBasic

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.GH74.GLS

section SylowPush

variable {G : Type} [Group G]

theorem sylow_map_le (K : Subgroup G) (T : Sylow 2 ↥K) :
    (T : Subgroup ↥K).map K.subtype ≤ K := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem sylow_map_isPGroup (K : Subgroup G) (T : Sylow 2 ↥K) :
    IsPGroup 2 ((T : Subgroup ↥K).map K.subtype) :=
  T.isPGroup'.map K.subtype

theorem sylow_map_max (K : Subgroup G) (T : Sylow 2 ↥K) (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPK : P ≤ K) (hle : (T : Subgroup ↥K).map K.subtype ≤ P) :
    P = (T : Subgroup ↥K).map K.subtype := by
  have hP' : IsPGroup 2 (P.subgroupOf K) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
  have hle' : (T : Subgroup ↥K) ≤ P.subgroupOf K := fun x hx =>
    hle (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
  have h := T.is_maximal' hP' hle'
  rw [← Subgroup.map_subgroupOf_eq_of_le hPK, h]

noncomputable def sylowMapEquiv (K : Subgroup G) (T : Sylow 2 ↥K) :
    ↥(T : Subgroup ↥K) ≃* ↥((T : Subgroup ↥K).map K.subtype) :=
  (T : Subgroup ↥K).equivMapOfInjective K.subtype K.subtype_injective

end SylowPush

section CenSup

variable {G : Type} [Group G]

theorem inner_of_aut_inner {t : G} {K : Subgroup G} (hK : IsCompCen t K)
    (huniq : ∀ K' : Subgroup G, IsCompCen t K' → K' = K)
    (hOut : ∀ φ : MulAut ↥K, ∃ k : ↥K, ∀ x : ↥K, φ x = k * x * k⁻¹) :
    ∀ g ∈ Cen t, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹ := by
  intro g hg
  have hconj : conjugate K g = K := conjugate_eq_of_unique hK huniq hg
  have hnorm : g ∈ normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h := AS16.mem_conjugate_iff' K g x
    rw [hconj] at h
    exact h
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut ↥K, φ = K.normalizerMonoidHom ⟨g, hnorm⟩ := ⟨_, rfl⟩
  have hφapp : ∀ x : ↥K, ((φ x : ↥K) : G) = g * x * g⁻¹ := fun x => by
    rw [hφ]
    rfl
  obtain ⟨k, hk⟩ := hOut φ
  refine ⟨k, k.2, fun x hx => ?_⟩
  have := congrArg (fun y : ↥K => (y : G)) (hk ⟨x, hx⟩)
  simpa [hφapp] using this

theorem cen_eq_sup_of_inner {t : G} {K : Subgroup G} (hKC : K ≤ Cen t)
    (hinner : ∀ g ∈ Cen t, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹) :
    Cen t = K ⊔ (Cen t ⊓ Subgroup.centralizer (K : Set G)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨k, hkK, hk⟩ := hinner g hg
    have hkC : k ∈ Cen t := hKC hkK
    have hmem : k⁻¹ * g ∈ Cen t ⊓ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_inf]
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hkC) hg, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := hk x hx
      calc x * (k⁻¹ * g) = k⁻¹ * (k * x * k⁻¹) * g := by group
        _ = k⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
        _ = (k⁻¹ * g) * x := by group
    have : g = k * (k⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hkK hmem
  · exact sup_le hKC inf_le_left

end CenSup

end CFSG.GH74.E2
