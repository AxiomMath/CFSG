module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellStruct2

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization

section Mnorm

variable {G : Type*} [Group G] {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

@[expose] def Mnorm (S : Sylow 2 G) (ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k) : Subgroup G :=
  (Subgroup.normalizer (((S : Subgroup G).map ρ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k)) :
    Set (Matrix.SpecialLinearGroup (Fin 2) k))).comap ρ

theorem mem_Mnorm_iff [Finite k] {ℓ : ℙ k (Fin 2 → k)} (hℓ : (S : Subgroup G).map ρ = rootGrp ℓ)
    {g : G} : g ∈ Mnorm S ρ ↔ ρ g • ℓ = ℓ := by
  unfold Mnorm
  rw [Subgroup.mem_comap, hℓ]
  exact mem_normalizer_rootGrp_iff

theorem aimg_thompsonJ [Finite G] (S₀ : Subgroup G) (α : S₀ ≃* S₀) :
    aimg S₀ α (thompsonJ S₀) = thompsonJ S₀ := by
  have key : ∀ β : S₀ ≃* S₀, aimg S₀ β (thompsonJ S₀) ≤ thompsonJ S₀ := by
    intro β
    have h1 : thompsonJ S₀ ≤ aimg S₀ β.symm (thompsonJ S₀) := by
      refine thompsonJ_le_of_forall fun A hA => ?_
      have h2 := maxElem_le_thompsonJ (isMaxElemAbelian_aimg β hA)
      have h3 := aimg_mono (S := S₀) (α := β.symm) h2
      rwa [aimg_symm_aimg hA.1] at h3
    have h2 := aimg_mono (S := S₀) (α := β) h1
    rwa [aimg_aimg_symm (thompsonJ_le_self' S₀)] at h2
  refine le_antisymm (key α) ?_
  have h := aimg_mono (S := S₀) (α := α) (key α.symm)
  rwa [aimg_aimg_symm (thompsonJ_le_self' S₀)] at h

theorem thompsonJ_conj_mem_sylow [Finite G] {S₀ : Subgroup G} {s t : G} (hs : s ∈ S₀)
    (ht : t ∈ thompsonJ S₀) : s * t * s⁻¹ ∈ thompsonJ S₀ := by
  have h1 := aimg_thompsonJ S₀ (MulAut.conj (⟨s, hs⟩ : S₀))
  have htS : t ∈ S₀ := thompsonJ_le_self' S₀ ht
  have : s * t * s⁻¹ ∈ aimg S₀ (MulAut.conj (⟨s, hs⟩ : S₀)) (thompsonJ S₀) :=
    mem_aimg.mpr ⟨⟨t, htS⟩, ht, rfl⟩
  rwa [h1] at this

namespace IsNatBase

variable [Finite G] [Finite k]

omit [Finite k] in
theorem ne_one_of_mem_sylow_of_not_mem_core (h : IsNatBase S ρ (Ecore G) ψ) {x : G}
    (hx : x ∈ (S : Subgroup G)) (hxQ : x ∉ CFSG.pCore 2 G) : ρ x ≠ 1 := by
  intro h1
  have : x ∈ (S : Subgroup G) ⊓ ρ.ker := ⟨hx, h1⟩
  rw [h.sylow_inf_ker] at this
  exact hxQ this

theorem mem_Mnorm_of_conj_mem (h : IsNatBase S ρ (Ecore G) ψ) {g x : G}
    (hx : x ∈ (S : Subgroup G)) (hxQ : x ∉ CFSG.pCore 2 G) (hgx : g * x * g⁻¹ ∈ Mnorm S ρ) :
    g ∈ Mnorm S ρ := by
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  rw [mem_Mnorm_iff hℓ] at hgx ⊢
  have hu : ρ x ∈ rootGrp ℓ := by rw [← hℓ]; exact ⟨x, hx, rfl⟩
  have hne := h.ne_one_of_mem_sylow_of_not_mem_core hx hxQ
  have hq : ρ x • (ρ g)⁻¹ • ℓ = (ρ g)⁻¹ • ℓ := by
    have h1 : (ρ g * ρ x * (ρ g)⁻¹) • ℓ = ℓ := by simpa [map_mul, map_inv] using hgx
    rw [mul_smul, mul_smul] at h1
    exact eq_inv_smul_iff.mpr h1
  have h2 := eq_of_smul_eq_of_mem_rootGrp hu hne hq
  rw [inv_smul_eq_iff] at h2
  exact h2.symm

omit [Finite k] in
theorem sup_core_eq_top (h : IsNatBase S ρ (Ecore G) ψ) {Y : Subgroup G} {ℓ m : ℙ k (Fin 2 → k)}
    (hne : ℓ ≠ m) (h1 : rootGrp ℓ ≤ Y.map ρ) (h2 : rootGrp m ≤ Y.map ρ) :
    Y ⊔ CFSG.pCore 2 G = ⊤ := by
  refine h.eq_top_of_map_eq_top le_sup_right ?_
  rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr h.core_le, sup_bot_eq]
  rw [eq_top_iff, ← rootGrp_sup_rootGrp hne]
  exact sup_le h1 h2

end IsNatBase

theorem Hone_le_of_sup_core_eq_top [Finite G] {J : Subgroup G}
    (hTJ : thompsonJ (S : Subgroup G) ≤ J) (hJ : J ⊔ CFSG.pCore 2 G = ⊤) : Hone S ≤ J := by
  unfold Hone
  rw [Subgroup.normalClosure]
  refine (Subgroup.closure_le J).mpr ?_
  intro x hx
  obtain ⟨t, ht, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
  have hc : c ∈ J ⊔ CFSG.pCore 2 G := by rw [hJ]; trivial
  obtain ⟨j, hj, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hc
  have : j * q * t * (j * q)⁻¹ = j * (q * t * q⁻¹) * j⁻¹ := by group
  rw [this]
  exact J.mul_mem (J.mul_mem hj (hTJ (thompsonJ_conj_mem_sylow (core_le_sylow S hq) ht)))
    (J.inv_mem hj)

end Mnorm

end CFSG.QuasithinUnique.Setup.Campbell
