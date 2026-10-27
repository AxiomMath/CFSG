module

public import CFSG.LocalAnalysis.ComponentClassification.AS81OstromWagnerIso

public section

namespace CFSG.ComponentClassification.AS81

open Equiv OstromWagner CFSG.Fischer

theorem image_permCongrHom {P Q : Type} (e : P ≃ Q) (g : Perm P) (s : Set Q) :
    (e.permCongrHom g : Q → Q) '' s = e '' ((g : P → P) '' (e.symm '' s)) := by
  rw [Set.image_image, Set.image_image]
  rfl

theorem ostromWagnerAG24 : OstromWagnerAG24 := by
  intro P _ lines hA h16 G hG h2
  obtain ⟨e, he⟩ := exists_equiv_agLines hA h16
  set φ : Perm P ≃* Perm (F4 × F4) := e.permCongrHom with hφ
  have hφapp : ∀ (g : Perm P) (x : P), φ g (e x) = e (g x) := fun g x => by
    rw [hφ, show e.permCongrHom g (e x) = e (g (e.symm (e x))) from rfl, e.symm_apply_apply]
  set G' := G.map φ.toMonoidHom with hG'def
  have hcoll : ∀ g ∈ G, ∀ ℓ ∈ agLines, (φ g : F4 × F4 → F4 × F4) '' ℓ ∈ agLines := by
    intro g hg ℓ hℓ
    have hℓ' : e.symm '' ℓ ∈ lines := by
      rw [he, ← Set.image_comp, Equiv.self_comp_symm, Set.image_id]
      exact hℓ
    rw [hφ, image_permCongrHom]
    exact (he _).1 (hG g hg _ hℓ')
  have hG' : G' ≤ coll := by
    rintro _ ⟨g, hg, rfl⟩ ℓ hℓ
    refine ⟨hcoll g hg ℓ hℓ, ?_⟩
    have h := hcoll g⁻¹ (G.inv_mem hg) ℓ hℓ
    rwa [map_inv] at h
  have h2' : ∀ p₁ p₂ q₁ q₂ : F4 × F4, p₁ ≠ p₂ → q₁ ≠ q₂ → ∃ g ∈ G', g p₁ = q₁ ∧ g p₂ = q₂ := by
    intro p₁ p₂ q₁ q₂ hp hq
    obtain ⟨g, hg, hg₁, hg₂⟩ := h2 (e.symm p₁) (e.symm p₂) (e.symm q₁) (e.symm q₂)
      (e.symm.injective.ne hp) (e.symm.injective.ne hq)
    refine ⟨φ g, ⟨g, hg, rfl⟩, ?_, ?_⟩
    · rw [← e.apply_symm_apply p₁, hφapp, hg₁, e.apply_symm_apply]
    · rw [← e.apply_symm_apply p₂, hφapp, hg₂, e.apply_symm_apply]
  have hle := transGroup_le hG' h2'
  have hN := le_normalizer_transGroup hG'
  set T := transGroup.map φ.symm.toMonoidHom with hTdef
  have hmemT : ∀ t, t ∈ T ↔ φ t ∈ transGroup := fun t => by
    rw [hTdef, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  refine ⟨T, ?_, ?_, ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩, ?_, ?_⟩
  · intro t ht
    obtain ⟨g, hg, hgt⟩ := hle ((hmemT t).1 ht)
    have : g = t := φ.injective hgt
    exact this ▸ hg
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [hmemT, hmemT, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.1 (hN ⟨g, hg, rfl⟩) (φ t)
  · apply φ.injective
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact transGroup_comm ((hmemT _).1 x.2) ((hmemT _).1 y.2)
  · intro t ht
    apply φ.injective
    rw [map_pow, map_one]
    exact transGroup_sq ((hmemT t).1 ht)
  · rw [hTdef, Subgroup.card_map_of_injective φ.symm.injective, card_transGroup]
  · intro p q
    obtain ⟨τ, hτ, hτp⟩ := exists_transGroup_apply_eq (e p) (e q)
    refine ⟨φ.symm τ, (hmemT _).2 (by rwa [MulEquiv.apply_symm_apply]), ?_⟩
    apply e.injective
    rw [← hφapp, MulEquiv.apply_symm_apply, hτp]

end CFSG.ComponentClassification.AS81
