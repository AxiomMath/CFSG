module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

variable {p n : ℕ} {L L' : Type} [Group L] [Group L'] {G C : Type} [Group G] [CommGroup C]
  {Φ : G →* MulAut L} {det : G →* C} {Z : Subgroup G}

theorem od_congr_apply (e : L ≃* L') (α : MulAut L) (x : L) :
    (MulAut.congr e) α (e x) = e (α x) := by
  change e (α (e.symm (e x))) = _
  rw [MulEquiv.symm_apply_apply]

theorem ODFamily.transport (hF : ODFamily p n Φ det Z) (e : L ≃* L') :
    ODFamily p n ((MulAut.congr e).toMonoidHom.comp Φ) det Z where
  central := hF.central
  ker_eq B := by
    change (MulAut.congr e) (Φ B) = 1 ↔ _
    rw [map_eq_one_iff _ (MulAut.congr e).injective]
    exact hF.ker_eq B
  det_center := hF.det_center
  comm_mem α β := by
    obtain ⟨B, hB⟩ := hF.comm_mem ((MulAut.congr e).symm α) ((MulAut.congr e).symm β)
    refine ⟨B, ?_⟩
    change (MulAut.congr e) (Φ B) = _
    rw [hB]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  inner_of_det B hB := by
    obtain ⟨ℓ, hℓ⟩ := hF.inner_of_det B hB
    refine ⟨e ℓ, ?_⟩
    change MulAut.conj (e ℓ) = (MulAut.congr e) (Φ B)
    rw [← hℓ]
    exact (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e ℓ).symm
  exists_det_one ℓ' := by
    obtain ⟨B, hdet, hB⟩ := hF.exists_det_one (e.symm ℓ')
    refine ⟨B, hdet, ?_⟩
    change (MulAut.congr e) (Φ B) = _
    rw [hB, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
  lift α := by
    obtain ⟨κ, t, ht1, ht2, ht3⟩ := hF.lift ((MulAut.congr e).symm α)
    refine ⟨κ, t, fun B => ?_, ht2, ht3⟩
    change α * (MulAut.congr e) (Φ B) * α⁻¹ = (MulAut.congr e) (Φ (t B))
    rw [← ht1 B]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  cyclic := hF.cyclic
  torus3 B hB := by
    obtain ⟨f, hf, hfix⟩ := hF.torus3 B hB
    refine ⟨e.toMonoidHom.comp f, e.injective.comp hf, fun a => ?_⟩
    change (MulAut.congr e) (Φ B) (e (f a)) = e (f a)
    rw [od_congr_apply, hfix]
  monomial hn B hB hBp := by
    obtain ⟨E, hE, hcard, hnorm⟩ := hF.monomial hn B hB hBp
    refine ⟨E.map e.toMonoidHom, IsElemAbelian.map hE _, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective e.injective]
      exact hcard
    · rintro _ ⟨x, hx, rfl⟩
      change (MulAut.congr e) (Φ B) (e x) ∈ _
      rw [od_congr_apply]
      exact ⟨Φ B x, hnorm x hx, rfl⟩
  det_nonpower := hF.det_nonpower
  comm_ne := hF.comm_ne

end CFSG.LocalAnalysis.RankFourTheoremC
