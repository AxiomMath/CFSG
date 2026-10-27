module

public import CFSG.ClassicalInvolution.Phan.Center

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section Automorphism

variable {G X : Type*} [Group G] [Group X]

theorem range_comp_mulEquiv (θ : G →* X) (e : G ≃* G) :
    (θ.comp e.toMonoidHom).range = θ.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x, by simp⟩

theorem ker_comp_mulEquiv_le_center {θ : G →* X} (hθ : θ.ker ≤ Subgroup.center G) (e : G ≃* G) :
    (θ.comp e.toMonoidHom).ker ≤ Subgroup.center G := fun _ hx =>
  (MulEquivClass.apply_mem_center_iff e).1 (hθ hx)

theorem map_comp_mulEquiv (θ : G →* X) (e : G ≃* G) (H : Subgroup G) :
    H.map (θ.comp e.toMonoidHom) = (H.map e.toMonoidHom).map θ :=
  (Subgroup.map_map _ _ _).symm

end Automorphism

section Normalize

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {X : Type} [Group X]

theorem pair_normalize {W U V : Subgroup X} (h : UnitaryBlockStandardPair K p f W U V) :
    ∃ θ : Su K p f 3 →* X, θ.range = W ∧ θ.ker ≤ Subgroup.center (Su K p f 3) ∧
      (B12 K p f).map θ = U ∧ (B23 K p f).map θ = V := by
  obtain ⟨θ, c, hrange, hker, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · refine ⟨θ.comp (MulAut.conj c⁻¹).toMonoidHom, ?_, ker_comp_mulEquiv_le_center hker _, ?_, ?_⟩
    · rw [range_comp_mulEquiv, hrange]
    · rw [map_comp_mulEquiv, h1]
    · rw [map_comp_mulEquiv, h2]
  · have e : (MulAut.conj (c⁻¹ * swapElt K p f)).toMonoidHom =
        (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj (swapElt K p f)).toMonoidHom := by
      ext x
      simp [mul_assoc]
    refine ⟨θ.comp (MulAut.conj (c⁻¹ * swapElt K p f)).toMonoidHom, ?_,
      ker_comp_mulEquiv_le_center hker _, ?_, ?_⟩
    · rw [range_comp_mulEquiv, hrange]
    · rw [map_comp_mulEquiv, e, ← Subgroup.map_map, map_conj_swapElt_B12, h2]
    · rw [map_comp_mulEquiv, e, ← Subgroup.map_map, map_conj_swapElt_B23, h1]

theorem pair_block_inj (hK : Nat.card K = (p ^ f) ^ 2) {θ : Su K p f 3 →* X}
    (hker : θ.ker ≤ Subgroup.center (Su K p f 3)) {U V : Subgroup X}
    (hU : (B12 K p f).map θ = U) (hV : (B23 K p f).map θ = V) :
    Function.Injective (θ.comp (embSUid (unitaryInvolution K p f) 2)) ∧
      (θ.comp (embSUid (unitaryInvolution K p f) 2)).range = U ∧
      Function.Injective (θ.comp (embSUid (unitaryInvolution K p f) 0)) ∧
      (θ.comp (embSUid (unitaryInvolution K p f) 0)).range = V :=
  ⟨comp_embSUid_injective hK hker 2, by rw [MonoidHom.range_comp, ← hU]; rfl,
    comp_embSUid_injective hK hker 0, by rw [MonoidHom.range_comp, ← hV]; rfl⟩

theorem nonempty_mulEquiv_of_standardPair (hK : Nat.card K = (p ^ f) ^ 2) {W U V : Subgroup X}
    (h : UnitaryBlockStandardPair K p f W U V) :
    Nonempty (Su K p f 2 ≃* U) ∧ Nonempty (Su K p f 2 ≃* V) := by
  obtain ⟨θ, -, hker, hU, hV⟩ := pair_normalize h
  obtain ⟨hi₂, hr₂, hi₀, hr₀⟩ := pair_block_inj hK hker hU hV
  exact ⟨⟨(MonoidHom.ofInjective hi₂).trans (MulEquiv.subgroupCongr hr₂)⟩,
    ⟨(MonoidHom.ofInjective hi₀).trans (MulEquiv.subgroupCongr hr₀)⟩⟩

end Normalize

end CFSG.ClassicalInvolution.Phan
