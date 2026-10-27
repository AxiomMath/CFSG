module

public import CFSG.ClassicalInvolution.WeakCT.SimplyLaced
public import CFSG.Timmesfeld.LieEmbed.FieldEmbed
public import CFSG.ClassicalInvolution.Models.TwistedPairs.Unitary

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.ClassicalInvolution.Models.TwistedPairs (fixedField mem_fixedField)
open scoped MatrixGroups

section Transport

variable {K K' : Type} [Field K] [Field K']

theorem map_Bs_ringEquiv (e : K ≃+* K') (s : Fin 2) :
    (Bs K s).map (Matrix.SpecialLinearGroup.map (e : K →+* K') : SL(3, K) →* SL(3, K')) =
      Bs K' s := by
  have h : (Matrix.SpecialLinearGroup.map (e : K →+* K') : SL(3, K) →* SL(3, K')).comp (blk K s) =
      (blk K' s).comp (Matrix.SpecialLinearGroup.map (e : K →+* K') : SL(2, K) →* SL(2, K')) :=
    MonoidHom.ext fun A => map_blk (e : K →+* K') s A
  have hsurj : Function.Surjective
      (Matrix.SpecialLinearGroup.map (e : K →+* K') : SL(2, K) →* SL(2, K')) := fun B =>
    ⟨Matrix.SpecialLinearGroup.map (e.symm : K' →+* K) B, map_symm_map e B⟩
  rw [Bs, ← MonoidHom.range_comp, h, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj,
    Subgroup.map_top]
  rfl

theorem LinearBlockStandardPair.of_ringEquiv (e : K ≃+* K') {X : Type} [Group X]
    {W U V : Subgroup X} (h : LinearBlockStandardPair K W U V) :
    LinearBlockStandardPair K' W U V := by
  obtain ⟨θ, c, hW, hker, hUV⟩ := h
  let Φ : SL(3, K) →* SL(3, K') := Matrix.SpecialLinearGroup.map (e : K →+* K')
  let Ψ : SL(3, K') →* SL(3, K) := Matrix.SpecialLinearGroup.map (e.symm : K' →+* K)
  have hΨΦ : ∀ x, Ψ (Φ x) = x := fun x => map_map_symm e x
  have hΦΨ : ∀ y, Φ (Ψ y) = y := fun y => map_symm_map e y
  have hΦsurj : Function.Surjective Φ := fun y => ⟨Ψ y, hΦΨ y⟩
  have hΨsurj : Function.Surjective Ψ := fun x => ⟨Φ x, hΨΦ x⟩
  have hconj : ∀ S : Subgroup SL(3, K),
      ((S.map Φ).map (MulAut.conj (Φ c)⁻¹).toMonoidHom).map (θ.comp Ψ) =
        (S.map (MulAut.conj c⁻¹).toMonoidHom).map θ := by
    intro S
    rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    show θ (Ψ ((Φ c)⁻¹ * Φ x * ((Φ c)⁻¹)⁻¹)) = θ (c⁻¹ * x * (c⁻¹)⁻¹)
    simp only [map_mul, map_inv, hΨΦ]
  have hB12 : (B12 K).map Φ = B12 K' := map_Bs_ringEquiv e 0
  have hB23 : (B23 K).map Φ = B23 K' := map_Bs_ringEquiv e 1
  refine ⟨θ.comp Ψ, Φ c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΨsurj, Subgroup.map_top]
    exact hW
  · intro x hx
    have h1 : Ψ x ∈ Subgroup.center SL(3, K) := hker hx
    have h2 : Φ (Ψ x) ∈ Subgroup.center SL(3, K') :=
      Subgroup.map_center_le_center hΦsurj ⟨_, h1, rfl⟩
    rwa [hΦΨ] at h2
  · rw [← hB12, ← hB23, hconj, hconj]
    exact hUV

end Transport

section FixedField

variable (p f : ℕ) [Fact p.Prime]

theorem card_fixedField_frobQ (hf : 1 ≤ f) :
    Nat.card (fixedField (CFSG.LieType.Steinberg.Exceptional.frobQ p f)) = p ^ f := by
  have e : ↥(fixedField (CFSG.LieType.Steinberg.Exceptional.frobQ p f)) ≃ GaloisField p f :=
    (Equiv.subtypeEquivRight fun c =>
      (mem_fixedField _).trans (CFSG.Timmesfeld.LieEmbed.frobQ_eq_iff_mem_range p f hf c)).trans
      (Equiv.ofInjective _ (CFSG.Timmesfeld.LieEmbed.gfEmbed_injective p f hf)).symm
  rw [Nat.card_congr e, GaloisField.card p f (by omega)]

theorem nonempty_ringEquiv_fixedField_frobQ (hf : 1 ≤ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) :
    Nonempty (F ≃+* fixedField (CFSG.LieType.Steinberg.Exceptional.frobQ p f)) := by
  have := Fintype.ofFinite F
  have := Fintype.ofFinite (fixedField (CFSG.LieType.Steinberg.Exceptional.frobQ p f))
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      card_fixedField_frobQ p f hf])⟩

end FixedField


end CFSG.ClassicalInvolution.WeakCT
