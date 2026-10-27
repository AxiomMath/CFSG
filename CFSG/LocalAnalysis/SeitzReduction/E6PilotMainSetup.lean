module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainRows
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeFinal

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)
open CFSG.SeitzReduction.F4Pilot (F4Work QuadraticFrobenius exists_quadraticFrobenius_F4)

section Transport


theorem baseChangeGL_mem_adjointGroup_E6 {K K' : Type} [Field K] [Field K'] (ε : K →+* K')
    (g : adjointGroup .E6 K) : baseChangeGL ε (g : ModGL .E6 K) ∈ adjointGroup .E6 K' :=
  map_baseChangeGL_adjointGroup_le ε ⟨g, g.2, rfl⟩

@[expose] noncomputable def adjointGroupE6RingEquiv {K K' : Type} [Field K] [Field K']
    (ε : K ≃+* K') : adjointGroup .E6 K ≃* adjointGroup .E6 K' where
  toFun g := ⟨baseChangeGL (ε : K →+* K') g, baseChangeGL_mem_adjointGroup_E6 _ g⟩
  invFun g := ⟨baseChangeGL (ε.symm : K' →+* K) g, baseChangeGL_mem_adjointGroup_E6 _ g⟩
  left_inv g := by
    apply Subtype.ext
    change baseChangeGL (ε.symm : K' →+* K) (baseChangeGL (ε : K →+* K') (g : ModGL .E6 K)) = g
    rw [baseChangeGL_baseChangeGL]
    have h : ((ε.symm : K' →+* K).comp (ε : K →+* K')) = RingHom.id K := by
      ext c
      simp
    rw [h, baseChangeGL_id]
  right_inv g := by
    apply Subtype.ext
    change baseChangeGL (ε : K →+* K') (baseChangeGL (ε.symm : K' →+* K) (g : ModGL .E6 K')) = g
    rw [baseChangeGL_baseChangeGL]
    have h : ((ε : K →+* K').comp (ε.symm : K' →+* K)) = RingHom.id K' := by
      ext c
      simp
    rw [h, baseChangeGL_id]
  map_mul' g h := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul]

end Transport

section Setup


theorem hypothesisOne_quotient_center_E6 {G : Type} [Group G] {L : Subgroup G}
    (hZ : center L = ⊥) {f : ℕ} (hL : LieModel L .E6 0 2 f) : HypothesisOne (L ⧸ center L) :=
  hypothesisOne_of_mulEquiv (quotientCenterMulEquiv hZ).symm
    (exceptionalHypothesisOne L .E6 f (.inr (.inl rfl)) hL)

theorem lieModel_of_mulEquiv_E6 {G : Type} [Group G] {L : Subgroup G} {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) :
    LieModel L .E6 0 2 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  refine Or.inr (Or.inl ⟨by decide, by decide, ⟨Nat.prime_two, hf, rfl⟩, K, inferInstance,
    inferInstance, hK, ⟨e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .E6 K).symm⟩⟩)

theorem exists_e6Work_of_mulEquiv {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hstd : StandardSetting G L) (hZ : center L = ⊥) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e₀ : L ≃* adjointGroup .E6 K) :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (_ : CharP K₂ 2) (σ : K₂ ≃+* K₂),
      QuadraticFrobenius K₂ σ f ∧
        ∃ (_ : L ≃* adjointGroup .E6 (fixSubfield σ)) (t : G), F4Work L (fixSubfield σ) t f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  obtain ⟨K₂, _, _, _, σ, hK₂, hσ, hσc, hk⟩ := exists_quadraticFrobenius_F4 hf
  let := Fintype.ofFinite K
  let := Fintype.ofFinite (fixSubfield σ)
  have hc : Fintype.card K = Fintype.card (fixSubfield σ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hk]
  let e : L ≃* adjointGroup .E6 (fixSubfield σ) :=
    e₀.trans (adjointGroupE6RingEquiv (FiniteField.ringEquivOfCardEq hc))
  obtain ⟨t, ht, -, -, hKt, -⟩ := F4Pilot.kernel hstd hZ
    (hypothesisOne_quotient_center_E6 hZ (lieModel_of_mulEquiv_E6 hf hK e₀))
  exact ⟨K₂, inferInstance, inferInstance, inferInstance, σ, ⟨hK₂, hσ, hσc⟩, e, t,
    ⟨hstd, hZ, hf, hk, ht, hKt⟩⟩

theorem exists_e6Work {G : Type} [Group G] [Finite G] {L : Subgroup G} (hset : SeitzSetting G L)
    {f : ℕ} (hL : LieModel L .E6 0 2 f) :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (_ : CharP K₂ 2) (σ : K₂ ≃+* K₂),
      QuadraticFrobenius K₂ σ f ∧
        ∃ (_ : L ≃* adjointGroup .E6 (fixSubfield σ)) (t : G), F4Work L (fixSubfield σ) t f := by
  obtain ⟨hf, K, _, _, hK, ⟨e₀⟩⟩ := exists_mulEquiv_adjointQuotient_of_lieModel (.inr (.inl rfl)) hL
  exact exists_e6Work_of_mulEquiv hset.standardSetting hset.center_eq_bot hf hK
    (e₀.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .E6 K))

theorem seitzExclusion_highE6_of_forall
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
      [CharP K₂ 2] (σ : K₂ ≃+* K₂) (f : ℕ), QuadraticFrobenius K₂ σ f →
      ∀ (_ : L ≃* adjointGroup .E6 (fixSubfield σ)) (t : G),
      F4Work L (fixSubfield σ) t f → False) :
    SeitzExclusion (HighExceptional .E6) := by
  rintro G _ _ L hset ⟨f, hL⟩
  obtain ⟨K₂, _, _, _, σ, hq, e, t, hw⟩ := exists_e6Work hset hL
  exact h G L K₂ σ f hq e t hw

end Setup

end CFSG.SeitzReduction.E6Pilot
