module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainRows
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotHR8Setting

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.SeitzReduction.F4Pilot (QuadraticFrobenius exists_quadraticFrobenius_F4)

set_option linter.unusedSectionVars false

section Transport


theorem baseChangeGL_mem_adjointGroup_of_E7 {K K' : Type} [Field K] [Field K'] (ε : K →+* K')
    (g : adjointGroup .E7 K) : baseChangeGL ε (g : ModGL .E7 K) ∈ adjointGroup .E7 K' :=
  map_baseChangeGL_adjointGroup_le ε ⟨g, g.2, rfl⟩

@[expose] noncomputable def adjointGroupE7OfRingEquiv {K K' : Type} [Field K] [Field K']
    (ε : K ≃+* K') : adjointGroup .E7 K ≃* adjointGroup .E7 K' where
  toFun g := ⟨baseChangeGL (ε : K →+* K') g, baseChangeGL_mem_adjointGroup_of_E7 _ g⟩
  invFun g := ⟨baseChangeGL (ε.symm : K' →+* K) g, baseChangeGL_mem_adjointGroup_of_E7 _ g⟩
  left_inv g := by
    apply Subtype.ext
    change baseChangeGL (ε.symm : K' →+* K) (baseChangeGL (ε : K →+* K') (g : ModGL .E7 K)) = g
    rw [baseChangeGL_baseChangeGL]
    have h : ((ε.symm : K' →+* K).comp (ε : K →+* K')) = RingHom.id K := by
      ext c
      simp
    rw [h, baseChangeGL_id]
  right_inv g := by
    apply Subtype.ext
    change baseChangeGL (ε : K →+* K') (baseChangeGL (ε.symm : K' →+* K) (g : ModGL .E7 K')) = g
    rw [baseChangeGL_baseChangeGL]
    have h : ((ε : K →+* K').comp (ε.symm : K' →+* K)) = RingHom.id K' := by
      ext c
      simp
    rw [h, baseChangeGL_id]
  map_mul' g h := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul]

end Transport

structure E7Work {G : Type} [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] (t : G)
    (f : ℕ) : Prop where
  seitz : SeitzSetting G L
  one_le : 1 ≤ f
  card_eq : Nat.card K = 2 ^ f
  orderOf_eq : orderOf t = 2
  mem_centralizer : t ∈ centralizer (L : Set G)

theorem E7Work.standard {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
    {t : G} {f : ℕ} (h : E7Work L K t f) : StandardSetting G L :=
  h.seitz.standardSetting

section Kernel


theorem E7Work.inf_eq {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
    {t : G} {f : ℕ} (h : E7Work L K t f) (e : L ≃* adjointGroup .E7 K) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
  inf_centralizer_eq_zpowers_E7 h.seitz h.card_eq e h.mem_centralizer h.orderOf_eq

end Kernel

section Setup


theorem exists_e7Work {G : Type} [Group G] [Finite G] {L : Subgroup G} (hset : SeitzSetting G L)
    {f : ℕ} (hL : LieModel L .E7 0 2 f) :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (_ : CharP K₂ 2) (σ : K₂ ≃+* K₂),
      QuadraticFrobenius K₂ σ f ∧
        ∃ (_ : L ≃* adjointGroup .E7 (fixSubfield σ)) (t : G), E7Work L (fixSubfield σ) t f := by
  obtain ⟨hf, K, _, _, hK, ⟨e₀⟩⟩ :=
    exists_mulEquiv_adjointQuotient_of_lieModel (.inr (.inr (.inl rfl))) hL
  obtain ⟨K₂, _, _, _, σ, hK₂, hσ, hσc, hk⟩ := exists_quadraticFrobenius_F4 hf
  let := Fintype.ofFinite K
  let := Fintype.ofFinite (fixSubfield σ)
  have hc : Fintype.card K = Fintype.card (fixSubfield σ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hk]
  let e : L ≃* adjointGroup .E7 (fixSubfield σ) :=
    (e₀.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .E7 K)).trans
      (adjointGroupE7OfRingEquiv (FiniteField.ringEquivOfCardEq hc))
  obtain ⟨t, htC, ht⟩ := F4Pilot.exists_orderOf_eq_two_mem_centralizer hset.standardSetting
  exact ⟨K₂, inferInstance, inferInstance, inferInstance, σ, ⟨hK₂, hσ, hσc⟩, e, t,
    ⟨hset, hf, hk, ht, htC⟩⟩

theorem seitzExclusion_highE7_of_forall
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
      [CharP K₂ 2] (σ : K₂ ≃+* K₂) (f : ℕ), QuadraticFrobenius K₂ σ f →
      ∀ (_ : L ≃* adjointGroup .E7 (fixSubfield σ)) (t : G),
      E7Work L (fixSubfield σ) t f → False) :
    SeitzExclusion (HighExceptional .E7) := by
  rintro G _ _ L hset ⟨f, hL⟩
  obtain ⟨K₂, _, _, _, σ, hq, e, t, hw⟩ := exists_e7Work hset hL
  exact h G L K₂ σ f hq e t hw

end Setup

end CFSG.SeitzReduction.E7Pilot
