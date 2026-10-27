module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotKernel
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamilies
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4ClassDescent
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6Hom
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LieType.Chevalley.LangActualInvolutionReduction

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)

section Transport


theorem baseChangeGL_mem_adjointGroup_F4 {K K' : Type} [Field K] [Field K'] (ε : K →+* K')
    (g : adjointGroup .F4 K) : baseChangeGL ε (g : ModGL .F4 K) ∈ adjointGroup .F4 K' :=
  map_baseChangeGL_adjointGroup_le ε ⟨g, g.2, rfl⟩

@[expose] noncomputable def adjointGroupF4RingEquiv {K K' : Type} [Field K] [Field K']
    (ε : K ≃+* K') : adjointGroup .F4 K ≃* adjointGroup .F4 K' where
  toFun g := ⟨baseChangeGL (ε : K →+* K') g, baseChangeGL_mem_adjointGroup_F4 _ g⟩
  invFun g := ⟨baseChangeGL (ε.symm : K' →+* K) g, baseChangeGL_mem_adjointGroup_F4 _ g⟩
  left_inv g := by
    apply Subtype.ext
    change baseChangeGL (ε.symm : K' →+* K) (baseChangeGL (ε : K →+* K') (g : ModGL .F4 K)) = g
    rw [baseChangeGL_baseChangeGL]
    have h : ((ε.symm : K' →+* K).comp (ε : K →+* K')) = RingHom.id K := by
      ext c
      simp
    rw [h, baseChangeGL_id]
  right_inv g := by
    apply Subtype.ext
    change baseChangeGL (ε : K →+* K') (baseChangeGL (ε.symm : K' →+* K) (g : ModGL .F4 K')) = g
    rw [baseChangeGL_baseChangeGL]
    have h : ((ε : K →+* K').comp (ε.symm : K' →+* K)) = RingHom.id K' := by
      ext c
      simp
    rw [h, baseChangeGL_id]
  map_mul' g h := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul]

end Transport

theorem exists_quadraticFrobenius_F4 {f : ℕ} (hf : 1 ≤ f) :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (_ : CharP K₂ 2) (σ : K₂ ≃+* K₂),
      Nat.card K₂ = 2 ^ (2 * f) ∧ orderOf σ = 2 ∧ (∀ c, σ c = c ^ 2 ^ f) ∧
        Nat.card (fixSubfield σ) = 2 ^ f := by
  have hcard : Nat.card (GaloisField 2 (2 * f)) = 2 ^ (2 * f) := GaloisField.card 2 (2 * f) (by omega)
  have hcard' : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [hcard, ← pow_mul, mul_comm]
  obtain ⟨σ, hσ, hinv, hfix⟩ :=
    CFSG.RankTwoShapes.exists_quadraticFrobenius (GaloisField 2 (2 * f)) f (by omega) hcard'
  have hfix' : Nat.card (fixSubfield σ) = 2 ^ f := by
    rw [← hfix]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  have hσσ : σ * σ = 1 := RingEquiv.ext fun c => hinv c
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hmem : ∀ c : GaloisField 2 (2 * f), c ∈ fixSubfield σ := fun c => by
      change σ c = c
      rw [h1]
      rfl
    have htop : Nat.card (fixSubfield σ) = Nat.card (GaloisField 2 (2 * f)) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hmem)
    rw [hfix', hcard] at htop
    have : 2 ^ f < 2 ^ (2 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  refine ⟨GaloisField 2 (2 * f), inferInstance, inferInstance, inferInstance, σ, hcard,
    orderOf_eq_prime (by rw [sq, hσσ]) hσ1, hσ, hfix'⟩

structure F4Work {G : Type} [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] (t : G)
    (f : ℕ) : Prop where
  standard : StandardSetting G L
  center_eq_bot : center L = ⊥
  one_le : 1 ≤ f
  card_eq : Nat.card K = 2 ^ f
  orderOf_eq : orderOf t = 2
  inf_eq : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t

theorem F4Work.mem_centralizer {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type}
    [Field K] {t : G} {f : ℕ} (h : F4Work L K t f) : t ∈ centralizer (L : Set G) := by
  have : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := h.inf_eq ▸ mem_zpowers t
  exact this.1

section Setup


theorem hypothesisOne_quotient_center_F4 {G : Type} [Group G] {L : Subgroup G}
    (hZ : center L = ⊥) {K : Type} [Field K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : L ≃* adjointGroup .F4 K) : HypothesisOne (L ⧸ center L) :=
  hypothesisOne_of_mulEquiv ((quotientCenterMulEquiv hZ).trans e).symm
    (hypothesisOne_F4_of_inner hf K hK (innerInvolutionInput_F4' hf hK))

theorem exists_f4Work {G : Type} [Group G] [Finite G] {L : Subgroup G} (hset : SeitzSetting G L)
    {f : ℕ} (hL : LieModel L .F4 0 2 f) :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Finite K₂) (_ : CharP K₂ 2) (σ : K₂ ≃+* K₂),
      Nat.card K₂ = 2 ^ (2 * f) ∧ orderOf σ = 2 ∧ (∀ c, σ c = c ^ 2 ^ f) ∧
        ∃ (_ : L ≃* adjointGroup .F4 (fixSubfield σ)) (t : G), F4Work L (fixSubfield σ) t f := by
  obtain ⟨hf, K, _, _, hK, ⟨e₀⟩⟩ := exists_mulEquiv_adjointQuotient_of_lieModel (.inl rfl) hL
  obtain ⟨K₂, _, _, _, σ, hK₂, hσ, hσc, hk⟩ := exists_quadraticFrobenius_F4 hf
  let := Fintype.ofFinite K
  let := Fintype.ofFinite (fixSubfield σ)
  have hc : Fintype.card K = Fintype.card (fixSubfield σ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hk]
  let e : L ≃* adjointGroup .F4 (fixSubfield σ) :=
    (e₀.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .F4 K)).trans
      (adjointGroupF4RingEquiv (FiniteField.ringEquivOfCardEq hc))
  have hZ := hset.center_eq_bot
  have hstd := hset.standardSetting
  obtain ⟨t, ht, -, -, hKt, -⟩ := kernel hstd hZ (hypothesisOne_quotient_center_F4 hZ hf hk e)
  exact ⟨K₂, inferInstance, inferInstance, inferInstance, σ, hK₂, hσ, hσc, e, t,
    ⟨hstd, hZ, hf, hk, ht, hKt⟩⟩

theorem seitzExclusion_highF4_of_forall
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
      [CharP K₂ 2] (σ : K₂ ≃+* K₂) (f : ℕ), Nat.card K₂ = 2 ^ (2 * f) → orderOf σ = 2 →
      (∀ c, σ c = c ^ 2 ^ f) → ∀ (_ : L ≃* adjointGroup .F4 (fixSubfield σ)) (t : G),
      F4Work L (fixSubfield σ) t f → False) :
    SeitzExclusion (HighExceptional .F4) := by
  rintro G _ _ L hset ⟨f, hL⟩
  obtain ⟨K₂, _, _, _, σ, hK₂, hσ, hσc, e, t, hw⟩ := exists_f4Work hset hL
  exact h G L K₂ σ f hK₂ hσ hσc e t hw

end Setup

end CFSG.SeitzReduction.F4Pilot
