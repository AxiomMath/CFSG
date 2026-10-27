module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainKinds
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapF4
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4TwoRoot
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndFieldBasic

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)

structure QuadraticFrobenius (K₂ : Type) [Field K₂] (σ : K₂ ≃+* K₂) (f : ℕ) : Prop where
  card_eq : Nat.card K₂ = 2 ^ (2 * f)
  orderOf_eq : orderOf σ = 2
  apply_eq : ∀ c, σ c = c ^ 2 ^ f

section Span

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def pieceSpan (e : L ≃* adjointGroup .F4 K) : Subgroup G :=
  ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, pieceCore e J.1

end Span

section Field

@[expose] def FieldNeighbourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
    [CharP K₂ 2] (σ : K₂ ≃+* K₂) (f : ℕ), QuadraticFrobenius K₂ σ f → 2 ≤ f →
    ∀ (e : L ≃* adjointGroup .F4 (fixSubfield σ)) (t : G), F4Work L (fixSubfield σ) t f →
    ∀ N : AmalgamNeighbour, N ≠ .X' → HR8Kind e t f N .field →
      Nonempty (N.levi K₂ ≃* neighbourCore e N) ∧
        perfectCore (neighbourCore e N ⊓ centralizer ({t} : Set G)) =
          modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .F4 (fixSubfield σ)).subtype)

@[expose] def FieldRowUniqueInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
    [CharP K₂ 2] (σ : K₂ ≃+* K₂) (f : ℕ), QuadraticFrobenius K₂ σ f → 2 ≤ f →
    ∀ (e : L ≃* adjointGroup .F4 (fixSubfield σ)) (t : G), F4Work L (fixSubfield σ) t f →
    HR8Kind e t f .X .field → HR8Kind e t f .Y .field →
    ∀ ψ : adjointGroup .F4 K₂ →* G, Function.Injective ψ → ψ.range = pieceSpan e →
      (∀ x : adjointGroup .F4 (fixSubfield σ), ψ (fixedFieldInclusion σ x) = ((e.symm x : L) : G)) →
      (∀ h : G, t ∈ normalizer (conjugate (pieceSpan e) h : Set G) →
        conjugate (pieceSpan e) h ⊓ centralizer ({t} : Set G) = L →
          conjugate (pieceSpan e) h = pieceSpan e) ∧
        centralizer (pieceSpan e : Set G) = ⊥

end Field

section Conj

variable {G : Type} [Group G]

theorem conjugate_inv_eq_map (M : Subgroup G) (g : G) :
    conjugate M g⁻¹ = M.map (MulAut.conj g).toMonoidHom := by
  simp only [conjugate, inv_inv]

theorem mem_normalizer_conjugate_inv {M : Subgroup G} {g t : G}
    (h : g⁻¹ * t * g ∈ normalizer (M : Set G)) : t ∈ normalizer (conjugate M g⁻¹ : Set G) := by
  rw [conjugate_inv_eq_map, ← map_equiv_normalizer_eq]
  refine ⟨g⁻¹ * t * g, h, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem mem_normalizer_of_conjugate_inv_eq {M : Subgroup G} {g : G}
    (h : conjugate M g⁻¹ = M) : g ∈ normalizer (M : Set G) := by
  rw [conjugate_inv_eq_map] at h
  exact mem_normalizer_iff_map_conj_eq.2 h

end Conj

section FieldRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K₂ : Type} [Field K₂] [Finite K₂]
  [CharP K₂ 2] {σ : K₂ ≃+* K₂} {f : ℕ}

omit [Finite K₂] [CharP K₂ 2] in
theorem unique_of_step3_F4_field {K : Type} [Field K] (hset : StandardSetting G L)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {G₀ : Subgroup G}
    (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (e₀ : G₀ ≃* adjointGroup .F4 K₂)
    (h3 : ∀ h : G, t ∈ normalizer (conjugate G₀ h : Set G) →
      conjugate G₀ h ⊓ centralizer ({t} : Set G) = L → conjugate G₀ h = G₀) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G) := by
  intro g hg
  have htM := mem_normalizer_conjugate_inv hg
  exact mem_normalizer_of_conjugate_inv_eq
    (h3 g⁻¹ htM (inf_centralizer_conjugate_eq_F4_field hset hK e htC ht hK₂ e₀ g⁻¹ htM))

end FieldRow

section SwapRow

@[expose] def SwapRowCTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    HR8Kind e t f .X .swap → HR8Kind e t f .Y .swap →
    ∃ G₁ : Subgroup G, Nonempty (G₁ ≃* adjointGroup .F4 K) ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSpan e

@[expose] def SwapRowUniqueInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
    HR8Kind e t f .X .swap → HR8Kind e t f .Y .swap →
    ∀ G₁ : Subgroup G, Nonempty (G₁ ≃* adjointGroup .F4 K) →
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) →
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSpan e →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer (pieceSpan e : Set G) →
        g ∈ normalizer (pieceSpan e : Set G)

theorem false_of_swapRow (hCT : SwapRowCTInput) (hU : SwapRowUniqueInput) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {t : G} {f : ℕ}
    (hw : F4Work L K t f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K)
    (hX : HR8Kind e t f .X .swap) (hY : HR8Kind e t f .Y .swap) : False := by
  obtain ⟨G₁, ⟨e₁⟩, h₁₂, hsup⟩ := hCT G L K e t f hw hf hX hY
  have huniq := hU G L K e t f hw hf hX hY G₁ ⟨e₁⟩ h₁₂ hsup
  have := hw.standard.simple
  exact false_of_simple_of_swap_F4 hw.orderOf_eq hw.one_le hw.card_eq e₁ h₁₂ rfl
    (by rw [hsup]; exact huniq)

end SwapRow

section E6Row

@[expose] def E6RowKinds {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ) : Prop :=
  (HR8Kind e t f .X .linear6 ∧ HR8Kind e t f .Y .omegaPlus8) ∨
    (HR8Kind e t f .X .omegaPlus8 ∧ HR8Kind e t f .Y .linear6)

@[expose] def E6RowCTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f → E6RowKinds e t f →
    ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = 2 ^ f ∧
      ∃ (e₆ : pieceSpan e ≃* adjointGroup Tag.E6 K') (htN : t ∈ normalizer (pieceSpan e : Set G))
        (φ : MulAut (adjointGroup Tag.E6 K')) (g : adjointGroup Tag.E6 K')
        (a : Fin Tag.E6.rank → K'ˣ) (σ' : K' ≃+* K'),
        φ * normalizerMulAut e₆ ⟨t, htN⟩ * φ⁻¹ = MulAut.conj g * exactNormalAut Tag.E6 K' a σ' 1

end E6Row

section TwistedE6Row

@[expose] def TwistedE6RowKinds {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ) : Prop :=
  (HR8Kind e t f .X .unitary6 ∧ HR8Kind e t f .Y .omegaMinus8) ∨
    (HR8Kind e t f .X .omegaMinus8 ∧ HR8Kind e t f .Y .unitary6)

end TwistedE6Row

section Two

@[expose] noncomputable def subgroupToG {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    (e : L ≃* adjointGroup .F4 K) (H : Subgroup (adjointGroup .F4 K)) : Subgroup G :=
  (H.map e.symm.toMonoidHom).map L.subtype

@[expose] def TwoRowsInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 →
    ∀ (htX : t ∈ centralizer (subgroupToG e X₀ : Set G)) (κ : Sp6Kind),
      NeighbourOvergroupKind
        (QuotientGroup.mk' (oddCore (centralizer (subgroupToG e X₀ : Set G))) ⟨t, htX⟩)
        (((subgroupToG e (C3Levi K)).subgroupOf (centralizer (subgroupToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (subgroupToG e X₀ : Set G))))) 1 κ → False

theorem false_of_two (hcat : Sp6CatalogueClauses) (h2 : TwoRowsInput) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {t : G}
    (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K) : False := by
  obtain ⟨X₀, hXJ₀, hcyc, hX₀⟩ := exists_nonsplit_le_subgroupOf_highestRootRankOne (K := K)
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have hX₀3 : Nat.card X₀ = 3 := by rw [hX₀, hK2]
  have htX : t ∈ centralizer (subgroupToG e X₀ : Set G) :=
    centralizer_le (map_subtype_le _) hw.mem_centralizer
  have hnn := not_normal_map_oddCore_nonsplit_of_card_eq_two hw.standard hK2 e hw.orderOf_eq
    hw.inf_eq hXJ₀ hX₀3 rfl rfl
  have hNO := neighbour_overgroup_nonsplit_of_not_normal hcat hw.standard hw.card_eq e
    hw.orderOf_eq hw.inf_eq hXJ₀ hcyc hX₀ rfl htX rfl hnn
  obtain ⟨κ, hκ⟩ := exists_neighbourOvergroupKind hNO
  exact h2 G L K e t hw X₀ hXJ₀ hcyc hX₀3 htX κ hκ

end Two

end CFSG.SeitzReduction.F4Pilot
