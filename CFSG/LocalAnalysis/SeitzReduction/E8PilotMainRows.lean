module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainKinds
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainEnd
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotUniqueField
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCTField

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (QuadraticFrobenius mem_normalizer_conjugate_inv
  mem_normalizer_of_conjugate_inv_eq)
open E6Pilot (modelToG)


@[expose] def E8FieldNeighbourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
    [CharP K₂ 2] (σ : K₂ ≃+* K₂) (f : ℕ), QuadraticFrobenius K₂ σ f → 2 ≤ f →
    ∀ (e : L ≃* adjointGroup .E8 (fixSubfield σ)) (t : G), E8Work L (fixSubfield σ) t f →
    HR8FieldE8 e t f →
      Nonempty (E8Neighbour.high.levi K₂ ≃* neighbourCore e .high) ∧
        perfectCore (neighbourCore e .high ⊓ centralizer ({t} : Set G)) =
          modelToG e ((E8Neighbour.high.levi (fixSubfield σ)).map
            (adjointGroup .E8 (fixSubfield σ)).subtype)

@[expose] def E8FieldRowStep3Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
    [CharP K₂ 2] (σ : K₂ ≃+* K₂) (f : ℕ), QuadraticFrobenius K₂ σ f → 2 ≤ f →
    ∀ (e : L ≃* adjointGroup .E8 (fixSubfield σ)) (t : G), E8Work L (fixSubfield σ) t f →
    HR8FieldE8 e t f →
    ∀ Ψ : adjointGroup .E8 K₂ ≃* pieceSup e,
      (∀ x : adjointGroup .E8 (fixSubfield σ),
        ((Ψ (fixedFieldInclusion σ x) : pieceSup e) : G) = ((e.symm x : L) : G)) →
      ∀ h : G, t ∈ normalizer (conjugate (pieceSup e) h : Set G) →
        conjugate (pieceSup e) h ⊓ centralizer ({t} : Set G) = L →
          conjugate (pieceSup e) h = pieceSup e

section FieldRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K₂ : Type} [Field K₂] [Finite K₂]
  [CharP K₂ 2] {σ : K₂ ≃+* K₂} {f : ℕ}

theorem unique_of_step3_E8_field {K : Type} [Field K] (hset : StandardSetting G L)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₀ : Subgroup G}
    (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (e₀ : G₀ ≃* adjointGroup .E8 K₂)
    (h3 : ∀ h : G, t ∈ normalizer (conjugate G₀ h : Set G) →
      conjugate G₀ h ⊓ centralizer ({t} : Set G) = L → conjugate G₀ h = G₀) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G) := by
  intro g hg
  have htM := mem_normalizer_conjugate_inv hg
  exact mem_normalizer_of_conjugate_inv_eq
    (h3 g⁻¹ htM (inf_centralizer_conjugate_eq_E8_field hset hK e ht hKt hK₂ e₀ g⁻¹ htM))

theorem not_mem_centralizer_E8_field {K : Type} [Field K] (hset : StandardSetting G L)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₀ : Subgroup G}
    (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (e₀ : G₀ ≃* adjointGroup .E8 K₂) :
    t ∉ centralizer (G₀ : Set G) := by
  intro htC
  refine not_exists_inner_E8_field hset hK e ht hKt hK₂ e₀ ⟨1, one_mem _, fun x hx => ?_⟩
  rw [one_mul, inv_one, mul_one, ← mem_centralizer_iff.1 htC x hx, mul_inv_cancel_right]

theorem false_of_fieldRow_E8 (hFN : E8FieldNeighbourInput) (h3 : E8FieldRowStep3Input)
    (hq : QuadraticFrobenius K₂ σ f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .E8 (fixSubfield σ))
    {t : G} (hw : E8Work L (fixSubfield σ) t f) (hX : HR8FieldE8 e t f) : False := by
  obtain ⟨hψ, hfix⟩ := hFN G L K₂ σ f hq hf e t hw hX
  have h4 : 4 ≤ Nat.card (fixSubfield σ) := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨Ψ, hΨfix, -⟩ := exists_mulEquiv_fieldRow_of_neighbour hψ hw.mem_centralizer
    hw.orderOf_eq hq.orderOf_eq hfix h4
  have hKt := hw.inf_eq e
  have hLG : L ≤ pieceSup e := le_pieceSup_fieldRow_of_neighbour hψ hw.mem_centralizer
    hw.orderOf_eq hq.orderOf_eq hfix h4
  have htN : t ∈ normalizer (pieceSup e : Set G) := mem_normalizer_pieceSup hw.mem_centralizer
  have htG : t ∉ pieceSup e :=
    not_mem_E8_field hw.standard hw.card_eq e hw.orderOf_eq hKt hq.card_eq Ψ.symm
  have htC : t ∉ centralizer (pieceSup e : Set G) :=
    not_mem_centralizer_E8_field hw.standard hw.card_eq e hw.orderOf_eq hKt hq.card_eq Ψ.symm
  have hZ := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLG hw.orderOf_eq htN htC
  have huniq := unique_of_step3_E8_field hw.standard hw.card_eq e hw.orderOf_eq hKt hq.card_eq
    Ψ.symm (h3 G L K₂ σ f hq hf e t hw hX Ψ hΨfix)
  have := hw.seitz.1
  exact false_of_simple_of_E8_odd hZ hq.card_eq Ψ.symm htN hw.orderOf_eq htG huniq

end FieldRow

section SwapRow

theorem exists_mul_ne_mul_of_mulEquiv_adjointGroup_E8 {H : Type*} [Group H] {K : Type} [Field K]
    (e : H ≃* adjointGroup .E8 K) : ∃ a b : H, a * b ≠ b * a := by
  have := CFSG.LieType.Steinberg.Adjoint.isPerfect_e8 K
  have := CFSG.LieType.Steinberg.Adjoint.nontrivial_e8 K
  by_contra h
  refine Group.IsPerfect.not_isMulCommutative (adjointGroup .E8 K) ⟨⟨fun a b => ?_⟩⟩
  by_contra hab
  exact h ⟨e.symm a, e.symm b, fun h' => hab (e.symm.injective (by rw [map_mul, map_mul, h']))⟩

theorem isSimpleGroup_adjointGroup_E8 (K : Type) [Field K] : IsSimpleGroup (adjointGroup .E8 K) :=
  isSimpleGroup_of_isQuasisimple_of_center_eq_bot (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K)
    (center_adjointGroup_eq_bot_field .E8 K)

@[expose] def E8SwapRowCTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .E8 K) (t : G) (f : ℕ), E8Work L K t f → 2 ≤ f → HR8SwapE8 e t →
    ∃ G₁ : Subgroup G, Nonempty (G₁ ≃* adjointGroup .E8 K) ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSup e

@[expose] def E8SwapRowUniqueInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .E8 K) (t : G) (f : ℕ), E8Work L K t f → 2 ≤ f → HR8SwapE8 e t →
    ∀ G₁ : Subgroup G, Nonempty (G₁ ≃* adjointGroup .E8 K) →
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) →
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSup e →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer (pieceSup e : Set G) →
        g ∈ normalizer (pieceSup e : Set G)

theorem false_of_swapRow_E8 (hCT : E8SwapRowCTInput) (hU : E8SwapRowUniqueInput) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {t : G}
    {f : ℕ} (hw : E8Work L K t f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .E8 K)
    (hX : HR8SwapE8 e t) : False := by
  obtain ⟨G₁, ⟨e₁⟩, h₁₂, hsup⟩ := hCT G L K e t f hw hf hX
  have huniq := hU G L K e t f hw hf hX G₁ ⟨e₁⟩ h₁₂ hsup
  have := hw.seitz.1
  have hs₁ : IsSimpleGroup G₁ := by
    have := isSimpleGroup_adjointGroup_E8 K
    exact e₁.isSimpleGroup
  exact F4Pilot.false_of_simple_of_swap_of_isSimpleGroup hw.orderOf_eq hs₁
    (exists_mul_ne_mul_of_mulEquiv_adjointGroup_E8 e₁) h₁₂ rfl (by rw [hsup]; exact huniq)

end SwapRow

@[expose] def E8TwoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K]
    (_ : L ≃* adjointGroup .E8 K) (t : G), E8Work L K t 1 → False

end CFSG.SeitzReduction.E8Pilot
