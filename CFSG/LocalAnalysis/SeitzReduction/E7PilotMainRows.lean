module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotMainLift
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotUniqueFieldStep3

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (QuadraticFrobenius mem_normalizer_conjugate_inv
  mem_normalizer_of_conjugate_inv_eq)
open E6Pilot (modelToG)


@[expose] def E7FieldRowFamilyInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
    [CharP K₂ 2] (σ : K₂ ≃+* K₂) (e : L ≃* adjointGroup .E7 (fixSubfield σ)) (t : G),
    Nonempty (E7Neighbour.high.levi K₂ ≃* neighbourCore e .high) →
    t ∈ centralizer (L : Set G) → orderOf t = 2 → orderOf σ = 2 →
    perfectCore (neighbourCore e .high ⊓ centralizer ({t} : Set G)) =
      modelToG e ((E7Neighbour.high.levi (fixSubfield σ)).map
        (adjointGroup .E7 (fixSubfield σ)).subtype) →
    4 ≤ Nat.card (fixSubfield σ) →
    ∃ φ : ∀ J, (adjDatumE7 K₂).leviAmalgam J →* G, IsCTFieldFamily e φ

section FieldRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K₂ : Type} [Field K₂] [Finite K₂]
  [CharP K₂ 2] {σ : K₂ ≃+* K₂} {f : ℕ}

theorem exists_mulEquiv_fieldRow_of_neighbour (hFam : E7FieldRowFamilyInput)
    (hq : QuadraticFrobenius K₂ σ f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .E7 (fixSubfield σ))
    {t : G} (hw : E7Work L (fixSubfield σ) t f) (hX : HR8FieldE7 e t f) :
    (∃ Ψ : adjointGroup .E7 K₂ ≃* pieceSup e,
      (∀ x : adjointGroup .E7 (fixSubfield σ),
        ((Ψ (fixedFieldInclusion σ x) : pieceSup e) : G) = ((e.symm x : L) : G)) ∧
      ∀ J : {J : Finset (Fin (adjDatumE7 K₂).rank) // J.card ≤ 2},
        (((adjDatumE7 K₂).leviAmalgam J).map Ψ.toMonoidHom).map (pieceSup e).subtype =
          pieceCore e J.1) ∧ L ≤ pieceSup e := by
  have h4 : 4 ≤ Nat.card (fixSubfield σ) := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨φ, hφ⟩ := hFam G L K₂ σ e t
    (nonempty_levi_high_mulEquiv_neighbourCore_high hw hf e hX K₂ hq.card_eq)
    hw.mem_centralizer hw.orderOf_eq hq.orderOf_eq
    (perfectCore_neighbourCore_high_inf_centralizer hw hf e) h4
  exact ⟨exists_mulEquiv_of_isCTFieldFamily hφ, le_pieceSup_of_isCTFieldFamily hφ⟩

theorem unique_of_step3_E7_field {K : Type} [Field K] (hset : StandardSetting G L)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₀ : Subgroup G}
    (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (e₀ : G₀ ≃* adjointGroup .E7 K₂)
    (h3 : ∀ h : G, t ∈ normalizer (conjugate G₀ h : Set G) →
      conjugate G₀ h ⊓ centralizer ({t} : Set G) = L → conjugate G₀ h = G₀) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G) := by
  intro g hg
  have htM := mem_normalizer_conjugate_inv hg
  exact mem_normalizer_of_conjugate_inv_eq
    (h3 g⁻¹ htM (inf_centralizer_conjugate_eq_E7_field hset hK e ht hKt hK₂ e₀ g⁻¹ htM))

theorem not_mem_centralizer_E7_field {K : Type} [Field K] (hset : StandardSetting G L)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₀ : Subgroup G}
    (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (e₀ : G₀ ≃* adjointGroup .E7 K₂) :
    t ∉ centralizer (G₀ : Set G) := by
  intro htC
  refine not_exists_inner_E7_field hset hK e ht hKt hK₂ e₀ ⟨1, one_mem _, fun x hx => ?_⟩
  rw [one_mul, inv_one, mul_one, ← mem_centralizer_iff.1 htC x hx, mul_inv_cancel_right]

theorem false_of_fieldRow_E7 (hFam : E7FieldRowFamilyInput) (hq : QuadraticFrobenius K₂ σ f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .E7 (fixSubfield σ)) {t : G}
    (hw : E7Work L (fixSubfield σ) t f) (hX : HR8FieldE7 e t f) : False := by
  obtain ⟨⟨Ψ, hΨfix, -⟩, hLG⟩ := exists_mulEquiv_fieldRow_of_neighbour hFam hq hf e hw hX
  have hKt := hw.inf_eq e
  have htN : t ∈ normalizer (pieceSup e : Set G) := mem_normalizer_pieceSup hw.mem_centralizer
  have htG : t ∉ pieceSup e :=
    not_mem_E7_field hw.standard hw.card_eq e hw.orderOf_eq hKt hq.card_eq Ψ.symm
  have htC : t ∉ centralizer (pieceSup e : Set G) :=
    not_mem_centralizer_E7_field hw.standard hw.card_eq e hw.orderOf_eq hKt hq.card_eq Ψ.symm
  have hZ := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLG hw.orderOf_eq htN htC
  have huniq := unique_of_step3_E7_field hw.standard hw.card_eq e hw.orderOf_eq hKt hq.card_eq
    Ψ.symm fun h htM hML => eq_of_conjugate_pieceSup_E7_field hw.standard hq.card_eq hw.card_eq e
      hw.orderOf_eq hw.mem_centralizer hKt Ψ hΨfix h htM hML
  have := hw.seitz.1
  exact false_of_simple_of_E7_odd hZ hq.card_eq Ψ.symm htN hw.orderOf_eq htG huniq

end FieldRow

section SwapRow

theorem isSimpleGroup_adjointGroup_E7 (K : Type) [Field K] [Finite K] :
    IsSimpleGroup (adjointGroup .E7 K) :=
  isSimpleGroup_of_isQuasisimple_of_center_eq_bot
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K)
    (center_adjointGroup_eq_bot_field .E7 K)

theorem exists_mul_ne_mul_of_mulEquiv_adjointGroup_E7 {H : Type*} [Group H] {K : Type} [Field K]
    [Finite K] (e : H ≃* adjointGroup .E7 K) : ∃ a b : H, a * b ≠ b * a := by
  have : Group.IsPerfect (adjointGroup .E7 K) :=
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K).1
  have := (isSimpleGroup_adjointGroup_E7 K).toNontrivial
  by_contra h
  refine Group.IsPerfect.not_isMulCommutative (adjointGroup .E7 K) ⟨⟨fun a b => ?_⟩⟩
  by_contra hab
  exact h ⟨e.symm a, e.symm b, fun h' => hab (e.symm.injective (by rw [map_mul, map_mul, h']))⟩

@[expose] def E7SwapRowCTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .E7 K) (t : G) (f : ℕ), E7Work L K t f → 2 ≤ f → HR8SwapE7 e t →
    ∃ G₁ : Subgroup G, Nonempty (G₁ ≃* adjointGroup .E7 K) ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSup e

@[expose] def E7SwapRowUniqueInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .E7 K) (t : G) (f : ℕ), E7Work L K t f → 2 ≤ f → HR8SwapE7 e t →
    ∀ G₁ : Subgroup G, Nonempty (G₁ ≃* adjointGroup .E7 K) →
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) →
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom = pieceSup e →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer (pieceSup e : Set G) →
        g ∈ normalizer (pieceSup e : Set G)

theorem false_of_swapRow_E7 (hCT : E7SwapRowCTInput) (hU : E7SwapRowUniqueInput) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {t : G}
    {f : ℕ} (hw : E7Work L K t f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .E7 K)
    (hX : HR8SwapE7 e t) : False := by
  obtain ⟨G₁, ⟨e₁⟩, h₁₂, hsup⟩ := hCT G L K e t f hw hf hX
  have huniq := hU G L K e t f hw hf hX G₁ ⟨e₁⟩ h₁₂ hsup
  have := hw.seitz.1
  have hs₁ : IsSimpleGroup G₁ := by
    have := isSimpleGroup_adjointGroup_E7 K
    exact e₁.isSimpleGroup
  exact F4Pilot.false_of_simple_of_swap_of_isSimpleGroup hw.orderOf_eq hs₁
    (exists_mul_ne_mul_of_mulEquiv_adjointGroup_E7 e₁) h₁₂ rfl (by rw [hsup]; exact huniq)

end SwapRow

@[expose] def E7TwoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K]
    (_ : L ≃* adjointGroup .E7 K) (t : G), E7Work L K t 1 → False

end CFSG.SeitzReduction.E7Pilot
