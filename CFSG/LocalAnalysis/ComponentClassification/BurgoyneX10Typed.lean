module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Ord
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

@[expose] def ExcCompModel (p : ℕ) (L : Type) [Group L] : Prop :=
  ∃ (τ' : StatedLieTag) (n' f' : ℕ), ExcCompTag τ' n' ∧ StatedLieAdmissible τ' n' p f' ∧
    LieModel (L ⧸ center L) τ' n' p f'

theorem ExcCompModel.of_centerQuotient_equiv {p : ℕ} {L M : Type} [Group L] [Group M]
    (e : L ⧸ center L ≃* M ⧸ center M) (h : ExcCompModel p M) : ExcCompModel p L := by
  obtain ⟨τ', n', f', ht, hadm, hM⟩ := h
  exact ⟨τ', n', f', ht, hadm, LieType.CurtisTits.lieModel_of_mulEquiv e.symm hM⟩

theorem ExcCompModel.of_mulEquiv {p : ℕ} {L M : Type} [Group L] [Group M] (e : L ≃* M)
    (h : ExcCompModel p M) : ExcCompModel p L :=
  h.of_centerQuotient_equiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))

theorem excCompModel_of_component_equiv {X Y : Type} [Group X] [Group Y] (Φ : X ≃* Y) {p : ℕ}
    (h : ∀ M : Subgroup Y, IsComponent M → ExcCompModel p M) {L : Subgroup X}
    (hL : IsComponent L) : ExcCompModel p L :=
  (h _ (LocalCores.isComponent_map_mulEquiv Φ hL)).of_mulEquiv
    (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)

theorem ExcCompModel.noPSp4 (hO : LieOrderFormulasInput) {p : ℕ} (hp2 : p ≠ 2) {L : Type}
    [Group L] (h : ExcCompModel p L) : NoPSp4 p L := by
  obtain ⟨τ', n', f', ht, hadm, hL⟩ := h
  exact noPSp4_of_lieModel hO hp2 ht hadm hL

theorem excCompModel_of_equiv_psl_two {M : Type} [Group M] {F : Type} [Field F] [Finite F]
    {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hF : Nat.card F = p ^ e) (hF2 : Nat.card F ≠ 2)
    (hF3 : Nat.card F ≠ 3) (E : M ⧸ center M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    ExcCompModel p M := by
  have hadm : StatedLieAdmissible .PSL 2 p e :=
    ⟨hp, he, le_rfl, fun h => hF2 (hF.trans (Prod.mk.inj h).2),
      fun h => hF3 (hF.trans (Prod.mk.inj h).2)⟩
  exact ⟨.PSL, 2, e, Or.inl ⟨rfl, Or.inl rfl⟩, hadm, LieType.CurtisTits.lieModel_of_mulEquiv E.symm
    (Or.inl ⟨by decide, ⟨hadm, F, inferInstance, inferInstance, hF,
      ⟨projectiveSpecialLinearGroupEquivStatedProj 2 F⟩⟩⟩)⟩

theorem excCompModel_of_simple_model {L Y : Type} [Group L] [Group Y] [IsSimpleGroup Y]
    (hnab : ∃ a b : Y, a * b ≠ b * a) (E : L ≃* Y) {t : StatedLieTag} {n p e : ℕ}
    (hadm : StatedLieAdmissible t n p e) (hY : LieModel Y t n p e)
    (ht : ExcCompTag t n := by unfold ExcCompTag; decide) : ExcCompModel p L := by
  have hZ : center Y = ⊥ := ExcSelector.center_eq_bot_of_isSimpleGroup' hnab
  exact ExcCompModel.of_mulEquiv E ⟨t, n, e, ht, hadm, LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hY⟩

theorem excCompTag_of_untwisted {t : StatedLieTag} {τ : Tag}
    (htτ : t = .G2 ∧ τ = .G2 ∨ t = .F4 ∧ τ = .F4 ∨ t = .E6 ∧ τ = .E6 ∨ t = .E7 ∧ τ = .E7 ∨
      t = .E8 ∧ τ = .E8) : ExcCompTag t 0 := by
  rcases htτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    (unfold ExcCompTag; decide)

variable {K : Type} [Field K] [Finite K]

theorem excCompModel_odd_field
    {t : StatedLieTag} {τ : Tag}
    (htτ : t = .G2 ∧ τ = .G2 ∨ t = .F4 ∧ τ = .F4 ∨ t = .E6 ∧ τ = .E6 ∨ t = .E7 ∧ τ = .E7 ∨
      t = .E8 ∧ τ = .E8) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup α) {L : Subgroup X}
    (hL : IsComponent L) : ExcCompModel p L := by
  obtain ⟨E⟩ := odd_field_component_equiv hp hp2 he hKe δ hδ hαg hα Ψ hL
  have hk := card_fixSubfield_of_sq_pow hp he hKe δ hδ
  have h3 := three_le_pow_of_odd_prime hp hp2 he
  have hadm : StatedLieAdmissible t 0 p e := by
    rcases htτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨hp, he, rfl, h3⟩
    all_goals exact ⟨hp, he, rfl⟩
  exact ⟨t, 0, e, excCompTag_of_untwisted htτ, hadm,
    lieModel_centralQuotient_of_mulEquiv_adjointGroup htτ hadm hk E⟩

theorem excCompModel_graphFixedRootGroup_E6
    {M : Type} [Field M] [Finite M] {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hM : Nat.card M = (p ^ e) ^ 2) (σ : M ≃+* M) (hσ : ∀ c, σ c = c ^ (p ^ e)) :
    ExcCompModel p (graphFixedRootGroup TwistTag.E6 M σ.toRingHom) := by
  have hperf := (finite_fixed_root_group_perfect TwistTag.E6 hp he M hM σ.toRingHom hσ).2.2.1
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 M σ
  obtain ⟨e'⟩ := LieType.Chevalley.nonempty_derivedCentralQuotient_equiv hperf hZ
  have hadm : StatedLieAdmissible .twistedE6 0 p e := ⟨hp, he, rfl⟩
  exact ⟨.twistedE6, 0, e, by unfold ExcCompTag; decide, hadm, Or.inr (Or.inl ⟨rfl, by decide,
    hadm, M, inferInstance, inferInstance, hM, σ.toRingHom, hσ,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e'.symm⟩⟩)⟩

theorem excCompModel_reeGamma_G2
    [CharP K ReeTag.G2.prime] {b : ℕ} (hb : 1 ≤ b) (hK : Nat.card K = 3 ^ (2 * b + 1)) :
    ExcCompModel 3 (ReeTag.G2.reeGamma K b) := by
  have hZ := ReeTag.center_reeGamma_G2_eq_bot hK
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2 hb hK
  have hadm : StatedLieAdmissible .twistedG2 0 3 (2 * b + 1) :=
    ⟨Nat.prime_three, by omega, rfl, rfl, ⟨b, rfl⟩, by omega⟩
  have hfx : reeFixedGroup .G2 K reeG2Perm
      (fun i => if i ∈ reeG2Long then 3 ^ b else 3 ^ (b + 1)) = ReeTag.G2.reeGamma K b :=
    (ReeTag.reeGamma_eq_reeFixedGroup (t := ReeTag.G2) (K := K) (a := b)).symm
  let eC : DerivedCentralQuotient (reeFixedGroup .G2 K reeG2Perm
      (fun i => if i ∈ reeG2Long then 3 ^ b else 3 ^ (b + 1))) ≃*
      DerivedCentralQuotient (ReeTag.G2.reeGamma K b) :=
    QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (by rw [hfx]; rfl))
      (Subgroup.map_center_eq _)
  let e' := ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
    (E.symm.trans eC.symm)
  exact ⟨.twistedG2, 0, 2 * b + 1, by unfold ExcCompTag; decide, hadm, Or.inr (Or.inr (Or.inl
    ⟨rfl, by decide, hadm, b, rfl, K, inferInstance, inferInstance, hK, ⟨e'⟩⟩))⟩

@[expose] def ExcInnerModel (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) → orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → ExcCompModel p L

@[expose] def E6GraphModel : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup TwistTag.E6.tag K)) (g : adjointGroup TwistTag.E6.tag K)
      (a : Fin TwistTag.E6.tag.rank → Kˣ),
      (∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
        (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
          diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) *
            (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
              (g : ModGL TwistTag.E6.tag K)⁻¹) → orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → ExcCompModel p L

@[expose] def ExcFamilyModel (t : StatedLieTag) : Prop :=
  ∀ (J : Type) [Group J] (n p f : ℕ), p.Prime → p ≠ 2 →
    StatedLieAdmissible t n p f → LieModel J t n p f →
    ∀ α : MulAut J, orderOf α = 2 → ∀ K : Subgroup (fixedSubgroup α), IsComponent K →
      ExcCompModel p K ∨
        (p = 3 ∧ LieModel J .G2 0 3 1 ∧ α ∉ (MulAut.conj : J →* MulAut J).range ∧
          LieModel K .PSL 2 2 3)

theorem excFamilyModel_of_explicit
    {t : StatedLieTag} {τ : Tag} (ht : t ∈ chevalleyExceptionalTags)
    (hmodel : ∀ (J : Type) [Group J] (p f : ℕ), ChevalleyExceptionalModel J t p f →
      UntwistedChevalleyModel J τ (p ^ f))
    (hexp : ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
      Nat.card K = p ^ f → ∀ β : MulAut (adjointGroup τ K), orderOf β = 2 →
        ∀ (X : Type) [Group X], (X ≃* fixedSubgroup β) → ∀ L : Subgroup X, IsComponent L →
          ExcCompModel p L) :
    ExcFamilyModel t := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ
    (hmodel J p f (GH74.chevalleyExceptionalModel_of_lieModel ht hm))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact Or.inl (hexp F p f hp hp2 hadm.2.1 hF _ hβ _ (fixedSubgroupCongrEquiv e α) Kc hKc)

theorem noPSp4_of_lieModel_psl_two_two_three (hO : LieOrderFormulasInput) {L : Type} [Group L]
    (h : LieModel L .PSL 2 2 3) : NoPSp4 3 L := by
  have hadm : StatedLieAdmissible .PSL 2 2 3 := by
    refine ⟨Nat.prime_two, by norm_num, le_rfl, ?_, ?_⟩ <;> decide
  obtain ⟨hfin, hord, -⟩ := hO L .PSL 2 2 3 hadm h
  have h1 : lieOrderDivisor .PSL 2 (2 ^ 3) = 1 := by decide
  have h2 : lieOrderNumerator .PSL 2 (2 ^ 3) = 504 := by decide
  rw [h1, h2, mul_one] at hord
  exact noPSp4_of_card_le hO Nat.prime_three (by decide) hord.le

end CFSG.ComponentClassification.Burgoyne.X10
