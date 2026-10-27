module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenExc
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeFixedPoints
public import CFSG.LieType.AlgebraicGroups.OddG2F4E8InvolutionCases
public import CFSG.LieType.Chevalley.CoordinateFieldFixedOddComponents
public import CFSG.LieType.Chevalley.GraphFixedOddComponents
public import CFSG.LieType.Chevalley.LangQuadraticFieldCosetConjugacy
public import CFSG.LieType.Ree.G2ExceptionalCosetInvolutions

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

@[expose] def OddLieCentralQuotient (p : ℕ) (L : Type) [Group L] : Prop :=
  ∃ (τ' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible τ' n' p f' ∧
    Blueprint.LieModel (L ⧸ center L) τ' n' p f'

theorem oddLieCentralQuotient_of_mulEquiv {p : ℕ} {L L' : Type} [Group L] [Group L']
    (e : L ≃* L') (h : OddLieCentralQuotient p L') : OddLieCentralQuotient p L := by
  obtain ⟨τ', n', f', hadm, hL⟩ := h
  exact ⟨τ', n', f', hadm, LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm hL⟩

theorem oddLieCentralQuotient_of_component_equiv {X Y : Type} [Group X] [Group Y] (Φ : X ≃* Y)
    {p : ℕ} (h : ∀ M : Subgroup Y, IsComponent M → OddLieCentralQuotient p M) {L : Subgroup X}
    (hL : IsComponent L) : OddLieCentralQuotient p L :=
  oddLieCentralQuotient_of_mulEquiv (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)
    (h _ (LocalCores.isComponent_map_mulEquiv Φ hL))

theorem nonempty_component_equiv_of_unique {X G : Type*} [Group X] [Group G] {F J : Subgroup G}
    (Ψ : X ≃* F) (hJ : ∀ M : Subgroup G, Assembly.IsComponentOf M F → M = J) {L : Subgroup X}
    (hL : IsComponent L) : Nonempty (L ≃* J) := by
  have hL' : IsComponent (L.map Ψ.toMonoidHom) := LocalCores.isComponent_map_mulEquiv Ψ hL
  have hMF : (L.map Ψ.toMonoidHom).map F.subtype ≤ F := Subgroup.map_subtype_le _
  have hMs : ((L.map Ψ.toMonoidHom).map F.subtype).subgroupOf F = L.map Ψ.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective F.subtype_injective _
  have hMc : Assembly.IsComponentOf ((L.map Ψ.toMonoidHom).map F.subtype) F :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hMF).2
      (by rw [hMs]; exact hL')
  exact ⟨((L.equivMapOfInjective Ψ.toMonoidHom Ψ.injective).trans
    ((L.map Ψ.toMonoidHom).equivMapOfInjective F.subtype F.subtype_injective)).trans
      (MulEquiv.subgroupCongr (hJ _ hMc))⟩

theorem nonempty_component_equiv_of_normal_simple {X G : Type} [Group X] [Group G]
    {F J : Subgroup G} [IsSimpleGroup J] (hJF : J ≤ F) (hJn : (J.subgroupOf F).Normal)
    (hsolv : Group.IsSolvable (F ⧸ J.subgroupOf F)) (Ψ : X ≃* F) {L : Subgroup X}
    (hL : IsComponent L) : Nonempty (L ≃* J) :=
  nonempty_component_equiv_of_unique Ψ
    (fun _ hM => ExcSelector.eq_of_isComponentOf_of_normal_simple hJF hJn hsolv hM) hL

theorem card_fixSubfield_of_sq_pow {K : Type} [Field K] {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hK : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e)) :
    Nat.card (fixSubfield δ) = p ^ e := by
  have hK' : Nat.card K = p ^ (2 * e) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨φ, hφ, hord, -, -, hA⟩ :=
    LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp
      (by omega) hK'
  have hδφ : δ = φ ^ e := RingEquiv.ext fun c => by
    rw [hδ, ringAut_pow_apply_of_frobenius hφ e c]
  have hδord : orderOf δ = 2 := by
    rw [hδφ, orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro_left 2 rfl), hord,
      Nat.mul_div_cancel _ (by omega : 0 < e)]
  obtain ⟨-, S, hS, hcard⟩ := hA (Subgroup.zpowers δ)
  rw [Nat.card_zpowers, hδord, Nat.mul_div_cancel_left e two_pos] at hcard
  have hSk : S = fixSubfield δ := by
    refine SetLike.ext' ?_
    rw [hS]
    ext a
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_fixSubfield]
    constructor
    · intro h
      exact h δ (Subgroup.mem_zpowers δ)
    · intro h τ' hτ'
      have hstab : Subgroup.zpowers δ ≤ MulAction.stabilizer (K ≃+* K) a :=
        Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff, RingAut.smul_def]; exact h)
      have h' := hstab hτ'
      rwa [MulAction.mem_stabilizer_iff, RingAut.smul_def] at h'
  rw [← hSk, hcard]

theorem lieModel_centralQuotient_of_mulEquiv_adjointGroup {L : Type} [Group L]
    {t : StatedLieTag} {τ : Tag}
    (htτ : t = .G2 ∧ τ = .G2 ∨ t = .F4 ∧ τ = .F4 ∨ t = .E6 ∧ τ = .E6 ∨ t = .E7 ∧ τ = .E7 ∨
      t = .E8 ∧ τ = .E8) {k : Type} [Field k] [Finite k] {p e : ℕ}
    (hadm : StatedLieAdmissible t 0 p e) (hk : Nat.card k = p ^ e)
    (E : L ≃* adjointGroup τ k) : LieModel (L ⧸ center L) t 0 p e := by
  have hu : UntwistedChevalleyModel (L ⧸ center L) τ (p ^ e) :=
    ⟨k, inferInstance, inferInstance, hk,
      ⟨QuotientGroup.congr _ _ E (Subgroup.map_center_eq E)⟩⟩
  rcases htτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals exact Or.inr (Or.inl ⟨rfl, by decide, hadm, hu⟩)

theorem three_le_pow_of_odd_prime {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    3 ≤ p ^ e :=
  le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)

theorem ringChar_eq_of_card {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) : ringChar K = p := by
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  exact ringChar.eq K p

variable {K : Type} [Field K] [Finite K]

theorem odd_field_component_equiv
    {τ : Tag} {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup α) {L : Subgroup X}
    (hL : IsComponent L) : Nonempty (L ≃* adjointGroup τ (fixSubfield δ)) := by
  classical
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar_eq_of_card hp (by omega : 1 ≤ 2 * e) (by rw [hKe, ← pow_mul, mul_comm])]
    exact hp2
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 τ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hβfix : (fixedSubgroup β).map (adjointGroup τ K).subtype = entrywiseFixedGroup τ δ := by
    ext y
    simp only [Subgroup.mem_map, entrywiseFixedGroup, Subgroup.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      change Units.map (entrywiseHom δ.toRingHom) (u : ModGL τ K) = u
      rw [← hβ u]
      exact congrArg Subtype.val hu
    · rintro ⟨hyG, hyδ⟩
      refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
      change (β ⟨y, hyG⟩ : ModGL τ K) = y
      rw [hβ]
      exact hyδ
  let e₂ : ↥(fixedSubgroup β) ≃* ↥(entrywiseFixedGroup τ δ) :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans (MulEquiv.subgroupCongr hβfix)
  obtain ⟨-, -, -, hJΓ, -, hJn, hcomm⟩ := Chevalley_coordinate_field_fixed_normal_subgroup τ K δ
  have hk2 := ringChar_fixSubfield_ne_two hK2 δ
  have hs := (odd_pinned_Chevalley_p_components τ (fixSubfield δ) hk2).1
  let eJ : adjointGroup τ (fixSubfield δ) ≃* fixedFieldImage τ δ :=
    (adjointGroup τ (fixSubfield δ)).equivMapOfInjective _ (baseChangeGL_injective _)
  have : IsSimpleGroup (fixedFieldImage τ δ) := (MulEquiv.isSimpleGroup_congr eJ).1 hs
  have hsolv : Group.IsSolvable (entrywiseFixedGroup τ δ ⧸
      (fixedFieldImage τ δ).subgroupOf (entrywiseFixedGroup τ δ)) :=
    Group.isSolvable_of_comm hcomm
  obtain ⟨E⟩ := nonempty_component_equiv_of_normal_simple hJΓ hJn hsolv
    (Ψ.trans (e₁.trans e₂)) hL
  exact ⟨E.trans eJ.symm⟩

theorem odd_field_oddLieCentralQuotient
    {t : StatedLieTag} {τ : Tag}
    (htτ : t = .G2 ∧ τ = .G2 ∨ t = .F4 ∧ τ = .F4 ∨ t = .E6 ∧ τ = .E6 ∨ t = .E7 ∧ τ = .E7 ∨
      t = .E8 ∧ τ = .E8) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup α) {L : Subgroup X}
    (hL : IsComponent L) : OddLieCentralQuotient p L := by
  obtain ⟨E⟩ := odd_field_component_equiv hp hp2 he hKe δ hδ hαg hα Ψ hL
  have hk := card_fixSubfield_of_sq_pow hp he hKe δ hδ
  have h3 := three_le_pow_of_odd_prime hp hp2 he
  have hadm : StatedLieAdmissible t 0 p e := by
    rcases htτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨hp, he, rfl, h3⟩
    all_goals exact ⟨hp, he, rfl⟩
  exact ⟨t, 0, e, hadm, lieModel_centralQuotient_of_mulEquiv_adjointGroup htτ hadm hk E⟩

theorem oddLieCentralQuotient_reeGamma_G2
    [CharP K ReeTag.G2.prime] {b : ℕ} (hb : 1 ≤ b) (hK : Nat.card K = 3 ^ (2 * b + 1)) :
    OddLieCentralQuotient 3 (ReeTag.G2.reeGamma K b) := by
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
  exact ⟨.twistedG2, 0, 2 * b + 1, hadm, Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hadm, b, rfl, K,
    inferInstance, inferInstance, hK, ⟨e'⟩⟩))⟩

theorem oddLieCentralQuotient_graphFixedRootGroup_E6
    {M : Type} [Field M] [Finite M] {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hM : Nat.card M = (p ^ e) ^ 2) (σ : M ≃+* M) (hσ : ∀ c, σ c = c ^ (p ^ e)) :
    OddLieCentralQuotient p (graphFixedRootGroup TwistTag.E6 M σ.toRingHom) := by
  have hperf := (finite_fixed_root_group_perfect TwistTag.E6 hp he M hM σ.toRingHom hσ).2.2.1
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 M σ
  obtain ⟨e'⟩ := LieType.Chevalley.nonempty_derivedCentralQuotient_equiv hperf hZ
  have hadm : StatedLieAdmissible .twistedE6 0 p e := ⟨hp, he, rfl⟩
  exact ⟨.twistedE6, 0, e, hadm, Or.inr (Or.inl ⟨rfl, by decide, hadm, M, inferInstance,
    inferInstance, hM, σ.toRingHom, hσ,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e'.symm⟩⟩)⟩

@[expose] def OddExcInnerDiagInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) → orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → OddLieCentralQuotient p L

@[expose] def OddE6GraphInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup TwistTag.E6.tag K)) (g : adjointGroup TwistTag.E6.tag K)
      (a : Fin TwistTag.E6.tag.rank → Kˣ),
      (∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
        (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
          diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) *
            (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
              (g : ModGL TwistTag.E6.tag K)⁻¹) → orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → OddLieCentralQuotient p L

theorem odd_F4_E8_G2_explicit
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E8 ∨ τ = .G2) (hinner : OddExcInnerDiagInput τ)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : τ = .G2 → p ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (β : MulAut (adjointGroup τ K)) (hβ : orderOf β = 2)
    {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup β) {L : Subgroup X} (hL : IsComponent L) :
    OddLieCentralQuotient p L := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hchar := ringChar_eq_of_card hp hf hK
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hτ' : τ = .F4 ∨ τ = .E8 ∨ (τ = .G2 ∧ ringChar K ≠ 3) := by
    rcases hτ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, hchar ▸ hp3 h⟩)
  rcases odd_F4_E8_G2_involution_inner_or_quadratic hτ' hKodd hβ2 with ⟨g, a, hβg⟩ |
    ⟨q, e, hq, he, hKe, δ, hδ, g, a, hβg⟩
  · exact oddLieCentralQuotient_of_component_equiv Ψ (hinner K p f hp hp2 hK β g a hβg hβ) hL
  · have hqp : q = p := by
      have h : q ∣ p ^ f := by
        rw [← hK, hKe]
        exact dvd_pow (dvd_pow_self q (by omega)) two_ne_zero
      exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)
    subst hqp
    have htτ : (StatedLieTag.F4 = .F4 ∧ τ = .F4 ∨ StatedLieTag.E8 = .E8 ∧ τ = .E8) ∨
        τ = .G2 := by
      rcases hτ with h | h | h
      · exact Or.inl (Or.inl ⟨rfl, h⟩)
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · exact Or.inr h
    rcases htτ with (⟨-, rfl⟩ | ⟨-, rfl⟩) | rfl
    · exact odd_field_oddLieCentralQuotient (t := .F4) (Or.inr (Or.inl ⟨rfl, rfl⟩)) hq hp2 he hKe
        δ hδ hβg hβ2 Ψ hL
    · exact odd_field_oddLieCentralQuotient (t := .E8)
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) hq hp2 he hKe δ hδ hβg hβ2 Ψ hL
    · exact odd_field_oddLieCentralQuotient (t := .G2) (Or.inl ⟨rfl, rfl⟩) hq hp2 he hKe δ hδ
        hβg hβ2 Ψ hL

theorem odd_G2_three_explicit
    [CharP K ReeTag.G2.prime] (hinner : OddExcInnerDiagInput .G2) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) (β : MulAut (adjointGroup ReeTag.G2.tag K)) (hβ : orderOf β = 2)
    {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup β) {L : Subgroup X} (hL : IsComponent L) :
    OddLieCentralQuotient 3 L ∨
      (f = 1 ∧ β ∉ inner (adjointGroup ReeTag.G2.tag K) ∧ LieModel L .PSL 2 2 3) := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  rcases G2_three_involution_inner_quadratic_or_exceptional hf hK hβ2 with ⟨g, a, hβg⟩ |
    ⟨e, he, hKe, δ, hδ, g, a, hβg⟩ | ⟨b, g, hfb, rfl⟩
  · exact Or.inl (oddLieCentralQuotient_of_component_equiv Ψ
      (hinner K 3 f Nat.prime_three (by decide) hK β g a hβg hβ) hL)
  · exact Or.inl (odd_field_oddLieCentralQuotient (t := .G2) (Or.inl ⟨rfl, rfl⟩) Nat.prime_three
      (by decide) he hKe δ hδ hβg hβ2 Ψ hL)
  · have hK' : Nat.card K = 3 ^ (2 * b + 1) := hfb ▸ hK
    obtain ⟨⟨ψ, hψ⟩, -, -⟩ :=
      LieType.Ree.G2_exceptional_coset_involution_fixed_p_components b K hK' g hβ2
    have hc : MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K b) =
        ReeTag.G2.finiteReeAut K b :=
      (MulEquiv.ext fun _ => rfl : MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K b) =
        ψ * (MulAut.conj g * ReeTag.G2.finiteReeAut K b) * ψ⁻¹).trans hψ
    have hmap : (fixedSubgroup (ReeTag.G2.finiteReeAut K b)).map
        (adjointGroup ReeTag.G2.tag K).subtype = ReeTag.G2.reeGamma K b := rfl
    have hFc : fixedSubgroup (MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K b)) =
        fixedSubgroup (ReeTag.G2.finiteReeAut K b) := by rw [hc]
    let Ψ' : X ≃* ReeTag.G2.reeGamma K b := Ψ.trans ((fixedSubgroupCongrEquiv ψ _).trans
      ((MulEquiv.subgroupCongr hFc).trans
        (((fixedSubgroup (ReeTag.G2.finiteReeAut K b)).equivMapOfInjective _
          Subtype.val_injective).trans (MulEquiv.subgroupCongr hmap))))
    obtain ⟨hDs, -, -, htop, -, -⟩ :=
      CatalogueBSmallRee.small_Ree_whole_group_p_components b K hK'
    set Γ := ReeTag.G2.reeGamma K b with hΓ
    have eJ : commutator Γ ≃* (commutator Γ).map Γ.subtype :=
      (commutator Γ).equivMapOfInjective _ Subtype.val_injective
    have : IsSimpleGroup ((commutator Γ).map Γ.subtype) := (MulEquiv.isSimpleGroup_congr eJ).1 hDs
    have hJF : (commutator Γ).map Γ.subtype ≤ Γ := Subgroup.map_subtype_le _
    have hJsub : ((commutator Γ).map Γ.subtype).subgroupOf Γ = commutator Γ :=
      Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
    have hJn : (((commutator Γ).map Γ.subtype).subgroupOf Γ).Normal := by
      rw [hJsub]
      exact Subgroup.commutator_normal ⊤ ⊤
    have hsolv : Group.IsSolvable (Γ ⧸ ((commutator Γ).map Γ.subtype).subgroupOf Γ) := by
      have : Group.IsSolvable (Abelianization Γ) := inferInstance
      exact Group.isSolvable_of_surjective
        (f := (QuotientGroup.quotientMulEquivOfEq hJsub.symm).toMonoidHom)
        (QuotientGroup.quotientMulEquivOfEq hJsub.symm).surjective
    obtain ⟨E⟩ := nonempty_component_equiv_of_normal_simple hJF hJn hsolv Ψ' hL
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · right
      refine ⟨by omega, ?_, ?_⟩
      · obtain ⟨-, -, ⟨Θ, hΘ, -, hker⟩, -, -, -, hodd⟩ :=
          G2_three_exact_automorphism_normal_form hf K hK
        obtain ⟨-, hR, -⟩ := hodd 0 hfb
        intro hin
        have hmem : MulAut.conj g * ReeTag.G2.finiteReeAut K 0 ∈ Θ.ker := by
          rw [hker]
          exact hin
        rw [MonoidHom.mem_ker, hΘ _ g f (by rw [hR])] at hmem
        have h1 : ((f : ℕ) : ZMod (2 * f)) = 0 := by
          simpa using congrArg Multiplicative.toAdd hmem
        rw [ZMod.natCast_eq_zero_iff] at h1
        have := Nat.le_of_dvd (by omega) h1
        omega
      · obtain ⟨-, -, -, -, -, -, h0⟩ :=
          LiteratureLocal.small_Ree_G2_fixed_points_and_Ree3_PGammaL2_8 0 K hK'
        obtain ⟨-, -, -, -, hstated, -⟩ := h0 rfl
        have hL0 : LieModel (commutator Γ) .PSL 2 2 3 := Or.inl ⟨by decide, hstated⟩
        exact LieType.CurtisTits.lieModel_of_mulEquiv (E.trans eJ.symm).symm hL0
    · left
      have eD : commutator Γ ≃* Γ := (MulEquiv.subgroupCongr (htop hb)).trans Subgroup.topEquiv
      exact oddLieCentralQuotient_of_mulEquiv ((E.trans eJ.symm).trans eD)
        (oddLieCentralQuotient_reeGamma_G2 hb hK')

theorem odd_E7_explicit
    (hinner : OddExcInnerDiagInput .E7) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (β : MulAut (adjointGroup .E7 K)) (hβ : orderOf β = 2)
    {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup β) {L : Subgroup X} (hL : IsComponent L) :
    OddLieCentralQuotient p L := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have h1 : ∀ x : ModGL Tag.E7 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ : ∀ ε : Fin (exactE Tag.E7), exactQ Tag.E7 K ε = 1 := fun _ => rfl
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form Tag.E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨-, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF β
  have hσ2 := hsq β g a σ ε hgaσ hβ2
  by_cases hσ1 : σ = 1
  · subst hσ1
    refine oddLieCentralQuotient_of_component_equiv Ψ
      (hinner K p f hp hp2 hK β g a (fun h => ?_) hβ) hL
    rw [hgaσ h, hQ, h1, mul_one, inv_one, mul_one]
  · obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hK σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hK]
    exact odd_field_oddLieCentralQuotient (t := .E7) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      hp hp2 he hKe σ hσc (g := g) (a := a) (fun h => by rw [hgaσ h, hQ, mul_one, inv_one,
        mul_one]) hβ2 Ψ hL

theorem odd_E6_explicit
    (hinner : OddExcInnerDiagInput .E6) (hgraph : OddE6GraphInput) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (β : MulAut (adjointGroup .E6 K))
    (hβ : orderOf β = 2) {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup β) {L : Subgroup X}
    (hL : IsComponent L) : OddLieCentralQuotient p L := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hK2 : ringChar K ≠ 2 := by rw [ringChar_eq_of_card hp hf hK]; exact hp2
  have h1 : ∀ x : ModGL Tag.E6 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ0 : exactQ Tag.E6 K 0 = 1 := pow_zero _
  have hQ1 : exactQ Tag.E6 K 1 = diagramMap TwistTag.E6 K := pow_one _
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K
  obtain ⟨-, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF β
  have hσ2 := hsq β g a σ ε hgaσ hβ2
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have h2 : (ε : ℕ) < 2 := ε.isLt
    omega
  by_cases hσ1 : σ = 1
  · subst hσ1
    rcases hε with hε | hε
    · refine oddLieCentralQuotient_of_component_equiv Ψ
        (hinner K p f hp hp2 hK β g a (fun h => ?_) hβ) hL
      rw [hgaσ h, hε, hQ0, h1, mul_one, inv_one, mul_one]
    · exact oddLieCentralQuotient_of_component_equiv Ψ (hgraph K p f hp hp2 hK β g a
        (fun h => (hgaσ h).trans (by rw [hε, hQ1, h1]; rfl)) hβ) hL
  · obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hK σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hK]
    rcases hε with hε | hε
    · exact odd_field_oddLieCentralQuotient (t := .E6) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hp
        hp2 he hKe σ hσc (g := g) (a := a)
        (fun h => by rw [hgaσ h, hε, hQ0, mul_one, inv_one, mul_one]) hβ2 Ψ hL
    · obtain ⟨-, β', hβ', hβα⟩ :=
        exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe σ.toRingHom hσc
      obtain ⟨-, hconj⟩ := hβα g a
      obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj β (fun h => (hgaσ h).trans (by rw [hε, hQ1]; rfl))
        ((sq β).symm.trans hβ2)
      have hβfix : (fixedSubgroup β').map (adjointGroup TwistTag.E6.tag K).subtype =
          twistedFixedGroup TwistTag.E6 K σ.toRingHom := by
        ext y
        simp only [Subgroup.mem_map, twistedFixedGroup, Subgroup.mem_inf]
        constructor
        · rintro ⟨u, hu, rfl⟩
          refine ⟨u.2, ?_⟩
          change twistHom TwistTag.E6 K σ.toRingHom (u : ModGL TwistTag.E6.tag K) = u
          rw [twistHom_apply, ← hβ' u]
          exact congrArg Subtype.val hu
        · rintro ⟨hyG, hyσ⟩
          refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
          change (β' ⟨y, hyG⟩ : ModGL TwistTag.E6.tag K) = y
          rw [hβ']
          change twistHom TwistTag.E6 K σ.toRingHom y = y at hyσ
          rw [twistHom_apply] at hyσ
          exact hyσ
      let e₂ : ↥(fixedSubgroup β') ≃* ↥(twistedFixedGroup TwistTag.E6 K σ.toRingHom) :=
        (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
          (MulEquiv.subgroupCongr hβfix)
      have hperf := (finite_fixed_root_group_perfect TwistTag.E6 hp he K hKe σ.toRingHom
        hσc).2.2.1
      have := (odd_diagram_field_fixed_p_components TwistTag.E6 K hK2 σ).1
      have hJF := graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom
      have hJsub : (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf
          (twistedFixedGroup TwistTag.E6 K σ.toRingHom) =
          commutator (twistedFixedGroup TwistTag.E6 K σ.toRingHom) := by
        rw [← hperf, ← Subgroup.map_subtype_commutator]
        exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
      have hJn : ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf
          (twistedFixedGroup TwistTag.E6 K σ.toRingHom)).Normal := by
        rw [hJsub]
        exact Subgroup.commutator_normal ⊤ ⊤
      have hsolv : Group.IsSolvable (twistedFixedGroup TwistTag.E6 K σ.toRingHom ⧸
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf
            (twistedFixedGroup TwistTag.E6 K σ.toRingHom)) := by
        have : Group.IsSolvable (Abelianization (twistedFixedGroup TwistTag.E6 K σ.toRingHom)) :=
          inferInstance
        exact Group.isSolvable_of_surjective
          (f := (QuotientGroup.quotientMulEquivOfEq hJsub.symm).toMonoidHom)
          (QuotientGroup.quotientMulEquivOfEq hJsub.symm).surjective
      obtain ⟨E⟩ := nonempty_component_equiv_of_normal_simple hJF hJn hsolv
        (Ψ.trans (e₁.trans e₂)) hL
      exact oddLieCentralQuotient_of_mulEquiv E
        (oddLieCentralQuotient_graphFixedRootGroup_E6 hp he hKe σ hσc)

theorem gls3OddFamilyInput_of_explicit
    {t : StatedLieTag} {τ : Tag} (ht : t ∈ chevalleyExceptionalTags)
    (hmodel : ∀ (J : Type) [Group J] (p f : ℕ), ChevalleyExceptionalModel J t p f →
      UntwistedChevalleyModel J τ (p ^ f))
    (hexp : ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
      Nat.card K = p ^ f → ∀ β : MulAut (adjointGroup τ K), orderOf β = 2 →
        ∀ (X : Type) [Group X], (X ≃* fixedSubgroup β) → ∀ L : Subgroup X, IsComponent L →
          OddLieCentralQuotient p L) :
    GLS3OddFamilyInput t := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ
    (hmodel J p f (GH74.chevalleyExceptionalModel_of_lieModel ht hm))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact Or.inl (hexp F p f hp hp2 hadm.2.1 hF _ hβ _ (fixedSubgroupCongrEquiv e α) Kc hKc)

theorem gls3OddFamilyInput_F4
    (hinner : OddExcInnerDiagInput .F4) : GLS3OddFamilyInput .F4 :=
  gls3OddFamilyInput_of_explicit (τ := .F4) (by decide) (fun _ _ _ _ h => h.2)
    fun K _ _ p f hp hp2 hf hK β hβ _ _ Ψ _ hL =>
      odd_F4_E8_G2_explicit (Or.inl rfl) hinner hp hp2 (fun h => absurd h (by decide)) hf hK β hβ
        Ψ hL

theorem gls3OddFamilyInput_E8
    (hinner : OddExcInnerDiagInput .E8) : GLS3OddFamilyInput .E8 :=
  gls3OddFamilyInput_of_explicit (τ := .E8) (by decide) (fun _ _ _ _ h => h.2)
    fun K _ _ p f hp hp2 hf hK β hβ _ _ Ψ _ hL =>
      odd_F4_E8_G2_explicit (Or.inr (Or.inl rfl)) hinner hp hp2 (fun h => absurd h (by decide)) hf
        hK β hβ Ψ hL

theorem gls3OddFamilyInput_E7
    (hinner : OddExcInnerDiagInput .E7) : GLS3OddFamilyInput .E7 :=
  gls3OddFamilyInput_of_explicit (τ := .E7) (by decide) (fun _ _ _ _ h => h.2)
    fun K _ _ p f hp hp2 hf hK β hβ _ _ Ψ _ hL => odd_E7_explicit hinner hp hp2 hf hK β hβ Ψ hL

theorem gls3OddFamilyInput_E6
    (hinner : OddExcInnerDiagInput .E6) (hgraph : OddE6GraphInput) : GLS3OddFamilyInput .E6 :=
  gls3OddFamilyInput_of_explicit (τ := .E6) (by decide) (fun _ _ _ _ h => h.2)
    fun K _ _ p f hp hp2 hf hK β hβ _ _ Ψ _ hL =>
      odd_E6_explicit hinner hgraph hp hp2 hf hK β hβ Ψ hL

theorem gls3OddFamilyInput_G2
    (hinner : OddExcInnerDiagInput .G2) : GLS3OddFamilyInput .G2 := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2
    ((GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2 : UntwistedChevalleyModel J
      .G2 (p ^ f))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP F ReeTag.G2.prime :=
      LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three hf hF
    rcases odd_G2_three_explicit hinner hf hF (MulAut.congr e α) hβ (fixedSubgroupCongrEquiv e α)
        hKc with h | ⟨rfl, hβo, hPSL⟩
    · exact Or.inl h
    · refine Or.inr ⟨rfl, ?_, fun hin => hβo ?_, hPSL⟩
      · rw [show n = 0 from hadm.2.2.1] at hm
        exact hm
      · exact (LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff e α).2 hin
  · exact Or.inl (odd_F4_E8_G2_explicit (Or.inr (Or.inr rfl)) hinner hp hp2 (fun _ => hp3) hf hF
      _ hβ (fixedSubgroupCongrEquiv e α) hKc)

end CFSG.ComponentClassification.CatLeafProof
