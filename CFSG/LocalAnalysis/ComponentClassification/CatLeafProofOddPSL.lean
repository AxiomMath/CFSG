module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldComponents
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearConjugacy

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem isPComponent_two_of_isComponent {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    (hL : IsComponent L) : IsPComponent 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (LocalAnalysis.ComponentInitial.solvable_prime_core_ordinary_components 2 Nat.prime_two
    (Milestones.odd_order_solvable
      (Nat.coprime_two_left.1 (pPrimeCore_coprime_card (G := X) (p := 2))))).1 L hL

theorem exists_mul_ne_of_isQuasisimple {L Y : Type*} [Group L] [Group Y] (hL : IsQuasisimple L)
    (E : L ≃* Y) : ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hL
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨E x, E y, fun h => hab ?_⟩
  have hxy : x * y = y * x := E.injective (by rw [map_mul, map_mul, h])
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]

theorem oddLieCentralQuotient_of_simple_model {L Y : Type} [Group L] [Group Y] [IsSimpleGroup Y]
    (hnab : ∃ a b : Y, a * b ≠ b * a) (E : L ≃* Y) {t : StatedLieTag} {n p e : ℕ}
    (hadm : StatedLieAdmissible t n p e) (hY : LieModel Y t n p e) :
    OddLieCentralQuotient p L := by
  have hZ : center Y = ⊥ := ExcSelector.center_eq_bot_of_isSimpleGroup' hnab
  exact oddLieCentralQuotient_of_mulEquiv E ⟨t, n, e, hadm, LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hY⟩

theorem nonempty_mulEquiv_psl_of_lieModel {J : Type} [Group J] {n p f : ℕ}
    (hadm : StatedLieAdmissible .PSL n p f) (hm : LieModel J .PSL n p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (J ≃* ProjectiveSpecialLinearGroup (Fin n) K) := by
  have hn : 2 ≤ n := hadm.2.2.1
  rcases hm with ⟨-, h⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    exact ⟨K, inferInstance, inferInstance, hK,
      ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm⟩⟩
  all_goals omega

theorem two_le_of_ringEquiv_ne_one {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {σ : K ≃+* K} (hσ : σ ≠ 1) : 2 ≤ f := by
  obtain ⟨-, -, -, -, hAut, -⟩ :=
    LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hf hK
  by_contra h
  have h1 : f = 1 := by omega
  rw [h1] at hAut
  have : Subsingleton (K ≃+* K) := (Nat.card_eq_one_iff_unique.1 hAut).1
  exact hσ (Subsingleton.elim _ _)

theorem odd_psl_field_oddLieCentralQuotient {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hsq : CatalogueBLinearSemilinear.semilinearAction n K A σ ^ 2 = 1) {X : Type} [Group X]
    (Ψ : X ≃* fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ))
    {L : Subgroup X} (hL : IsComponent L) : OddLieCentralQuotient p L := by
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hf2 := two_le_of_ringEquiv_ne_one hp hf hK hσ
  have hpar : 3 ≤ n ∨ 5 ≤ Nat.card K := by
    right
    rw [hK]
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left (by have := hp.two_le; omega) 2
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf2
  obtain ⟨heven, hσc, H, hα⟩ := CatalogueBLinearSemilinear.odd_linear_field_involution_conjugacy
    n K p f hp hpodd hf hK hn hpar A σ hσ hsq
  have hσ2 : σ ^ 2 = 1 := by
    have : Fintype K := Fintype.ofFinite K
    refine RingEquiv.ext fun x => ?_
    rw [sq, RingAut.mul_apply, hσc, hσc, ← pow_mul, ← sq, ← pow_mul,
      Nat.div_mul_cancel (even_iff_two_dvd.1 heven), ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
    rfl
  have hc : MulAut.congr (CatalogueBHigherLinearAction.innerDiagonalAction n K H)
      (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) =
      CatalogueBLinearSemilinear.semilinearAction n K A σ :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (CatalogueBHigherLinearAction.innerDiagonalAction
      n K H) (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) = _).trans hα.symm
  let Ψ' : X ≃* fixedSubgroup (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) :=
    Ψ.trans ((MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      (fixedSubgroupCongrEquiv _ _).symm)
  have hL' : IsComponent (L.map Ψ'.toMonoidHom) := LocalCores.isComponent_map_mulEquiv Ψ' hL
  have hL2 := isPComponent_two_of_isComponent hL'
  obtain ⟨hcard, -, hsmall, hiso⟩ :=
    CatalogueBHigherLinearField.linear_field_involution_fixed_p_components n hn K σ hσ2 hσ
  have hcardk : Nat.card (CatalogueBHigherLinearField.fixedField K σ) = p ^ (f / 2) := by
    have h2 : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 heven), hK]
    rw [hcard] at h2
    exact Nat.pow_left_injective two_ne_zero h2
  by_cases hex : n = 2 ∧ (Nat.card (CatalogueBHigherLinearField.fixedField K σ) = 2 ∨
      Nat.card (CatalogueBHigherLinearField.fixedField K σ) = 3)
  · exact absurd hL2 (hsmall hex 2 Nat.prime_two _)
  obtain ⟨E⟩ := hiso hex 2 Nat.prime_two _ hL2
  have he : 1 ≤ f / 2 := by omega
  have hadm : StatedLieAdmissible .PSL n p (f / 2) := by
    refine ⟨hp, he, hn, fun h => ?_, fun h => ?_⟩
    · have h1 : p ^ (f / 2) = 2 := (Prod.mk.inj h).2
      have hodd : Odd (p ^ (f / 2)) := hpodd.pow
      rw [h1] at hodd
      exact absurd hodd (by decide)
    · exact hex ⟨(Prod.mk.inj h).1, Or.inr (hcardk.trans (Prod.mk.inj h).2)⟩
  have hstated : StatedClassicalModel (ProjectiveSpecialLinearGroup (Fin n)
      (CatalogueBHigherLinearField.fixedField K σ)) .PSL n p (f / 2) :=
    ⟨hadm, CatalogueBHigherLinearField.fixedField K σ, inferInstance, inferInstance, hcardk,
      ⟨projectiveSpecialLinearGroupEquivStatedProj n _⟩⟩
  have := (LieType.Simplicity.fam_PSL_simplicity _ n p (f / 2) hstated).2
  exact oddLieCentralQuotient_of_simple_model (exists_mul_ne_of_isQuasisimple hL'.1 E)
    ((L.equivMapOfInjective Ψ'.toMonoidHom Ψ'.injective).trans E) hadm
    (Or.inl ⟨by decide, hstated⟩)

theorem nonempty_projectiveSpecialUnitary_equiv_statedProj {n : ℕ} {K : Type} [Field K]
    [Finite K] {p e : ℕ} [Fact p.Prime] (hunitary : Nat.card K = (p ^ e) ^ 2) :
    Nonempty (CatalogueBGraphField.UnitaryDataProjectiveSpecial n K p e hunitary ≃*
      StatedProj (StatedSU n (p ^ e) K)) := by
  have : CharP K p := CatalogueBUnitaryTwo.unitaryFieldCharP p e hunitary
  have hSU : LieType.Universal.Unitary.SUid
      (CatalogueBUnitaryTwo.unitaryFieldConjugation p e hunitary) n = StatedSU n (p ^ e) K :=
    LieType.Universal.Unitary.SUid_eq_statedSU hunitary n
  exact ⟨QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hSU) (by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x.1, by rw [hSU]; exact x.2⟩, hx, rfl⟩)⟩

theorem odd_psl_graphField_oddLieCentralQuotient {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hord : orderOf (CatalogueBGraphField.graphFieldAction n K A σ) = 2) {X : Type} [Group X]
    (Ψ : X ≃* fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ)) {L : Subgroup X}
    (hL : IsComponent L) : OddLieCentralQuotient p L := by
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hsq : CatalogueBGraphField.graphFieldAction n K A σ ^ 2 = 1 :=
    hord ▸ pow_orderOf_eq_one _
  have hne1 : CatalogueBGraphField.graphFieldAction n K A σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    exact absurd hord (by decide)
  obtain ⟨-, hhalf, hunitary, -, -, -, hcomp⟩ :=
    CatalogueBGraphField.odd_linear_graph_field_involution_fixed_p_components_native n K p f
      hpodd hf hK hn A σ hσ hne1 hsq
  let Ψt : X ≃* CatalogueBGraphField.twistedFixedPSL n K A σ := Ψ
  have hL' : IsComponent (L.map Ψt.toMonoidHom) := LocalCores.isComponent_map_mulEquiv Ψt hL
  obtain ⟨-, ⟨E⟩⟩ := hcomp 2 Nat.prime_two _ (isPComponent_two_of_isComponent hL')
  obtain ⟨eQ⟩ := nonempty_projectiveSpecialUnitary_equiv_statedProj (n := n) hunitary
  have hadm : StatedLieAdmissible .PSU n p (f / 2) := by
    refine ⟨hp, hhalf, hn, fun h => ?_⟩
    have h1 : p ^ (f / 2) = 2 := (Prod.mk.inj h).2
    have hodd : Odd (p ^ (f / 2)) := hpodd.pow
    rw [h1] at hodd
    exact absurd hodd (by decide)
  have hstated : StatedClassicalModel (StatedProj (StatedSU n (p ^ (f / 2)) K)) .PSU n p (f / 2) :=
    ⟨hadm, K, inferInstance, inferInstance, hunitary, ⟨MulEquiv.refl _⟩⟩
  have := (ClassicalGroups.Unitary.fam_PSU_simplicity _ n p (f / 2) hstated).2
  exact oddLieCentralQuotient_of_simple_model (exists_mul_ne_of_isQuasisimple hL'.1 (E.trans eQ))
    (((L.equivMapOfInjective Ψt.toMonoidHom Ψt.injective).trans E).trans eQ) hadm
    (Or.inl ⟨by decide, hstated⟩)

theorem psl_two_normal_form {K : Type} [Field K] [Finite K]
    (α : MulAut (ProjectiveSpecialLinearGroup (Fin 2) K)) :
    ∃ (A : GL (Fin 2) K) (σ : K ≃+* K),
      α = CatalogueBLinearSemilinear.semilinearAction 2 K A σ := by
  obtain ⟨x, rfl⟩ := CatalogueSchreierLinearTwo.semilinearAction_surjective K α
  obtain ⟨g, σ, rfl⟩ : ∃ g σ, x = SemidirectProduct.inl g * SemidirectProduct.inr σ :=
    ⟨x.left, x.right, (SemidirectProduct.inl_left_mul_inr_right x).symm⟩
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
  refine ⟨A, σ, ?_⟩
  rw [map_mul, CatalogueSchreierLinearTwo.semilinearAction_inl,
    CatalogueSchreierLinearTwo.semilinearAction_inr]
  refine congrArg₂ (· * ·) (MulEquiv.ext fun y => ?_) (MulEquiv.ext fun y => ?_)
  · apply ProjectiveSpecialLinearGroup.toPGL_injective
    change ProjectiveSpecialLinearGroup.toPGL
        (CatalogueSchreierLinearTwo.pglAction K (ProjGenLinGroup.mk A) y) =
      ProjectiveSpecialLinearGroup.toPGL (CatalogueBHigherLinearAction.pglAction 2 K
        (ProjGenLinGroup.mk A) y)
    rw [CatalogueSchreierLinearTwo.toPGL_pglAction, CatalogueBHigherLinearAction.toPGL_pglAction]
  · obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective y
    change GorensteinWalter.psl2RingEquiv σ (QuotientGroup.mk' _ B) = _
    rw [GorensteinWalter.psl2RingEquiv_mk, CatalogueBHigherLinearField.pslFieldAut_mk]
    rfl

@[expose] def OddPSLInnerDiagInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    StatedLieAdmissible .PSL n p f → ∀ A : GL (Fin n) K,
      orderOf (CatalogueBHigherLinearAction.innerDiagonalAction n K A) = 2 →
      ∀ L : Subgroup (fixedSubgroup (CatalogueBHigherLinearAction.innerDiagonalAction n K A)),
        IsComponent L → OddLieCentralQuotient p L

@[expose] def OddPSLGraphInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    3 ≤ n → ∀ A : GL (Fin n) K, orderOf (CatalogueBGraphForm.pureGraphAction n K A) = 2 →
      ∀ L : Subgroup (fixedSubgroup (CatalogueBGraphForm.pureGraphAction n K A)),
        IsComponent L → OddLieCentralQuotient p L

theorem gls3OddFamilyInput_PSL (hinner : OddPSLInnerDiagInput) (hgraph : OddPSLGraphInput) :
    GLS3OddFamilyInput .PSL := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  refine Or.inl ?_
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psl_of_lieModel hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hβ2 : MulAut.congr e α ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have key : ∀ γ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K), MulAut.congr e α = γ →
      (orderOf γ = 2 → ∀ (X : Type) [Group X], (X ≃* fixedSubgroup γ) →
        ∀ L : Subgroup X, IsComponent L → OddLieCentralQuotient p L) →
      OddLieCentralQuotient p Kc := by
    intro γ hγ h
    exact h (hγ ▸ hβ) _ ((fixedSubgroupCongrEquiv e α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))) Kc hKc
  have hn : 2 ≤ n := hadm.2.2.1
  have hsemi : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr e α = CatalogueBLinearSemilinear.semilinearAction n K A σ →
      OddLieCentralQuotient p Kc := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact key _ hAσ fun hord X _ Ψ L hL => oddLieCentralQuotient_of_component_equiv Ψ
        (hinner n K p f hp hp2 hK hadm A hord) hL
    · exact key _ hAσ fun _ X _ Ψ L hL => odd_psl_field_oddLieCentralQuotient hn hp hp2 hf hK A
        σ hσ (hAσ ▸ hβ2) Ψ hL
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  · obtain ⟨A, σ, hAσ⟩ := psl_two_normal_form (MulAut.congr e α)
    exact hsemi A σ hAσ
  · obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
      (K := K) hn3
    obtain ⟨A, σ, ε, hε, hAσε⟩ :=
      hgen (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K).symm (MulAut.congr e α))
    have hβ' : MulAut.congr e α = MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)
        (LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
          LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ *
            LocalAnalysis.ComponentInitial.LinearFlag.dualAut n K ^ ε) := by
      rw [← hAσε]
      ext x
      simp
    interval_cases ε
    · rw [pow_zero, mul_one, CatalogueBLinearHigherB.congr_semilinear] at hβ'
      exact hsemi A σ hβ'
    · rw [pow_one] at hβ'
      by_cases hσ : σ = 1
      · subst hσ
        rw [map_one, mul_one, CatalogueBLinearHigherB.congr_pureGraph] at hβ'
        exact key _ hβ' fun hord X _ Ψ L hL => oddLieCentralQuotient_of_component_equiv Ψ
          (hgraph n K p f hp hp2 hK hn3 A hord) hL
      · rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
        exact key _ hβ' fun hord X _ Ψ L hL => odd_psl_graphField_oddLieCentralQuotient hn3 hp hp2
          hf hK A σ hσ hord Ψ hL

end CFSG.ComponentClassification.CatLeafProof
