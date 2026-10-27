module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamGL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamLGraph
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamOrth
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryComponents
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Simplicity.Classical
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerLGraph
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthAll

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem cl24_odd_psl_field_oddLieCentralQuotient {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K]
    [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hsq : CatalogueBLinearSemilinear.semilinearAction n K A σ ^ 2 = 1) {X : Type} [Group X]
    (Ψ : X ≃* fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ))
    {L : Subgroup X} (hL : IsComponent L)
    {Rel : ℕ → Prop} (hRel : ∀ f', f = 2 * f' → Rel f' := by cl24_rel) :
    Cl24Q p Rel L := by
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
  exact cl24_of_simple_model (exists_mul_ne_of_isQuasisimple hL'.1 E)
    ((L.equivMapOfInjective Ψ'.toMonoidHom Ψ'.injective).trans E) hadm
    (Or.inl ⟨by decide, hstated⟩)
    (hRel (f / 2) (by obtain ⟨r, hr⟩ := heven; omega))

theorem cl24_odd_psl_graphField_oddLieCentralQuotient {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hord : orderOf (CatalogueBGraphField.graphFieldAction n K A σ) = 2) {X : Type} [Group X]
    (Ψ : X ≃* fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ)) {L : Subgroup X}
    (hL : IsComponent L)
    {Rel : ℕ → Prop} (hRel : ∀ f', f = 2 * f' → Rel f' := by cl24_rel) :
    Cl24Q p Rel L := by
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
  exact cl24_of_simple_model (exists_mul_ne_of_isQuasisimple hL'.1 (E.trans eQ))
    (((L.equivMapOfInjective Ψt.toMonoidHom Ψt.injective).trans E).trans eQ) hadm
    (Or.inl ⟨by decide, hstated⟩)
    (hRel (f / 2) (Nat.pow_right_injective hp.two_le
      (show p ^ f = p ^ (2 * (f / 2)) by rw [← hK, hunitary, ← pow_mul, mul_comm])))

theorem cl24_psl_involution {J : Type} [Group J] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSL n p f) (hm : LieModel J .PSL n p f)
    {α : MulAut J} (hα : orderOf α = 2) {Kc : Subgroup (fixedSubgroup α)}
    (hKc : IsComponent Kc) :
    Cl24Q p (fun f' => f' = f ∨ f' = 2 * f ∨ f = 2 * f') Kc := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psl_of_lieModel hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hβ2 : MulAut.congr e α ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have key : ∀ γ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K), MulAut.congr e α = γ →
      (orderOf γ = 2 → ∀ (X : Type) [Group X], (X ≃* fixedSubgroup γ) →
        ∀ L : Subgroup X, IsComponent L → Cl24Q p (fun f' => f' = f ∨ f' = 2 * f ∨ f = 2 * f') L) →
      Cl24Q p (fun f' => f' = f ∨ f' = 2 * f ∨ f = 2 * f') Kc := by
    intro γ hγ h
    exact h (hγ ▸ hβ) _ ((fixedSubgroupCongrEquiv e α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))) Kc hKc
  have hn : 2 ≤ n := hadm.2.2.1
  have hsemi : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr e α = CatalogueBLinearSemilinear.semilinearAction n K A σ →
      Cl24Q p (fun f' => f' = f ∨ f' = 2 * f ∨ f = 2 * f') Kc := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact key _ hAσ fun hord X _ Ψ L hL => cl24_of_component_equiv Ψ
        (fun M hM =>
        cl24_oddLie_inner_psl hp hp2 hK hadm A hord hM) hL
    · exact key _ hAσ fun _ X _ Ψ L hL => cl24_odd_psl_field_oddLieCentralQuotient hn hp hp2 hf hK A
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
        exact key _ hβ' fun hord X _ Ψ L hL => cl24_of_component_equiv Ψ
          (fun M hM =>
          cl24_oddLie_graph_psl (cl24_orthogonalComponentsLie_holds hp hp2) hp hp2 hK
            hn3 A hord hM) hL
      · rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
        exact key _ hβ' fun hord X _ Ψ L hL => cl24_odd_psl_graphField_oddLieCentralQuotient hn3
          hp hp2
          hf hK A σ hσ hord Ψ hL

theorem cl24_family_PSL : Cl24OddFamily .PSL := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  refine Or.inl ((cl24_psl_involution hp hp2 hadm hm hα hKc).mono ?_)
  intro f' h
  unfold Cl24FieldRel
  omega

end CFSG.OddStandard.SmallF3.HypA2Leaves
