module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6PSLInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Outer
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Split

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem a6_psl_field {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hsq : CatalogueBLinearSemilinear.semilinearAction n K A σ ^ 2 = 1) :
    A6CentreForm (fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ)) := by
  intro L hL
  show A6Safe L
  let Ψ : fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ) ≃*
      fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ) := MulEquiv.refl _
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
  let Ψ' : fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ) ≃*
      fixedSubgroup (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) :=
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
  exact fun _ => isPGroup_center_of_mulEquiv_simple hL.1
    ((L.equivMapOfInjective Ψ'.toMonoidHom Ψ'.injective).trans E)
theorem a6_psl_graphField {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hord : orderOf (CatalogueBGraphField.graphFieldAction n K A σ) = 2) :
    A6CentreForm (fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ)) := by
  intro L hL
  show A6Safe L
  let Ψ : fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ) ≃*
      fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ) := MulEquiv.refl _
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
  let Ψt : fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ) ≃*
      CatalogueBGraphField.twistedFixedPSL n K A σ := Ψ
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
  exact fun _ => isPGroup_center_of_mulEquiv_simple hL.1
    (((L.equivMapOfInjective Ψt.toMonoidHom Ψt.injective).trans E).trans eQ)
theorem oddLieA6CentreFor_PSL
    : OddLieA6CentreFor .PSL := by
  intro J _ n p f hp hp2 hadm hm α hα
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psl_of_lieModel hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hβ2 : MulAut.congr e α ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have key : ∀ γ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K), MulAut.congr e α = γ →
      (orderOf γ = 2 → A6CentreForm (fixedSubgroup γ)) → A6CentreForm (fixedSubgroup α) := by
    intro γ hγ h
    exact a6CentreForm_of_mulEquiv ((fixedSubgroupCongrEquiv e α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))) (h (hγ ▸ hβ))
  have hn : 2 ≤ n := hadm.2.2.1
  have hsemi : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr e α = CatalogueBLinearSemilinear.semilinearAction n K A σ →
      A6CentreForm (fixedSubgroup α) := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact key _ hAσ fun hord => a6_inner_psl hp hp2 hK hadm A hord
    · exact key _ hAσ fun _ => a6_psl_field hn hp hp2 hf hK A σ hσ (hAσ ▸ hβ2)
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
        exact key _ hβ' fun hord => a6_graph_psl hp hp2 hK hn3 A hord
      · rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
        exact key _ hβ' fun hord => a6_psl_graphField hn3 hp hp2 hf hK A σ hσ hord

end CFSG.ComponentClassification.CatLeafProof
