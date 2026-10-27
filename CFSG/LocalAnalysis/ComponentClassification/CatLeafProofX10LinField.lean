module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpModel

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Lin

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof.X10Sp (CentralModel)
open CFSG.ComponentClassification.CatLeafProof (isPComponent_two_of_isComponent
  exists_mul_ne_of_isQuasisimple two_le_of_ringEquiv_ne_one fixedSubgroupCongrEquiv
  nonempty_projectiveSpecialUnitary_equiv_statedProj)

theorem centralModel_of_simple_model {L Y : Type} [Group L] [Group Y] [IsSimpleGroup Y]
    (hnab : ∃ a b : Y, a * b ≠ b * a) (E : L ≃* Y) {t : StatedLieTag} {n p e : ℕ}
    (hadm : StatedLieAdmissible t n p e) (hY : Blueprint.LieModel Y t n p e) :
    CentralModel p t n e L := by
  have hZ : center Y = ⊥ := ExcSelector.center_eq_bot_of_isSimpleGroup' hnab
  exact (show CentralModel p t n e Y from ⟨hadm, LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hY⟩).of_mulEquiv
      E

theorem field_psl_component_model {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hsq : CatalogueBLinearSemilinear.semilinearAction n K A σ ^ 2 = 1) {X : Type} [Group X]
    (Ψ : X ≃* fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ))
    {L : Subgroup X} (hL : IsComponent L) : ∃ j, f = 2 * j ∧ CentralModel p .PSL n j L := by
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
  refine ⟨f / 2, by obtain ⟨r, hr⟩ := heven; omega, ?_⟩
  exact centralModel_of_simple_model (exists_mul_ne_of_isQuasisimple hL'.1 E)
    ((L.equivMapOfInjective Ψ'.toMonoidHom Ψ'.injective).trans E) hadm
    (Or.inl ⟨by decide, hstated⟩)

theorem graphField_psl_component_model {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hord : orderOf (CatalogueBGraphField.graphFieldAction n K A σ) = 2) {X : Type} [Group X]
    (Ψ : X ≃* fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ)) {L : Subgroup X}
    (hL : IsComponent L) : ∃ j, f = 2 * j ∧ CentralModel p .PSU n j L := by
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hsq : CatalogueBGraphField.graphFieldAction n K A σ ^ 2 = 1 :=
    hord ▸ pow_orderOf_eq_one _
  have hne1 : CatalogueBGraphField.graphFieldAction n K A σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    exact absurd hord (by decide)
  obtain ⟨heven, hhalf, hunitary, -, -, -, hcomp⟩ :=
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
  have hstated : StatedClassicalModel (StatedProj (StatedSU n (p ^ (f / 2)) K)) .PSU n p
      (f / 2) := ⟨hadm, K, inferInstance, inferInstance, hunitary, ⟨MulEquiv.refl _⟩⟩
  have := (ClassicalGroups.Unitary.fam_PSU_simplicity _ n p (f / 2) hstated).2
  refine ⟨f / 2, ?_, ?_⟩
  · have := heven
    obtain ⟨r, hr⟩ := this
    omega
  exact centralModel_of_simple_model (exists_mul_ne_of_isQuasisimple hL'.1 (E.trans eQ))
    (((L.equivMapOfInjective Ψt.toMonoidHom Ψt.injective).trans E).trans eQ) hadm
    (Or.inl ⟨by decide, hstated⟩)

end CFSG.ComponentClassification.CatLeafProof.X10Lin
