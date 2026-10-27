module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Typed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem excCompModel_psl_field {n : ℕ} (hn68 : n = 6 ∨ n = 8) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hsq : CatalogueBLinearSemilinear.semilinearAction n K A σ ^ 2 = 1) {X : Type} [Group X]
    (Ψ : X ≃* fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ))
    {L : Subgroup X} (hL : IsComponent L) : ExcCompModel p L := by
  have hn : 2 ≤ n := by omega
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
  exact excCompModel_of_simple_model (exists_mul_ne_of_isQuasisimple hL'.1 E)
    ((L.equivMapOfInjective Ψ'.toMonoidHom Ψ'.injective).trans E) hadm
    (Or.inl ⟨by decide, hstated⟩) (Or.inl ⟨rfl, Or.inr hn68⟩)

theorem excCompModel_psl_graphField {n : ℕ} (hn68 : n = 6 ∨ n = 8) {K : Type} [Field K]
    [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hord : orderOf (CatalogueBGraphField.graphFieldAction n K A σ) = 2) {X : Type} [Group X]
    (Ψ : X ≃* fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ)) {L : Subgroup X}
    (hL : IsComponent L) : ExcCompModel p L := by
  have hn : 3 ≤ n := by omega
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
  exact excCompModel_of_simple_model (exists_mul_ne_of_isQuasisimple hL'.1 (E.trans eQ))
    (((L.equivMapOfInjective Ψt.toMonoidHom Ψt.injective).trans E).trans eQ) hadm
    (Or.inl ⟨by decide, hstated⟩) (Or.inr (Or.inl ⟨rfl, hn68⟩))

theorem excCompModel_of_projectiveSL_involution {n : ℕ} (hn68 : n = 6 ∨ n = 8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {α : MulAut (LinearFlag.projectiveSL n K)} (hα2 : α ^ 2 = 1)
    (hα1 : α ≠ 1) (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1) (ε : ℕ) (hε : ε ≤ 1)
    (hαe : α = LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ * LinearFlag.dualAut n K ^ ε)
    (L : Subgroup (fixedSubgroup α)) (hL : IsComponent L) : ExcCompModel p L := by
  set e := CatalogueBLinearHigherB.nativeEquiv n K with he
  have hord : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans
      (orderOf_eq_prime hα2 hα1)
  have hsq : MulAut.congr e α ^ 2 = 1 := by rw [← map_pow, hα2, map_one]
  interval_cases ε
  · rw [pow_zero, mul_one] at hαe
    have hβ : MulAut.congr e α = CatalogueBLinearSemilinear.semilinearAction n K A σ := by
      rw [hαe, he, CatalogueBLinearHigherB.congr_semilinear]
    exact excCompModel_psl_field hn68 hp hp2 hf hK A σ hσ (hβ ▸ hsq)
      ((fixedSubgroupCongrEquiv e α).trans (MulEquiv.subgroupCongr (congrArg fixedSubgroup hβ)))
      hL
  · rw [pow_one] at hαe
    have hβ : MulAut.congr e α = CatalogueBGraphField.graphFieldAction n K A σ := by
      rw [hαe, he, CatalogueBLinearHigherB.congr_graphField]
    exact excCompModel_psl_graphField hn68 hp hp2 hf hK A σ hσ (hβ ▸ hord)
      ((fixedSubgroupCongrEquiv e α).trans (MulEquiv.subgroupCongr (congrArg fixedSubgroup hβ)))
      hL

end CFSG.ComponentClassification.Burgoyne.X10
