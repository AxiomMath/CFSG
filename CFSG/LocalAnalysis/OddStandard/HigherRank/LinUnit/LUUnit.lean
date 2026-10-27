module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinGL
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer
public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUDefs

public noncomputable section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG Subgroup Module CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatLeafProof.X10Lin
  (ModelIn modelIn_of_component_equiv centralModel_GL_component_two_le)
open CFSG.ComponentClassification.CatLeafProof.X10Sp
  (CentralModel centralModel_SL centralModel_unitary_component)

theorem unitaryFactor_component_model {p f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) {W : Type} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (hW : 1 ≤ finrank E W) {C : W →ₛₗ[h.bar] W →ₗ[E] E} (hC : C.IsSymm) (hCl : C.SeparatingLeft)
    {M : Type} [Group M] (ρ : M →* sesqUnitaryGroup C) (hρi : Function.Injective ρ)
    (hρc : IsComponent ρ.range) :
    (finrank E W = 2 ∧ CentralModel p .PSL 2 f M) ∨
      (3 ≤ finrank E W ∧ CentralModel p .PSU (finrank E W) f M) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  have hnd := CatalogueBUnitaryB.nondegenerate_of_isSymm hC hCl
  obtain ⟨hsig2, hsig1, hfix⟩ :=
    CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f h.card_eq_sq
  have hsig := CatalogueBUnitaryTwo.unitaryFieldConjugation_apply p f h.card_eq_sq
  have : Finite (CatalogueBUnitaryIsometry.isometryGroup
      (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq) C) :=
    CatalogueBUnitaryIsometry.isometryGroupFinite _
  set σ := CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h C
  have hN := LocalCores.isComponent_map_mulEquiv σ hρc
  have eM : M ≃* (ρ.range.map σ.toMonoidHom) :=
    (MonoidHom.ofInjective hρi).trans (ρ.range.equivMapOfInjective σ.toMonoidHom σ.injective)
  rcases Nat.lt_or_ge (finrank E W) 3 with h3 | h3
  · left
    rcases Nat.lt_or_ge (finrank E W) 2 with h1 | h2
    · exfalso
      have := CatalogueBUnitaryIsometry.isometry_one_solvable
        (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq) C (by omega)
      exact OddInner.not_isComponent_of_isSolvable _ hN
    have hd : finrank E W = 2 := by omega
    refine ⟨hd, ?_⟩
    have hq3 := OddInner.three_le_pow h.prime hp h.one_le
    by_cases hq : p ^ f = 3
    · exfalso
      have := CatalogueBUnitaryIsometry.isometry_two_three_solvable C hC hnd hsig2 hsig1 hd
        (hfix.trans hq)
      exact OddInner.not_isComponent_of_isSolvable _ hN
    have hS := CatalogueBUnitaryIsometry.specialIsometry_two_quasisimple C hC hnd hsig2 hsig1 hd
      (by rw [hfix]; omega) (by rw [hfix]; exact hq)
    have hNS := LocalAnalysis.ComponentInitial.CentralQuotientLift.eq_of_isComponent_of_quasisimple
      hS (Abelianization.commutator_subset_ker _) hN
    obtain ⟨-, -, eSL, -⟩ := CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
      (CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq) C hC hnd hsig2 hsig1 hd
    have hadm : StatedLieAdmissible .PSL 2 p f :=
      OddInner.admissible_PSL h.prime h.one_le le_rfl (Or.inr (by omega)) (Or.inr hq)
    exact (centralModel_SL hadm hfix).of_mulEquiv
      ((eM.trans (MulEquiv.subgroupCongr hNS)).trans eSL)
  · right
    refine ⟨h3, (centralModel_unitary_component h.prime hp h.one_le h.card_eq_sq h3 C hC hnd
      hsig2 hsig1 hsig hN).of_mulEquiv eM⟩

theorem sesqCentralizer_modelIn {p f : ℕ} {E : Type} [Field E]
    (h : UnitaryFieldData p f E) (hp : p ≠ 2) {V : Type} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2)
    {M : Subgroup (Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B)))} (hM : IsComponent M) :
    ModelIn p (luUniTuples (finrank E V) f) M := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨l, -, -, hN, hP, hMm, hcompl, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl hA
  have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
    ⟨fun x y => hB.eq (x : V) (y : V)⟩
  have hdim := Submodule.finrank_add_eq_of_isCompl hcompl
  have hP' := Submodule.one_le_finrank_iff.mpr hP
  have hM' := Submodule.one_le_finrank_iff.mpr hMm
  rcases hN with hN | hN
  ·
    obtain ⟨-, hlP, hlM, e, hres⟩ := hsplit hN
    have hMe := LocalCores.isComponent_map_mulEquiv e hM
    rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
        hMe with h2' | h1'
    ·
      have h2'' : ∀ x ∈ M, (e x).2 = 1 := fun x hx => h2' _ ⟨x, hx, rfl⟩
      obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component e hM h2''
      rcases unitaryFactor_component_model h hp hP' (hsymm _) hlP ρ hρi hρc with
        ⟨-, hm⟩ | ⟨h3, hm⟩
      · exact ⟨.PSL, 2, f, Or.inr (Or.inl rfl), hm⟩
      · exact ⟨.PSU, _, f, Or.inl ⟨_, h3, by omega, rfl⟩, hm⟩
    ·
      let e' := e.trans MulEquiv.prodComm
      have h2'' : ∀ x ∈ M, (e' x).2 = 1 := fun x hx => h1' _ ⟨x, hx, rfl⟩
      obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component e' hM h2''
      rcases unitaryFactor_component_model h hp hM' (hsymm _) hlM ρ hρi hρc with
        ⟨-, hm⟩ | ⟨h3, hm⟩
      · exact ⟨.PSL, 2, f, Or.inr (Or.inl rfl), hm⟩
      · exact ⟨.PSU, _, f, Or.inl ⟨_, h3, by omega, rfl⟩, hm⟩
  ·
    obtain ⟨-, -, -, hdim2, -, -, e, -⟩ := hpaired hN
    refine modelIn_of_component_equiv (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
      (Module.finBasis E (eigenPlus l (unitaryOp A)))).toMulEquiv)) (fun N hN' => ?_) hM
    rcases Nat.lt_or_ge (finrank E (eigenPlus l (unitaryOp A))) 2 with h1 | h2'
    · exfalso
      have := CatalogueBGeneralLinear.generalLinear_small_solvable
        (finrank E (eigenPlus l (unitaryOp A))) E (Or.inl (by omega))
      exact OddInner.not_isComponent_of_isSolvable N hN'
    · have h9 : 9 ≤ p ^ (2 * f) := by
        rw [pow_mul']
        exact Nat.pow_le_pow_left (OddInner.three_le_pow h.prime hp h.one_le) 2
      exact ⟨.PSL, _, 2 * f, Or.inr (Or.inr ⟨⟨finrank E (eigenPlus l (unitaryOp A)), by omega⟩, by
        rw [show finrank E V / 2 = finrank E (eigenPlus l (unitaryOp A)) by omega]⟩),
        centralModel_GL_component_two_le h.prime hp (by have := h.one_le; omega) h.card h2'
          (Or.inr (by rw [h.card]; omega)) hN'⟩

end CFSG.OddStandard.HigherRank.LinUnit
