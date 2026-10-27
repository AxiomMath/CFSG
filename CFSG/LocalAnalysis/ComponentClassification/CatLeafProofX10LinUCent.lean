module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinGL
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Lin

open CFSG Subgroup Module CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatLeafProof.X10Sp (CentralModel centralModel_unitary_component)

@[expose] def linUInnerTuples (n f : ℕ) : Set (StatedLieTag × ℕ × ℕ) :=
  {x | (∃ k, 3 ≤ k ∧ k < n ∧ x = (.PSU, k, f)) ∨ (Even n ∧ x = (.PSL, n / 2, 2 * f))}

theorem neg_one_mem_sesqUnitaryGroup {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    {σ : E →+* E} (C : W →ₛₗ[σ] W →ₗ[E] E) : (-1 : LinearMap.GeneralLinearGroup E W) ∈
      sesqUnitaryGroup C := fun x y => by
  change C (-x) (-y) = C x y
  simp

theorem neg_one_central_sesq {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    {σ : E →+* E} {C : W →ₛₗ[σ] W →ₗ[E] E} {g : sesqUnitaryGroup C}
    (hg : (g : LinearMap.GeneralLinearGroup E W) = -1) (u : sesqUnitaryGroup C) :
    g * u = u * g ∧ g * g = 1 := by
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, hg, neg_one_mul, mul_neg_one]
  · rw [Subgroup.coe_mul, hg, neg_one_mul, neg_neg, Subgroup.coe_one]

theorem unitaryFactor_component_cases {p f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) {W : Type} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (hW : 1 ≤ finrank E W) {C : W →ₛₗ[h.bar] W →ₗ[E] E} (hC : C.IsSymm) (hCl : C.SeparatingLeft)
    {M : Type} [Group M] (ρ : M →* sesqUnitaryGroup C) (hρi : Function.Injective ρ)
    (hρc : IsComponent ρ.range) :
    (∃ x : M, ((ρ x : sesqUnitaryGroup C) : LinearMap.GeneralLinearGroup E W) = -1) ∨
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
    let m : sesqUnitaryGroup C := ⟨-1, neg_one_mem_sesqUnitaryGroup C⟩
    have hm : σ m ∈ CatalogueBUnitaryIsometry.specialIsometry C := by
      refine (CatalogueBUnitaryIsometry.mem_specialIsometry_iff
        (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq) C (σ m)).2 ?_
      change LinearMap.det (-LinearMap.id : W →ₗ[E] W) = 1
      rw [show (-LinearMap.id : W →ₗ[E] W) = (-1 : E) • LinearMap.id by simp,
        LinearMap.det_smul, LinearMap.det_id, mul_one, hd]
      norm_num
    rw [← hNS] at hm
    obtain ⟨y, hy, hym⟩ := Subgroup.mem_map.1 hm
    obtain ⟨x, rfl⟩ := hy
    refine ⟨x, ?_⟩
    have := σ.injective hym
    rw [this]
  · right
    refine ⟨h3, (centralModel_unitary_component h.prime hp h.one_le h.card_eq_sq h3 C hC hnd
      hsig2 hsig1 hsig hN).of_mulEquiv eM⟩

theorem sesqCentralizer_component_cases {p f : ℕ} {E : Type} [Field E]
    (h : UnitaryFieldData p f E) (hp : p ≠ 2) {V : Type} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2)
    {M : Subgroup (Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B)))} (hM : IsComponent M) :
    (∃ z ∈ M, (∀ y ∈ M, z * y = y * z) ∧ z * z = 1 ∧
      ∀ c : E, unitaryOp ((z : Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B))) :
        sesqUnitaryGroup B) ≠ c • 1) ∨
    ModelIn p (linUInnerTuples (finrank E V) f) M := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  have hodd : Odd (Nat.card E) := by
    rw [h.card]
    exact (h.prime.odd_of_ne_two hp).pow
  have h2 : (2 : E) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
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
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMm
    have hns : ∀ x : Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B)),
        ((((e x).1 : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp A))) :
            Module.End E (eigenPlus l (unitaryOp A))) = -1 ∧
          (((e x).2 : LinearMap.GeneralLinearGroup E (eigenMinus l (unitaryOp A))) :
            Module.End E (eigenMinus l (unitaryOp A))) = 1) ∨
        ((((e x).1 : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp A))) :
            Module.End E (eigenPlus l (unitaryOp A))) = 1 ∧
          (((e x).2 : LinearMap.GeneralLinearGroup E (eigenMinus l (unitaryOp A))) :
            Module.End E (eigenMinus l (unitaryOp A))) = -1) →
        ∀ c : E, unitaryOp (x : sesqUnitaryGroup B) ≠ c • 1 := by
      intro x hx c hc
      obtain ⟨hx₁, hx₂⟩ := hres x
      have e₁ := LinearMap.congr_fun hx₁ ⟨v, hv⟩
      have e₂ := LinearMap.congr_fun hx₂ ⟨w, hw⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, hc, LinearMap.smul_apply,
        Module.End.one_apply] at e₁ e₂
      rcases hx with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha] at e₁
        rw [hb] at e₂
        simp only [LinearMap.neg_apply, Module.End.one_apply, Submodule.coe_neg] at e₁ e₂
        have hc1 : c = -1 := by
          have h3 : (c + 1) • v = 0 := by rw [add_smul, one_smul, ← e₁, neg_add_cancel]
          have := (smul_eq_zero.1 h3).resolve_right hv0
          linear_combination this
        have hc2 : c = 1 := by
          have h3 : (c - 1) • w = 0 := by rw [sub_smul, one_smul, ← e₂, sub_self]
          have := (smul_eq_zero.1 h3).resolve_right hw0
          linear_combination this
        exact h2 (by linear_combination hc1 - hc2)
      · rw [ha] at e₁
        rw [hb] at e₂
        simp only [LinearMap.neg_apply, Module.End.one_apply, Submodule.coe_neg] at e₁ e₂
        have hc1 : c = 1 := by
          have h3 : (c - 1) • v = 0 := by rw [sub_smul, one_smul, ← e₁, sub_self]
          have := (smul_eq_zero.1 h3).resolve_right hv0
          linear_combination this
        have hc2 : c = -1 := by
          have h3 : (c + 1) • w = 0 := by rw [add_smul, one_smul, ← e₂, neg_add_cancel]
          have := (smul_eq_zero.1 h3).resolve_right hw0
          linear_combination this
        exact h2 (by linear_combination hc2 - hc1)
    have hMe := LocalCores.isComponent_map_mulEquiv e hM
    rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
        hMe with h2' | h1'
    ·
      have h2'' : ∀ x ∈ M, (e x).2 = 1 := fun x hx => h2' _ ⟨x, hx, rfl⟩
      obtain ⟨ρ, hρi, hρc, hρ⟩ := OddClassSelector.restrict_component e hM h2''
      rcases unitaryFactor_component_cases h hp hP' (hsymm _) hlP ρ hρi hρc with
        ⟨x, hx⟩ | ⟨h3, hm⟩
      · left
        have hx1 : ((e x).1 : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp A))) =
            -1 := by
          rw [← hρ x]
          exact hx
        refine ⟨x, x.2, fun y _ => e.injective ?_, e.injective ?_, hns x (Or.inl ⟨?_, ?_⟩)⟩
        · rw [map_mul, map_mul]
          exact Prod.ext (neg_one_central_sesq hx1 _).1
            (by rw [Prod.snd_mul, Prod.snd_mul, h2'' x x.2, one_mul, mul_one])
        · rw [map_mul, map_one]
          exact Prod.ext (neg_one_central_sesq hx1 1).2
            (by rw [Prod.snd_mul, Prod.snd_one, h2'' x x.2, one_mul])
        · rw [hx1]
          rfl
        · rw [h2'' x x.2]
          rfl
      · exact Or.inr ⟨.PSU, _, f, Or.inl ⟨_, h3, by omega, rfl⟩, hm⟩
    ·
      let e' := e.trans MulEquiv.prodComm
      have h2'' : ∀ x ∈ M, (e' x).2 = 1 := fun x hx => h1' _ ⟨x, hx, rfl⟩
      obtain ⟨ρ, hρi, hρc, hρ⟩ := OddClassSelector.restrict_component e' hM h2''
      rcases unitaryFactor_component_cases h hp hM' (hsymm _) hlM ρ hρi hρc with
        ⟨x, hx⟩ | ⟨h3, hm⟩
      · left
        have hx2 : ((e x).2 : LinearMap.GeneralLinearGroup E (eigenMinus l (unitaryOp A))) =
            -1 := by
          have := hρ x
          change ρ x = (e x).2 at this
          rw [← this]
          exact hx
        have hx1 : (e x).1 = 1 := h2'' x x.2
        refine ⟨x, x.2, fun y _ => e.injective ?_, e.injective ?_, hns x (Or.inr ⟨?_, ?_⟩)⟩
        · rw [map_mul, map_mul]
          exact Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, hx1, one_mul, mul_one])
            (neg_one_central_sesq hx2 _).1
        · rw [map_mul, map_one]
          exact Prod.ext (by rw [Prod.fst_mul, Prod.fst_one, hx1, one_mul])
            (neg_one_central_sesq hx2 1).2
        · rw [hx1]
          rfl
        · rw [hx2]
          rfl
      · exact Or.inr ⟨.PSU, _, f, Or.inl ⟨_, h3, by omega, rfl⟩, hm⟩
  ·
    right
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
      exact ⟨.PSL, _, 2 * f, Or.inr ⟨⟨finrank E (eigenPlus l (unitaryOp A)), by omega⟩, by
        rw [show finrank E V / 2 = finrank E (eigenPlus l (unitaryOp A)) by omega]⟩,
        centralModel_GL_component_two_le h.prime hp (by have := h.one_le; omega) h.card h2'
          (Or.inr (by rw [h.card]; omega)) hN'⟩

end CFSG.ComponentClassification.CatLeafProof.X10Lin
