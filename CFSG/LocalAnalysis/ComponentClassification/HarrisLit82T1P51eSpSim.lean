module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e.Sp

open CFSG Subgroup Module CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.ComponentClassification.CatLeafProof.X10Sp
open LinearMap (BilinForm)
open scoped MatrixGroups

theorem centralModel_GL_component' {k : Type} [Field k] [Finite k] {ℓ j n : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hj : 1 ≤ j) (hk : Nat.card k = ℓ ^ j) (hn : 2 ≤ n)
    {L : Subgroup (GL (Fin n) k)} (hL : IsComponent L) : CentralModel ℓ .PSL n j L := by
  have hodd : Odd (ℓ ^ j) := (hℓ.odd_of_ne_two hℓ2).pow
  by_cases hsmall : n = 2 ∧ Nat.card k = 3
  · have := CatalogueBGeneralLinear.generalLinear_small_solvable n k
      (Or.inr ⟨hsmall.1, Or.inr hsmall.2⟩)
    exact absurd hL (CatLeafProof.OddInner.not_isComponent_of_isSolvable L)
  have h22 : n ≠ 2 ∨ Nat.card k ≠ 2 := Or.inr (by
    rw [hk]
    intro h
    rw [h] at hodd
    exact (by decide : ¬ Odd 2) hodd)
  have h23 : n ≠ 2 ∨ Nat.card k ≠ 3 := by
    by_cases h2 : n = 2
    · exact Or.inr fun h3 => hsmall ⟨h2, h3⟩
    · exact Or.inl h2
  have : Group.IsPerfect L := hL.1.1
  have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
  obtain rfl := CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange n k hn h22 h23
    L hL.2
  have hadm : StatedLieAdmissible .PSL n ℓ j :=
    CatLeafProof.OddInner.admissible_PSL hℓ hj hn (by rw [← hk]; exact h22)
      (by rw [← hk]; exact h23)
  exact (centralModel_SL hadm hk).of_mulEquiv
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm

theorem centralModel_unitary_two_component {E W : Type} [Field E] [Finite E] [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] {sigma : E ≃+* E} {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : Module.finrank E W = 2)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    {L : Subgroup (CatalogueBUnitaryIsometry.isometryGroup h)} (hL : IsComponent L) :
    CentralModel ℓ .PSL 2 e L := by
  have hfix := CatLeafProof.OddInner.card_fixedSubfield hsigma hne hE
  by_cases h3 : ℓ ^ e = 3
  · have := CatalogueBUnitaryIsometry.isometry_two_three_solvable h hsym hnd hsigma hne hW
      (hfix.trans h3)
    exact absurd hL (CatLeafProof.OddInner.not_isComponent_of_isSolvable L)
  have hq5 := CatLeafProof.OddInner.five_le_pow hℓ hℓ2 he h3
  have hquasi := CatalogueBUnitaryIsometry.specialIsometry_two_quasisimple h hsym hnd hsigma
    hne hW (by rw [hfix]; omega) (by rw [hfix]; exact h3)
  obtain ⟨-, -, eSL, -⟩ := CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
    sigma h hsym hnd hsigma hne hW
  have hadm : StatedLieAdmissible .PSL 2 ℓ e :=
    CatLeafProof.OddInner.admissible_PSL hℓ he le_rfl (Or.inr (by omega)) (Or.inr h3)
  obtain rfl := LocalAnalysis.ComponentInitial.CentralQuotientLift.eq_of_isComponent_of_quasisimple
    hquasi (Abelianization.commutator_subset_ker _) hL
  exact (centralModel_SL hadm hfix).of_mulEquiv eSL

theorem sim_comp_types {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {r : ℕ} (hr : 2 ≤ r) (hdim : finrank K V = 2 * r)
    {B : BilinForm K V} (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : LinearMap.GeneralLinearGroup K V} (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1)
    {d : K} (hd0 : d ≠ 0) (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1)
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = B v w)
    {M : Subgroup (similitudeCentralizer B A)} (hM : IsComponent M) :
    (∃ k, 1 ≤ k ∧ Nonempty (M ≃* StatedSp k K) ∧ ∀ x ∈ M, ∀ c : K,
      ((x : LinearMap.GeneralLinearGroup K V) : Module.End K V) = c • 1 → c = 1) ∨
    CentralModel ℓ .PSL r f M ∨ CentralModel ℓ .PSU r f M := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hAμ' : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = (1 : K) * B v w :=
    fun v w => by rw [one_mul]; exact hAμ v w
  obtain ⟨hε, hsplit, hnonsplit⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2
    hf hK (by omega) hdim hB hBnd hAns hd0 hAA hAμ'
  have hd : d = 1 ∨ d = -1 := by
    rcases hε with h | h
    · left
      rw [div_eq_one_iff_eq hd0] at h
      exact h.symm
    · right
      have := (div_eq_iff hd0).1 h
      linear_combination this
  rcases hd with rfl | rfl
  ·
    left
    obtain ⟨hP, hMm, hpos, -⟩ := hsplit 1 (one_pow 2)
    obtain ⟨-, haltP, haltM, hndP, hndM, e, hres⟩ := hpos (div_one 1)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMm
    have hscal : ∀ (x : similitudeCentralizer B A) (c : K) (u : V), u ≠ 0 →
        ((x : LinearMap.GeneralLinearGroup K V) : Module.End K V) u = u →
        ((x : LinearMap.GeneralLinearGroup K V) : Module.End K V) = c • 1 → c = 1 := by
      intro x c u hu0 hxu hc
      rw [hc, LinearMap.smul_apply, Module.End.one_apply] at hxu
      have h3 : (c - 1) • u = 0 := by rw [sub_smul, one_smul, hxu, sub_self]
      have := (smul_eq_zero.1 h3).resolve_right hu0
      linear_combination this
    have hMe := LocalCores.isComponent_map_mulEquiv e hM
    have hfin : ∀ {W : Submodule K V}, (B.domRestrict₁₂ W W).IsAlt →
        (B.domRestrict₁₂ W W).Nondegenerate → W ≠ ⊥ →
        ∃ k, 1 ≤ k ∧ Nonempty (LocalAnalysis.ComponentInitial.sesqUnitaryGroup
          (B.domRestrict₁₂ W W) ≃* StatedSp k K) := by
      intro W halt hnd hW0
      obtain ⟨m, hdm, -⟩ :=
        CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic _ halt hnd
      obtain ⟨eS⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _ halt hnd hdm
      have h1 : 1 ≤ finrank K W := Submodule.one_le_finrank_iff.mpr hW0
      exact ⟨m, by omega, ⟨(sesqUnitaryIsometryEquiv _).trans eS⟩⟩
    rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
        hMe with h2' | h1'
    ·
      have h2'' : ∀ x ∈ M, (e x).2 = 1 := fun x hx => h2' _ ⟨x, hx, rfl⟩
      obtain ⟨ρ, hρi, hρc, hρ⟩ := OddClassSelector.restrict_component e hM h2''
      have htop := eq_top_of_isComponent_sesqUnitaryGroup hℓ hℓ2 hf hK _ haltP hndP
        (by have := Submodule.one_le_finrank_iff.mpr hP; omega) hρc
      obtain ⟨k, hk, ⟨eS⟩⟩ := hfin haltP hndP hP
      refine ⟨k, hk, ⟨((MonoidHom.ofInjective hρi).trans
        ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)).trans eS⟩, fun x hx c hc => ?_⟩
      refine hscal x c w hw0 ?_ hc
      have e₂ := LinearMap.congr_fun (hres x).2 ⟨w, hw⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at e₂
      rw [h2'' x hx] at e₂
      exact e₂.symm
    ·
      let e' := e.trans MulEquiv.prodComm
      have h2'' : ∀ x ∈ M, (e' x).2 = 1 := fun x hx => h1' _ ⟨x, hx, rfl⟩
      obtain ⟨ρ, hρi, hρc, hρ⟩ := OddClassSelector.restrict_component e' hM h2''
      have htop := eq_top_of_isComponent_sesqUnitaryGroup hℓ hℓ2 hf hK _ haltM hndM
        (by have := Submodule.one_le_finrank_iff.mpr hMm; omega) hρc
      obtain ⟨k, hk, ⟨eS⟩⟩ := hfin haltM hndM hMm
      refine ⟨k, hk, ⟨((MonoidHom.ofInjective hρi).trans
        ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)).trans eS⟩, fun x hx c hc => ?_⟩
      refine hscal x c v hv0 ?_ hc
      have e₁ := LinearMap.congr_fun (hres x).1 ⟨v, hv⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at e₁
      have h1x : (e x).1 = 1 := h2'' x hx
      rw [h1x] at e₁
      exact e₁.symm
  ·
    right
    have h1 : (1 : K) / -1 = -1 := by rw [div_neg, div_one]
    by_cases hsq : ∃ l : K, l ^ 2 = -1
    ·
      left
      obtain ⟨l, hl⟩ := hsq
      obtain ⟨-, -, -, hneg⟩ := hsplit l hl
      obtain ⟨-, -, hdP, -, -, -, e, -⟩ := hneg h1
      let bP : Basis (Fin r) K (eigenPlus l (A : Module.End K V)) :=
        Module.finBasisOfFinrankEq K _ hdP
      exact centralModel_of_component_equiv
        (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv))
        (fun N hN => centralModel_GL_component' hℓ hℓ2 hf hK hr hN) hM
    ·
      push Not at hsq
      obtain ⟨-, hF, hcard, hfinrank, bar, hbar, hpow, hbarbar, -, hneg⟩ := hnonsplit hsq
      let : Field (scalarSquareField (A : Module.End K V)) := hF.toField
      have hEodd : Odd (Nat.card (scalarSquareField (A : Module.End K V))) := by
        rw [hcard]
        exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
      have := finite_of_odd_card hEodd
      have : Module.Finite (scalarSquareField (A : Module.End K V)) V :=
        CatalogueBOrthogonalScalarSquareField.evaluationModule_finite (A : Module.End K V)
      obtain ⟨h, -, hsymm, hsep, hiff⟩ := hneg h1
      let sigma := RingEquiv.ofBijective bar (Function.Involutive.bijective hbarbar)
      let h' : V →ₛₗ[sigma.toRingHom] V →ₗ[scalarSquareField (A : Module.End K V)]
        scalarSquareField (A : Module.End K V) := h
      have hnd' : h'.Nondegenerate :=
        ⟨hsep, fun y hy => hsep y fun x => by
          rw [← hsymm.eq x y]
          exact (congrArg bar (hy x)).trans (map_zero bar)⟩
      have hsigma : sigma ^ 2 = 1 := RingEquiv.ext hbarbar
      have hne : sigma ≠ 1 := by
        intro heq
        let x : scalarSquareField (A : Module.End K V) :=
          ⟨A, Algebra.self_mem_adjoin_singleton K _⟩
        have hx := hbar x 0 1 (by simp only [zero_smul, zero_add, one_smul, x])
        have hfix : bar x = x := DFunLike.congr_fun heq x
        rw [hfix] at hx
        simp only [zero_smul, zero_sub, one_smul, x] at hx
        have hA2 : (2 : K) • (A : Module.End K V) = 0 := by
          rw [two_smul]
          nth_rewrite 2 [hx]
          exact add_neg_cancel _
        apply hAns 0
        rw [zero_smul]
        calc (A : Module.End K V) = (2 : K)⁻¹ • ((2 : K) • (A : Module.End K V)) := by
              rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
          _ = 0 := by rw [hA2, smul_zero]
      have heq := (centralizerSimilitudeEquiv B A).symm.trans
          (evaluationIsometryEquiv B A (CatalogueBUnitaryIsometry.isometryGroup h')
            (fun φ => ∀ v w, h (φ v) (φ w) = h v w)
            (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff)
      rcases Nat.lt_or_ge r 3 with hr3 | hr3
      ·
        left
        obtain rfl : r = 2 := by omega
        exact centralModel_of_component_equiv heq
          (fun N hN => centralModel_unitary_two_component hℓ hℓ2 hf hcard hfinrank h' hsymm hnd'
            hsigma hne hN) hM
      · right
        have := centralModel_of_component_equiv heq
          (fun N hN => centralModel_unitary_component hℓ hℓ2 hf hcard (by omega) h' hsymm hnd'
            hsigma hne hpow hN) hM
        rwa [hfinrank] at this

end CFSG.ComponentClassification.HarrisLit.T1.P51e.Sp
