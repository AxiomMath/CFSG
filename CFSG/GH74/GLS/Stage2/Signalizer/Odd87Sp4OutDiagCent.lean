module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sp4OutCQ
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinearBranches

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG Subgroup Module CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open LinearMap (BilinForm)

theorem psl2CQ_SL_two {k : Type} [Field k] [Finite k] {p j : ℕ}
    (hadm : StatedLieAdmissible .PSL 2 p j) (hk : Nat.card k = p ^ j) :
    Psl2CQ p (Matrix.SpecialLinearGroup (Fin 2) k) :=
  ⟨j, hadm.2.1, Or.inl ⟨by decide,
    LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient 1 k hadm hk⟩⟩

theorem psl2CQ_statedSp_one {k : Type} [Field k] [Finite k] {p j : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hj : 1 ≤ j) (hk : Nat.card k = p ^ j) {L : Subgroup (StatedSp 1 k)}
    (hL : IsComponent L) : Psl2CQ p L := by
  let e := ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne k
  by_cases h3 : p ^ j = 3
  · have : Group.IsSolvable (StatedSp 1 k) :=
      LieType.HighestRoot.isSolvable_of_mulEquiv (hk.trans h3) e.symm
    exact absurd hL (OddInner.not_isComponent_of_isSolvable L)
  · have hq5 := OddInner.five_le_pow hp hp2 hj h3
    have hadm : StatedLieAdmissible .PSL 2 p j :=
      OddInner.admissible_PSL hp hj le_rfl (Or.inr (by omega)) (Or.inr h3)
    have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 k le_rfl
      (Or.inr (by rw [hk]; omega)) (Or.inr (by rw [hk]; exact h3))
    exact psl2CQ_of_isQuasisimple (LocalCores.isQuasisimple_of_mulEquiv e hSL)
      (Psl2CQ.of_mulEquiv e.symm (psl2CQ_SL_two hadm hk)) hL

theorem psl2CQ_isometryGroup_two {k W : Type} [Field k] [Finite k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {p j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hj : 1 ≤ j)
    (hk : Nat.card k = p ^ j) (B : BilinForm k W) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hW : finrank k W = 2) {L : Subgroup (CatalogueBAlternatingIsometry.isometryGroup B)}
    (hL : IsComponent L) : Psl2CQ p L := by
  obtain ⟨e⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp B hB hnd (r := 1) (by omega)
  exact psl2CQ_of_component_equiv e (fun M hM => psl2CQ_statedSp_one hp hp2 hj hk hM) hL

theorem psl2CQ_GL_two {k : Type} [Field k] [Finite k] {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j)
    (hk : Nat.card k = p ^ j) {L : Subgroup (GL (Fin 2) k)} (hL : IsComponent L) :
    Psl2CQ p L := by
  by_cases hsmall : 2 = 1 ∨ 2 = 2 ∧ (Nat.card k = 2 ∨ Nat.card k = 3)
  · have := CatalogueBGeneralLinear.generalLinear_small_solvable 2 k hsmall
    exact absurd hL (OddInner.not_isComponent_of_isSolvable L)
  obtain ⟨hn2, h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters 2 k (by norm_num) hsmall
  have : Group.IsPerfect L := hL.1.1
  have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
  obtain rfl := CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange 2 k hn2 h22 h23
    L hL.2
  have hadm : StatedLieAdmissible .PSL 2 p j :=
    OddInner.admissible_PSL hp hj hn2 (by rw [← hk]; exact h22) (by rw [← hk]; exact h23)
  exact Psl2CQ.of_mulEquiv
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm
    (psl2CQ_SL_two hadm hk)

theorem psl2CQ_unitary_two {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {sigma : E ≃+* E} {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : finrank E W = 2)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    {L : Subgroup (CatalogueBUnitaryIsometry.isometryGroup h)} (hL : IsComponent L) :
    Psl2CQ ℓ L := by
  have hq3 := OddInner.three_le_pow hℓ hℓ2 he
  have hfix := OddInner.card_fixedSubfield hsigma hne hE
  by_cases h3 : ℓ ^ e = 3
  · have := CatalogueBUnitaryIsometry.isometry_two_three_solvable h hsym hnd hsigma hne hW
      (hfix.trans h3)
    exact absurd hL (OddInner.not_isComponent_of_isSolvable L)
  · have hq5 := OddInner.five_le_pow hℓ hℓ2 he h3
    have hquasi := CatalogueBUnitaryIsometry.specialIsometry_two_quasisimple h hsym hnd hsigma
      hne hW (by rw [hfix]; omega) (by rw [hfix]; exact h3)
    obtain ⟨-, -, eSL, -⟩ := CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
      sigma h hsym hnd hsigma hne hW
    have hadm : StatedLieAdmissible .PSL 2 ℓ e :=
      OddInner.admissible_PSL hℓ he le_rfl (Or.inr (by omega)) (Or.inr h3)
    exact psl2CQ_of_commutator_le hquasi (Abelianization.commutator_subset_ker _)
      (Psl2CQ.of_mulEquiv eSL (psl2CQ_SL_two hadm hfix)) hL

theorem psl2CQ_similitudeCentralizer_sq_plus {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (hdim : finrank K V = 2 * 2)
    {B : BilinForm K V} (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : LinearMap.GeneralLinearGroup K V} (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1)
    {d : K} (hd0 : d ≠ 0) (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w) {l : K}
    (hl : l ^ 2 = d) (h1 : μ / d = 1) {L : Subgroup (similitudeCentralizer B A)}
    (hL : IsComponent L) : Psl2CQ ℓ L := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hl
    exact hd0 hl.symm
  have hAA' : (A : Module.End K V) * (A : Module.End K V) = (l ^ 2) • 1 := by
    rw [hl]
    exact hAA
  obtain ⟨-, hsplit, -⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2 hf hK
    (by omega) hdim hB hBnd hAns hd0 hAA hAμ
  obtain ⟨hP, hM, hpos, -⟩ := hsplit l hl
  obtain ⟨-, haltP, haltM, hndP, hndM, e, -⟩ := hpos h1
  have hP' := Submodule.one_le_finrank_iff.mpr hP
  have hM' := Submodule.one_le_finrank_iff.mpr hM
  obtain ⟨a, ha⟩ := CatalogueBAlternatingIsometry.even_finrank _ haltP hndP
  obtain ⟨b, hb⟩ := CatalogueBAlternatingIsometry.even_finrank _ haltM hndM
  have hc : IsCompl (eigenPlus l (A : Module.End K V)) (eigenMinus l (A : Module.End K V)) :=
    isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hAA')
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hdP : finrank K (eigenPlus l (A : Module.End K V)) = 2 := by omega
  have hdM : finrank K (eigenMinus l (A : Module.End K V)) = 2 := by omega
  exact psl2CQ_of_component_equiv
    (e.trans (MulEquiv.prodCongr (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _)
      (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _)))
    (fun M hMc => psl2CQ_prod
      (fun M₁ hM₁ => psl2CQ_isometryGroup_two hℓ hℓ2 hf hK _ haltP hndP hdP hM₁)
      (fun M₂ hM₂ => psl2CQ_isometryGroup_two hℓ hℓ2 hf hK _ haltM hndM hdM hM₂) hMc) hL

theorem psl2CQ_similitudeCentralizer_sq_minus {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (hdim : finrank K V = 2 * 2)
    {B : BilinForm K V} (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : LinearMap.GeneralLinearGroup K V} (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1)
    {d : K} (hd0 : d ≠ 0) (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w) {l : K}
    (hl : l ^ 2 = d) (h1 : μ / d = -1) {L : Subgroup (similitudeCentralizer B A)}
    (hL : IsComponent L) : Psl2CQ ℓ L := by
  obtain ⟨-, hsplit, -⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2 hf hK
    (by omega) hdim hB hBnd hAns hd0 hAA hAμ
  obtain ⟨-, -, -, hneg⟩ := hsplit l hl
  obtain ⟨-, -, hdP, -, -, -, e, -⟩ := hneg h1
  let bP : Basis (Fin 2) K (eigenPlus l (A : Module.End K V)) :=
    Module.finBasisOfFinrankEq K _ hdP
  exact psl2CQ_of_component_equiv
    (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv))
    (fun M hMc => psl2CQ_GL_two hℓ hf hK hMc) hL

theorem psl2CQ_similitudeCentralizer_nonsq_plus {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (hdim : finrank K V = 2 * 2)
    {B : BilinForm K V} (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : LinearMap.GeneralLinearGroup K V} (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1)
    {d : K} (hd0 : d ≠ 0) (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w)
    (hsq : ∀ l : K, l ^ 2 ≠ d) (h1 : μ / d = 1) {L : Subgroup (similitudeCentralizer B A)}
    (hL : IsComponent L) : Psl2CQ ℓ L := by
  obtain ⟨-, -, hnonsplit⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2 hf hK
    (by omega) hdim hB hBnd hAns hd0 hAA hAμ
  obtain ⟨-, hF, hcard, hfinrank, -, -, -, -, hpos, -⟩ := hnonsplit hsq
  let : Field (scalarSquareField (A : Module.End K V)) := hF.toField
  have hEodd : Odd (Nat.card (scalarSquareField (A : Module.End K V))) := by
    rw [hcard]
    exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
  have := CatalogueBSymplecticB.finite_of_odd_card hEodd
  have : Module.Finite (scalarSquareField (A : Module.End K V)) V :=
    CatalogueBOrthogonalScalarSquareField.evaluationModule_finite (A : Module.End K V)
  obtain ⟨BE, -, hBEalt, hBEnd, -, hiff⟩ := hpos h1
  exact psl2CQ_of_component_equiv
    ((CatalogueBSymplecticB.centralizerSimilitudeEquiv B A).symm.trans
      (CatalogueBSymplecticB.evaluationIsometryEquiv B A
        (CatalogueBAlternatingIsometry.isometryGroup BE)
        (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w)
        (CatalogueBAlternatingIsometry.mem_isometryGroup_iff BE) hiff))
    (fun M hMc => psl2CQ_isometryGroup_two (j := 2 * f) hℓ hℓ2 (by omega)
      (by rw [hcard, ← pow_mul, mul_comm]) BE hBEalt hBEnd hfinrank hMc) hL

theorem psl2CQ_similitudeCentralizer_nonsq_minus {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (hdim : finrank K V = 2 * 2)
    {B : BilinForm K V} (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : LinearMap.GeneralLinearGroup K V} (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1)
    {d : K} (hd0 : d ≠ 0) (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w)
    (hsq : ∀ l : K, l ^ 2 ≠ d) (h1 : μ / d = -1) {L : Subgroup (similitudeCentralizer B A)}
    (hL : IsComponent L) : Psl2CQ ℓ L := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨-, -, hnonsplit⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2 hf hK
    (by omega) hdim hB hBnd hAns hd0 hAA hAμ
  obtain ⟨-, hF, hcard, hfinrank, bar, hbar, -, hbarbar, -, hneg⟩ := hnonsplit hsq
  let : Field (scalarSquareField (A : Module.End K V)) := hF.toField
  have hEodd : Odd (Nat.card (scalarSquareField (A : Module.End K V))) := by
    rw [hcard]
    exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
  have := CatalogueBSymplecticB.finite_of_odd_card hEodd
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
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
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
  exact psl2CQ_of_component_equiv
    ((CatalogueBSymplecticB.centralizerSimilitudeEquiv B A).symm.trans
      (CatalogueBSymplecticB.evaluationIsometryEquiv B A
        (CatalogueBUnitaryIsometry.isometryGroup h')
        (fun φ => ∀ v w, h (φ v) (φ w) = h v w)
        (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff))
    (fun M hMc => psl2CQ_unitary_two hℓ hℓ2 hf hcard hfinrank h' hsymm hnd' hsigma hne hMc) hL

theorem psl2_similitudeCentralizer_two {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hdim : finrank K V = 2 * 2)
    {B : BilinForm K V} (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {A : LinearMap.GeneralLinearGroup K V} (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1)
    {d : K} (hd0 : d ≠ 0) (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w)
    {L : Subgroup (similitudeCentralizer B A)} (hL : IsComponent L) :
    Psl2CQ ℓ L := by
  obtain ⟨hε, -, -⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2 hf hK
    (by omega) hdim hB hBnd hAns hd0 hAA hAμ
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    rcases hε with h1 | h1
    · exact psl2CQ_similitudeCentralizer_sq_plus hℓ hℓ2 hf hK hdim hB hBnd hAns hd0 hAA hAμ
        hl h1 hL
    · exact psl2CQ_similitudeCentralizer_sq_minus hℓ hℓ2 hf hK hdim hB hBnd hAns hd0 hAA hAμ
        hl h1 hL
  · push Not at hsq
    rcases hε with h1 | h1
    · exact psl2CQ_similitudeCentralizer_nonsq_plus hℓ hℓ2 hf hK hdim hB hBnd hAns hd0 hAA hAμ
        hsq h1 hL
    · exact psl2CQ_similitudeCentralizer_nonsq_minus hℓ hℓ2 hf hK hdim hB hBnd hAns hd0 hAA hAμ
        hsq h1 hL

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
