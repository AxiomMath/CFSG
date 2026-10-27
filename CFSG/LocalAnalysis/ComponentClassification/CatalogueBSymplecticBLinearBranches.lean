module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquare
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBConjugation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixedBranches
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFieldFixedPolarization

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticB

open LinearMap (BilinForm)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CatalogueBAlternatingIsometry CatalogueBProjectiveInvolution
  CatalogueBOrthogonalScalarSquareField CatalogueBOrthogonalScalarSquareForms

universe u v w

section General

variable {K : Type u} [Field K] {W : Type v} [AddCommGroup W] [Module K W]

@[expose] def sesqUnitaryIsometryEquiv (B : BilinForm K W) :
    sesqUnitaryGroup B ≃* isometryGroup B where
  toFun g := ⟨LinearMap.GeneralLinearGroup.toLinearEquiv g.val,
    (mem_isometryGroup_iff B _).mpr g.property⟩
  invFun g := ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv g.val,
    (mem_isometryGroup_iff B _).mp g.property⟩
  left_inv g := by
    apply Subtype.ext
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm_apply_apply g.val
  right_inv g := by
    apply Subtype.ext
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).apply_symm_apply g.val
  map_mul' g h := by
    apply Subtype.ext
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).map_mul g.val h.val

variable {V : Type w} [AddCommGroup V] [Module K V]

@[expose] def centralizerSimilitudeEquiv (B : BilinForm K V)
    (A : LinearMap.GeneralLinearGroup K V) :
    symplecticOperatorCentralizer B (A : Module.End K V) ≃*
      (sesqUnitaryGroup B ⊓ Subgroup.centralizer {A} :
        Subgroup (LinearMap.GeneralLinearGroup K V)) where
  toFun g := ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv g.val.val,
    (mem_isometryGroup_iff B _).mp g.val.property,
    Subgroup.mem_centralizer_singleton_iff.mpr (Units.ext (LinearMap.ext fun x =>
      (mem_symplecticOperatorCentralizer_iff B _ g.val).mp g.property x))⟩
  invFun g := ⟨⟨LinearMap.GeneralLinearGroup.toLinearEquiv g.val,
    (mem_isometryGroup_iff B _).mpr g.property.1⟩, fun x =>
      congrArg (fun u : LinearMap.GeneralLinearGroup K V => (u : Module.End K V) x)
        (Subgroup.mem_centralizer_singleton_iff.mp g.property.2)⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).apply_symm_apply g.val.val
  right_inv g := by
    apply Subtype.ext
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm_apply_apply g.val
  map_mul' g h := by
    apply Subtype.ext
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.map_mul g.val.val h.val.val

theorem centralizerSimilitudeEquiv_apply (B : BilinForm K V)
    (A : LinearMap.GeneralLinearGroup K V) (g : symplecticOperatorCentralizer B A) (x : V) :
    ((centralizerSimilitudeEquiv B A g).val : Module.End K V) x = g.val.val x := rfl

theorem two_le_finrank_of_ne_bot [FiniteDimensional K V] {U : Submodule K V} (hU : U ≠ ⊥)
    (B : BilinForm K U) (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    2 ≤ Module.finrank K U := by
  have hpos : 1 ≤ Module.finrank K U := Submodule.one_le_finrank_iff.mpr hU
  obtain ⟨m, hm⟩ := even_finrank B hB hnd
  omega

variable [Finite K]

theorem generalLinearGroup_pComponent_quasisimple [FiniteDimensional K W]
    (hn : 1 ≤ Module.finrank K W) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (LinearMap.GeneralLinearGroup K W)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L :=
  pComponent_quasisimple_of_equiv p (LinearMap.GeneralLinearGroup.generalLinearEquiv K W)
    (CatalogueBOrthogonalLinearFixed.original_generalLinear_pComponent_quasisimple hn p) L hL

theorem sesqUnitary_pComponent_quasisimple [FiniteDimensional K W]
    (hodd : Odd (Nat.card K)) (B : BilinForm K W) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hdim : 2 ≤ Module.finrank K W) (p : ℕ) (L : Subgroup (sesqUnitaryGroup B))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L :=
  pComponent_quasisimple_of_equiv p (sesqUnitaryIsometryEquiv B)
    (isometry_pComponent_quasisimple B hB hnd hdim hodd p) L hL

end General

section ScalarSquare

variable {K : Type} [Field K] [Finite K] {V : Type w} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem split_positive_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (B : BilinForm K V) (A : LinearMap.GeneralLinearGroup K V) (l : K)
    (hP : eigenPlus l (A : Module.End K V) ≠ ⊥) (hM : eigenMinus l (A : Module.End K V) ≠ ⊥)
    (haltP : (B.domRestrict₁₂ (eigenPlus l (A : Module.End K V))
      (eigenPlus l (A : Module.End K V))).IsAlt)
    (haltM : (B.domRestrict₁₂ (eigenMinus l (A : Module.End K V))
      (eigenMinus l (A : Module.End K V))).IsAlt)
    (hndP : (B.domRestrict₁₂ (eigenPlus l (A : Module.End K V))
      (eigenPlus l (A : Module.End K V))).Nondegenerate)
    (hndM : (B.domRestrict₁₂ (eigenMinus l (A : Module.End K V))
      (eigenMinus l (A : Module.End K V))).Nondegenerate)
    (e : similitudeCentralizer B A ≃*
      sesqUnitaryGroup (B.domRestrict₁₂ (eigenPlus l (A : Module.End K V))
        (eigenPlus l (A : Module.End K V))) ×
      sesqUnitaryGroup (B.domRestrict₁₂ (eigenMinus l (A : Module.End K V))
        (eigenMinus l (A : Module.End K V))))
    (p : ℕ) [Fact p.Prime] (L : Subgroup (symplecticOperatorCentralizer B A))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have hdimP := two_le_finrank_of_ne_bot hP _ haltP hndP
  have hdimM := two_le_finrank_of_ne_bot hM _ haltM hndM
  exact pComponent_quasisimple_of_equiv p
    (((centralizerSimilitudeEquiv B A).trans e).trans
      (MulEquiv.prodCongr (sesqUnitaryIsometryEquiv _) (sesqUnitaryIsometryEquiv _)))
    (CatalogueBProjectiveInvolutionProduct.pComponent_quasisimple_product p
      (isometry_pComponent_quasisimple _ haltP hndP hdimP hodd p)
      (isometry_pComponent_quasisimple _ haltM hndM hdimM hodd p)) L hL

theorem split_negative_pComponent_quasisimple
    (B : BilinForm K V) (A : LinearMap.GeneralLinearGroup K V) (l : K)
    (hP : eigenPlus l (A : Module.End K V) ≠ ⊥)
    (e : similitudeCentralizer B A ≃*
      LinearMap.GeneralLinearGroup K (eigenPlus l (A : Module.End K V)))
    (p : ℕ) [Fact p.Prime] (L : Subgroup (symplecticOperatorCentralizer B A))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L :=
  pComponent_quasisimple_of_equiv p ((centralizerSimilitudeEquiv B A).trans e)
    (generalLinearGroup_pComponent_quasisimple (Submodule.one_le_finrank_iff.mpr hP) p) L hL

omit [Finite K] [FiniteDimensional K V] in
theorem centralizer_mem_similitudeCentralizer (B : BilinForm K V)
    (A : LinearMap.GeneralLinearGroup K V) (g : symplecticOperatorCentralizer B A) :
    LinearMap.GeneralLinearGroup.ofLinearEquiv g.val.val ∈ similitudeCentralizer B A :=
  (centralizerSimilitudeEquiv B A g).property

omit [Finite K] [FiniteDimensional K V] in
@[expose] def evaluationIsometryEquiv (B : BilinForm K V)
    (A : LinearMap.GeneralLinearGroup K V)
    (H : Subgroup (V ≃ₗ[scalarSquareField (A : Module.End K V)] V)) (P : (V → V) → Prop)
    (hH : ∀ f, f ∈ H ↔ P ⇑f)
    (hiff : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ similitudeCentralizer B A ↔
      g ∈ Subgroup.centralizer {A} ∧ P ⇑(g : Module.End K V)) :
    symplecticOperatorCentralizer B A ≃* H where
  toFun g := ⟨centralizerEvaluationEquiv (A : Module.End K V) ⟨g.val.val, g.property⟩,
    (hH _).mpr ((hiff _).mp (centralizer_mem_similitudeCentralizer B A g)).2⟩
  invFun f := ⟨⟨(evaluationToCentralizer (A : Module.End K V) f.val).val,
    (mem_isometryGroup_iff B _).mpr ((hiff (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (evaluationToCentralizer (A : Module.End K V) f.val).val)).mpr
        ⟨Subgroup.mem_centralizer_singleton_iff.mpr (Units.ext (LinearMap.ext fun x =>
          (evaluationToCentralizer (A : Module.End K V) f.val).property x)),
          (hH f.val).mp f.property⟩).1⟩,
    (evaluationToCentralizer (A : Module.End K V) f.val).property⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    rfl
  right_inv f := by
    apply Subtype.ext
    ext x
    rfl
  map_mul' g h := by
    apply Subtype.ext
    ext x
    rfl

omit [FiniteDimensional K V] in
theorem finite_of_odd_card {X : Type*} (hX : Odd (Nat.card X)) : Finite X :=
  Nat.finite_of_card_ne_zero (fun h => by rw [h] at hX; exact Nat.not_odd_zero hX)

omit [Finite K] in
theorem nonsquare_positive_pComponent_quasisimple
    (B : BilinForm K V) (A : LinearMap.GeneralLinearGroup K V)
    (hF : IsField (scalarSquareField (A : Module.End K V)))
    (hEodd : Odd (Nat.card (scalarSquareField (A : Module.End K V))))
    (hdim : 2 ≤ Module.finrank (scalarSquareField (A : Module.End K V)) V)
    (BE : BilinForm (scalarSquareField (A : Module.End K V)) V)
    (hBEalt : BE.IsAlt) (hBEnd : BE.Nondegenerate)
    (hiff : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ similitudeCentralizer B A ↔
      g ∈ Subgroup.centralizer {A} ∧
        ∀ v w, BE ((g : Module.End K V) v) ((g : Module.End K V) w) = BE v w)
    (p : ℕ) [Fact p.Prime] (L : Subgroup (symplecticOperatorCentralizer B A))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let : Field (scalarSquareField (A : Module.End K V)) := hF.toField
  have := finite_of_odd_card hEodd
  have : Module.Finite (scalarSquareField (A : Module.End K V)) V :=
    evaluationModule_finite (A : Module.End K V)
  exact pComponent_quasisimple_of_equiv p
    (evaluationIsometryEquiv B A (isometryGroup BE) (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w)
      (mem_isometryGroup_iff BE) hiff)
    (isometry_pComponent_quasisimple BE hBEalt hBEnd hdim hEodd p) L hL

theorem nonsquare_negative_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (B : BilinForm K V) (A : LinearMap.GeneralLinearGroup K V)
    (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1)
    (hF : IsField (scalarSquareField (A : Module.End K V)))
    (hEodd : Odd (Nat.card (scalarSquareField (A : Module.End K V))))
    (hdim : 1 ≤ Module.finrank (scalarSquareField (A : Module.End K V)) V)
    (bar : scalarSquareField (A : Module.End K V) →+* scalarSquareField (A : Module.End K V))
    (hbar : ∀ (x : scalarSquareField (A : Module.End K V)) (a b : K),
      (x : Module.End K V) = a • 1 + b • A → (bar x : Module.End K V) = a • 1 - b • A)
    (hbarbar : ∀ x, bar (bar x) = x)
    (h : V →ₛₗ[bar] V →ₗ[scalarSquareField (A : Module.End K V)]
      scalarSquareField (A : Module.End K V))
    (hsymm : h.IsSymm) (hsep : h.SeparatingLeft)
    (hiff : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ similitudeCentralizer B A ↔
      g ∈ Subgroup.centralizer {A} ∧
        ∀ v w, h ((g : Module.End K V) v) ((g : Module.End K V) w) = h v w)
    (p : ℕ) [Fact p.Prime] (L : Subgroup (symplecticOperatorCentralizer B A))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let : Field (scalarSquareField (A : Module.End K V)) := hF.toField
  have := finite_of_odd_card hEodd
  have : Module.Finite (scalarSquareField (A : Module.End K V)) V :=
    evaluationModule_finite (A : Module.End K V)
  let sigma := RingEquiv.ofBijective bar (Function.Involutive.bijective hbarbar)
  let h' : V →ₛₗ[sigma.toRingHom] V →ₗ[scalarSquareField (A : Module.End K V)]
    scalarSquareField (A : Module.End K V) := h
  have hnd : h'.Nondegenerate :=
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
    have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
    have hA : (2 : K) • (A : Module.End K V) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hx]
      exact add_neg_cancel _
    apply hAns 0
    rw [zero_smul]
    calc (A : Module.End K V) = (2 : K)⁻¹ • ((2 : K) • (A : Module.End K V)) := by
          rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
      _ = 0 := by rw [hA, smul_zero]
  have hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield
      (scalarSquareField (A : Module.End K V)) sigma) ≠ 2 := by
    intro heq
    have hfodd := CatalogueBOrthogonalFieldFixed.subfield_card_odd hEodd
      (CatalogueBLinearTwoDescent.fixedSubfield (scalarSquareField (A : Module.End K V)) sigma)
    rw [heq] at hfodd
    exact Nat.not_even_iff_odd.mpr hfodd even_two
  exact pComponent_quasisimple_of_equiv p
    (evaluationIsometryEquiv B A (CatalogueBUnitaryIsometry.isometryGroup h')
      (fun φ => ∀ v w, h (φ v) (φ w) = h v w)
      (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff)
    (fun M hM => CatalogueBUnitaryIsometry.isometry_all_dimensions_pComponent_quasisimple h'
      hsymm hnd hsigma hne hdim hq2 p Fact.out M hM) L hL

theorem scalar_square_centralizer_pComponent_quasisimple {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {r : ℕ} (hr : 1 ≤ r)
    (hdim : Module.finrank K V = 2 * r) (B : BilinForm K V) (hB : B.IsAlt)
    (hBnd : B.Nondegenerate) (A : LinearMap.GeneralLinearGroup K V)
    (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1) {d : K} (hd0 : d ≠ 0)
    (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w)
    (p : ℕ) [Fact p.Prime] (L : Subgroup (symplecticOperatorCentralizer B A))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact hℓodd.pow
  obtain ⟨hε, hsplit, hnonsplit⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2
    hf hK hr hdim hB hBnd hAns hd0 hAA hAμ
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    obtain ⟨hP, hM, hpos, hneg⟩ := hsplit l hl
    rcases hε with h1 | h1
    · obtain ⟨-, haltP, haltM, hndP, hndM, e, -⟩ := hpos h1
      exact split_positive_pComponent_quasisimple hodd B A l hP hM haltP haltM hndP hndM e
        p L hL
    · obtain ⟨-, -, -, -, -, -, e, -⟩ := hneg h1
      exact split_negative_pComponent_quasisimple B A l hP e p L hL
  · push Not at hsq
    obtain ⟨-, hF, hcard, hfinrank, bar, hbar, -, hbarbar, hpos, hneg⟩ := hnonsplit hsq
    have hEodd : Odd (Nat.card (scalarSquareField (A : Module.End K V))) := by
      rw [hcard]
      exact hℓodd.pow.pow
    rcases hε with h1 | h1
    · obtain ⟨BE, -, hBEalt, hBEnd, ⟨m, hm⟩, hiff⟩ := hpos h1
      exact nonsquare_positive_pComponent_quasisimple B A hF hEodd (by omega) BE hBEalt hBEnd
        hiff p L hL
    · obtain ⟨h, -, hsymm, hsep, hiff⟩ := hneg h1
      exact nonsquare_negative_pComponent_quasisimple hodd B A hAns hF hEodd (by omega) bar
        hbar hbarbar h hsymm hsep hiff p L hL

end ScalarSquare

end CFSG.ComponentClassification.CatalogueBSymplecticB
