module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerModels
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthLift
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_iff_isComponent_subgroupOf
  isComponentOf_map_of_injective)

namespace OddInner

theorem card_extension {K : Type} [Field K] [Finite K] (lambda : K)
    [Fact (¬ IsSquare lambda)] :
    Nat.card (CatalogueBProjectiveQuadratic.extension lambda) = Nat.card K ^ 2 := by
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Finite (CatalogueBProjectiveQuadratic.extension lambda) := Module.finite_of_finite K
  let _ : Fintype (CatalogueBProjectiveQuadratic.extension lambda) := Fintype.ofFinite _
  have h := Module.card_eq_pow_finrank (K := K)
    (V := CatalogueBProjectiveQuadratic.extension lambda)
  rw [CatalogueBProjectiveQuadratic.extension_finrank lambda, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at h
  exact h

theorem oddLie_glCentralizer {n : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 2 ≤ n)
    (A : GL (Fin n) K) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1) (lambda : Kˣ)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin n) lambda)
    {L : Subgroup (Subgroup.centralizer ({A} : Set (GL (Fin n) K)))} (hL : IsComponent L) :
    OddLieCentralQuotient p L := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  by_cases hsquare : IsSquare lambda.val
  · obtain ⟨b, -, hr, hs, -, e, -⟩ :=
      CatalogueBProjectiveInvolution.square_projective_centralizer_structure n hn A lambda h2
        hne hsq hsquare
    exact oddLieCentralQuotient_of_component_equiv e
      (fun M hM => oddLie_prod (fun M₁ hM₁ => oddLie_GL hp hf hK hr hM₁)
        (fun M₂ hM₂ => oddLie_GL hp hf hK hs hM₂) hM) hL
  · let : Fact (¬ IsSquare lambda.val) := ⟨hsquare⟩
    let : Finite (CatalogueBProjectiveQuadratic.extension lambda.val) :=
      CatalogueBProjectiveInvolution.quadraticExtension_finite lambda.val
    have hm := (CatalogueBProjectiveQuadratic.nonsquare_matrix_dimension n hn A lambda hsq
      hsquare).2
    exact oddLieCentralQuotient_of_component_equiv
      (CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A lambda hsq)
      (fun M hM => oddLie_GL hp (j := 2 * f) (by omega)
        (by rw [card_extension, hK, ← pow_mul, mul_comm]) hm hM) hL

end OddInner

theorem oddLie_inner_psl {n : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hadm : StatedLieAdmissible .PSL n p f)
    (A : GL (Fin n) K) (hA : orderOf (innerDiagonalAction n K A) = 2)
    {L : Subgroup (fixedSubgroup (innerDiagonalAction n K A))} (hL : IsComponent L) :
    OddLieCentralQuotient p L := by
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K := by
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · right
      have hn2 : n = 2 := by omega
      have h3' : p ^ f ≠ 3 := fun h => hadm.2.2.2.2 (by rw [hn2, h])
      rw [hK]
      exact OddInner.five_le_pow hp hp2 hf h3'
    · exact Or.inl h3
  have hne : innerDiagonalAction n K A ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hsq2 : innerDiagonalAction n K A ^ 2 = 1 := by
    rw [← hA, pow_orderOf_eq_one]
  obtain ⟨hmk, -, c, hc⟩ :=
    CatalogueBHigherLinearInner.inner_involution_projective_data n K hn hparameter A hne hsq2
  set Z := center (SpecialLinearGroup (Fin n) K)
  set ψ := slConjugation n K A
  have hinv : Z.map ψ.toMonoidHom = Z := Subgroup.map_center_eq ψ
  have heq : innerDiagonalAction n K A = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : SpecialLinearGroup (Fin n) K ⧸ Z)) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk]
      exact innerDiagonalAction_mk n K A g
  let eF := MulEquiv.subgroupCongr (congrArg fixedSubgroup heq)
  have hL' := LocalCores.isComponent_map_mulEquiv eF hL
  obtain ⟨M, hM, ⟨eLM⟩⟩ := exists_component_of_quotientFixed Z le_rfl ψ hinv hL'
  have hmap : (fixedSubgroup ψ).map SpecialLinearGroup.toGL =
      Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ⊓
        CatalogueBGeneralLinear.specialLinearRange n K := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : SpecialLinearGroup.toGL (ψ g) = SpecialLinearGroup.toGL g :=
        congrArg _ (show ψ g = g from hg)
      rw [toGL_slConjugation] at h1
      calc SpecialLinearGroup.toGL g * A =
          (A * SpecialLinearGroup.toGL g * A⁻¹) * A := by rw [h1]
        _ = A * SpecialLinearGroup.toGL g := by group
    · intro hy
      obtain ⟨hyC, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
      refine ⟨g, ?_, rfl⟩
      change ψ g = g
      apply SpecialLinearGroup.toGL_injective
      rw [toGL_slConjugation, ← Subgroup.mem_centralizer_singleton_iff.mp hyC,
        mul_inv_cancel_right]
  have hMF : Assembly.IsComponentOf (M.map (fixedSubgroup ψ).subtype) (fixedSubgroup ψ) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le M)).2 ?_
    have hMM : (M.map (fixedSubgroup ψ).subtype).subgroupOf (fixedSubgroup ψ) = M :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) M
    rw [hMM]
    exact hM
  have h1 := isComponentOf_map_of_injective hMF SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective
  rw [hmap] at h1
  have hnormal : ((Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ⊓
      CatalogueBGeneralLinear.specialLinearRange n K).subgroupOf
        (Subgroup.centralizer ({A} : Set (GL (Fin n) K)))).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨-, hxS⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(g * x * g⁻¹).2, ?_⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (CatalogueBGeneralLinear.specialLinearRangeNormal n K).conj_mem _ hxS (g : GL (Fin n) K)
  have h2 := OddClassSelector.isComponentOf_of_normal_le h1 inf_le_left hnormal
  have h3 := (isComponentOf_iff_isComponent_subgroupOf h2.1).1 h2
  have hO := OddInner.oddLie_glCentralizer hp hp2 hf hK hn A hmk c hc h3
  have hMo : OddLieCentralQuotient p M :=
    oddLieCentralQuotient_of_mulEquiv
      ((M.equivMapOfInjective (fixedSubgroup ψ).subtype (subtype_injective _)).trans
        ((M.map (fixedSubgroup ψ).subtype).equivMapOfInjective SpecialLinearGroup.toGL
          SpecialLinearGroup.toGL_injective))
      (oddLieCentralQuotient_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h2.1).symm hO)
  exact oddLieCentralQuotient_of_mulEquiv (L.equivMapOfInjective eF.toMonoidHom eF.injective)
    (oddLieCentralQuotient_of_centerQuotient_equiv eLM hMo)

theorem oddPSLInnerDiagInput : OddPSLInnerDiagInput := by
  intro n K _ _ p f hp hp2 hK hadm A hA L hL
  exact oddLie_inner_psl hp hp2 hK hadm A hA hL

theorem gls3OddFamilyInput_PSL_of_graphInput (hgraph : OddPSLGraphInput) :
    GLS3OddFamilyInput .PSL :=
  gls3OddFamilyInput_PSL oddPSLInnerDiagInput hgraph

end CFSG.ComponentClassification.CatLeafProof
