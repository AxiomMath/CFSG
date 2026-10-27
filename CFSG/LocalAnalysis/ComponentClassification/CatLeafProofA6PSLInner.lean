module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Cent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBPureGraph

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBGraphForm (glGraphAut glTranspose slGraphAut
  pureGraphAction)
open CFSG.ComponentClassification.CatalogueBLinearHigherB
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_iff_isComponent_subgroupOf
  isComponentOf_map_of_injective)

theorem a6_inner_psl
    {n : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hadm : StatedLieAdmissible .PSL n p f)
    (A : GL (Fin n) K) (hA : orderOf (innerDiagonalAction n K A) = 2) :
    A6CentreForm (fixedSubgroup (innerDiagonalAction n K A)) := by
  intro L hL
  show A6Safe L
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
  obtain ⟨M, hM, σ, hσ, hker⟩ := exists_component_cover_of_quotientFixed Z le_rfl ψ hinv hL'
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
  have hO := a6CentreForm_glCentralizer hp hp2 hf hK hn A hmk c hc _ h3
  have hMo : A6Safe M :=
    a6Safe_of_mulEquiv
      ((M.equivMapOfInjective (fixedSubgroup ψ).subtype (subtype_injective _)).trans
        ((M.map (fixedSubgroup ψ).subtype).equivMapOfInjective SpecialLinearGroup.toGL
          SpecialLinearGroup.toGL_injective))
      (a6Safe_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h2.1).symm hO)
  exact a6Safe_of_mulEquiv (L.equivMapOfInjective eF.toMonoidHom eF.injective)
    (a6Safe_of_cover hM.1 σ hσ hker hMo)

theorem a6_graph_psl
    {n : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hA : orderOf (pureGraphAction n K A) = 2) :
    A6CentreForm (fixedSubgroup (pureGraphAction n K A)) := by
  intro L hL
  show A6Safe L
  have hf : 1 ≤ f := by
    by_contra h0
    have : f = 0 := by omega
    have h1 := Finite.one_lt_card (α := K)
    rw [hK, this, pow_zero] at h1
    exact lt_irrefl 1 h1
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hodd : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have hsq2 : pureGraphAction n K A ^ 2 = 1 := by
    rw [← hA, pow_orderOf_eq_one]
  have hform := CatalogueBGraphForm.pureGraph_involution_form_data n K hn hodd A hsq2
  set Z := center (SpecialLinearGroup (Fin n) K)
  set ψ := slConjugation n K A * slGraphAut n K
  have hinv : Z.map ψ.toMonoidHom = Z := Subgroup.map_center_eq ψ
  have heq : pureGraphAction n K A = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : SpecialLinearGroup (Fin n) K ⧸ Z)) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk]
      exact CatalogueBGraphForm.pureGraphAction_mk n K A g
  let eF := MulEquiv.subgroupCongr (congrArg fixedSubgroup heq)
  have hL' := LocalCores.isComponent_map_mulEquiv eF hL
  obtain ⟨M, hM, σ, hσ, hker⟩ := exists_component_cover_of_quotientFixed Z le_rfl ψ hinv hL'
  have hfix : ∀ x : GL (Fin n) K, A * glGraphAut n K x * A⁻¹ = x ↔
      glTranspose n K x * A⁻¹ * x = A⁻¹ := by
    intro x
    have hT : glGraphAut n K x = (glTranspose n K x)⁻¹ := (inv_inv _).symm
    rw [hT]
    constructor
    · intro h
      calc glTranspose n K x * A⁻¹ * x =
          glTranspose n K x * A⁻¹ * (A * (glTranspose n K x)⁻¹ * A⁻¹) := by rw [h]
        _ = A⁻¹ := by group
    · intro h
      calc A * (glTranspose n K x)⁻¹ * A⁻¹ =
          A * (glTranspose n K x)⁻¹ * (glTranspose n K x * A⁻¹ * x) := by rw [h]
        _ = x := by group
  have hmap : (fixedSubgroup ψ).map SpecialLinearGroup.toGL =
      CatalogueBGraphForm.isometryGroup n K A⁻¹ ⊓
        CatalogueBGeneralLinear.specialLinearRange n K := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
      have h1 : SpecialLinearGroup.toGL (ψ g) = SpecialLinearGroup.toGL g :=
        congrArg _ (show ψ g = g from hg)
      rw [MulAut.mul_apply, toGL_slConjugation, CatalogueBGraphForm.toGL_slGraphAut] at h1
      exact (hfix _).mp h1
    · intro hy
      obtain ⟨hyI, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
      refine ⟨g, ?_, rfl⟩
      change ψ g = g
      apply SpecialLinearGroup.toGL_injective
      rw [MulAut.mul_apply, toGL_slConjugation, CatalogueBGraphForm.toGL_slGraphAut]
      exact (hfix _).mpr hyI
  have hMF : Assembly.IsComponentOf (M.map (fixedSubgroup ψ).subtype) (fixedSubgroup ψ) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le M)).2 ?_
    have hMM : (M.map (fixedSubgroup ψ).subtype).subgroupOf (fixedSubgroup ψ) = M :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) M
    rw [hMM]
    exact hM
  have h1 := isComponentOf_map_of_injective hMF SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective
  rw [hmap] at h1
  have hnormal : ((CatalogueBGraphForm.isometryGroup n K A⁻¹ ⊓
      CatalogueBGeneralLinear.specialLinearRange n K).subgroupOf
        (CatalogueBGraphForm.isometryGroup n K A⁻¹)).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨-, hxS⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(g * x * g⁻¹).2, ?_⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (CatalogueBGeneralLinear.specialLinearRangeNormal n K).conj_mem _ hxS (g : GL (Fin n) K)
  have h2 := OddClassSelector.isComponentOf_of_normal_le h1 inf_le_left hnormal
  have h3 := (isComponentOf_iff_isComponent_subgroupOf h2.1).1 h2
  have hO' : A6Safe (((M.map (fixedSubgroup ψ).subtype).map
      SpecialLinearGroup.toGL).subgroupOf (CatalogueBGraphForm.isometryGroup n K A⁻¹)) := by
    refine a6CentreForm_of_mulEquiv (isometryGroupEquiv A⁻¹).symm ?_ _ h3
    have hpos : 0 < Module.finrank K (Fin n → K) := by
      rw [Module.finrank_fin_fun]
      omega
    rcases hform with hsymm | ⟨halt, -⟩
    · have hR := transpose_inv_of_transpose_eq A hsymm
      exact a6CentreForm_of_mulEquiv
        (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd A⁻¹ hR).symm)
        (a6CentreForm_orthogonal hp hp2 hf hK _
          (polarBilin_matrixQuadraticForm_nondegenerate hodd A⁻¹ hR))
    · have hR := transpose_inv_of_transpose_eq_neg A halt
      exact a6CentreForm_isometryGroup hp hp2 hf hK (matrixForm A⁻¹)
        (matrixForm_isAlt hodd A⁻¹ hR) (matrixForm_nondegenerate A⁻¹) hpos
  have hMo : A6Safe M :=
    a6Safe_of_mulEquiv
      ((M.equivMapOfInjective (fixedSubgroup ψ).subtype (subtype_injective _)).trans
        ((M.map (fixedSubgroup ψ).subtype).equivMapOfInjective SpecialLinearGroup.toGL
          SpecialLinearGroup.toGL_injective))
      (a6Safe_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h2.1).symm hO')
  exact a6Safe_of_mulEquiv (L.equivMapOfInjective eF.toMonoidHom eF.injective)
    (a6Safe_of_cover hM.1 σ hσ hker hMo)

end CFSG.ComponentClassification.CatLeafProof
