module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthHigh
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBPureGraph
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthLift
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Lin

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBGraphForm (glGraphAut glTranspose slGraphAut
  pureGraphAction)
open CFSG.ComponentClassification.CatalogueBLinearHigherB
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_iff_isComponent_subgroupOf
  isComponentOf_map_of_injective)
open CFSG.ComponentClassification.CatLeafProof (exists_component_of_quotientFixed)

@[expose] def graphTuples (n e : ℕ) : Set (StatedLieTag × ℕ × ℕ) :=
  {x | x ∈ orthTuples n e ∨ (Even n ∧ x = (.PSp, n / 2, e))}

theorem modelIn_isometryGroup_alt {k W : Type} [Field k] [Finite k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = p ^ e) (B : LinearMap.BilinForm k W) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hW : 3 ≤ Module.finrank k W)
    {L : Subgroup (CatalogueBAlternatingIsometry.isometryGroup B)} (hL : IsComponent L) :
    ModelIn p (graphTuples (Module.finrank k W) e) L := by
  obtain ⟨m, hdm, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B hB hnd
  refine ⟨.PSp, m, e, Or.inr ⟨⟨m, by omega⟩, by rw [show Module.finrank k W / 2 = m by omega]⟩,
    X10Sp.centralModel_isometryGroup_component hp hp2 he hk B hB hnd hdm (by omega) hL⟩

theorem graph_psl_component_models {n : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hA : orderOf (pureGraphAction n K A) = 2)
    {L : Subgroup (fixedSubgroup (pureGraphAction n K A))} (hL : IsComponent L) :
    ModelIn p (graphTuples n f) L := by
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
  obtain ⟨M, hM, ⟨eLM⟩⟩ := exists_component_of_quotientFixed Z le_rfl ψ hinv hL'
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
  have hdim : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hO' : ModelIn p (graphTuples n f) (((M.map (fixedSubgroup ψ).subtype).map
      SpecialLinearGroup.toGL).subgroupOf (CatalogueBGraphForm.isometryGroup n K A⁻¹)) := by
    refine modelIn_of_component_equiv (isometryGroupEquiv A⁻¹).symm (fun N hN => ?_) h3
    rcases hform with hsymm | ⟨halt, -⟩
    · have hR := transpose_inv_of_transpose_eq A hsymm
      refine modelIn_of_component_equiv
        (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd A⁻¹ hR).symm)
        (fun N' hN' => ?_) hN
      have hm := orthogonal_component_models hp hp2 hf hK _
        (polarBilin_matrixQuadraticForm_nondegenerate hodd A⁻¹ hR) (by omega) hN'
      rw [hdim] at hm
      exact hm.mono fun x hx => Or.inl hx
    · have hR := transpose_inv_of_transpose_eq_neg A halt
      have hm := modelIn_isometryGroup_alt hp hp2 hf hK (matrixForm A⁻¹)
        (matrixForm_isAlt hodd A⁻¹ hR) (matrixForm_nondegenerate A⁻¹) (by omega) hN
      rwa [hdim] at hm
  have hMo : ModelIn p (graphTuples n f) M :=
    (hO'.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h2.1).symm).of_mulEquiv
      ((M.equivMapOfInjective (fixedSubgroup ψ).subtype (subtype_injective _)).trans
        ((M.map (fixedSubgroup ψ).subtype).equivMapOfInjective SpecialLinearGroup.toGL
          SpecialLinearGroup.toGL_injective))
  exact (hMo.of_centerQuotient_equiv eLM).of_mulEquiv
    (L.equivMapOfInjective eF.toMonoidHom eF.injective)

end CFSG.ComponentClassification.CatLeafProof.X10Lin
