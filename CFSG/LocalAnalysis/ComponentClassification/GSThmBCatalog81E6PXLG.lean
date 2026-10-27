module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXC
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthLift
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211X

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBGraphForm (glGraphAut glTranspose slGraphAut
  pureGraphAction)
open CFSG.ComponentClassification.CatalogueBLinearHigherB
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_iff_isComponent_subgroupOf
  isComponentOf_map_of_injective)

variable {Q : ℕ → Prop}

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFive CatLeafProof in
theorem compOrd_orthogonal_five {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (Q₀ : QuadraticForm K W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : Module.finrank K W = 5) (hQ : Q (Open.ordBC 2 (p ^ e))) :
    CompOrd Q (TauCeti.QuadraticMap.orthogonalGroup Q₀) := by
  intro M hM
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_five_derived hodd Q₀ hQ₀ hdim
  have hMeq := eq_commutator_of_isComponent hq hM
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e' (symplecticKernel_quasisimple hodd)
    (selfAdjointSymplecticAction h2) (selfAdjointSymplecticImage_quasisimple hodd)
    (hMeq.trans hcomm)
  have hadm : StatedLieAdmissible .PSp 2 p e := by
    refine ⟨hp, he, le_rfl, fun h => ?_⟩
    have h1 : p ^ e = 2 := (Prod.mk.inj h).2
    rw [← hK] at h1
    exact absurd (h1 ▸ hodd) (by decide)
  let eSp := symplecticKernelEquivFin.trans (LieType.Universal.Symplectic.equivStatedSp 2 K)
  let eTot := E.trans (QuotientGroup.congr _ _ eSp (Subgroup.map_center_eq eSp))
  have hL : Blueprint.LieModel (M ⧸ center M) .PSp 2 p e :=
    LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm (Or.inl ⟨by decide,
      LieType.Universal.Symplectic.statedClassicalModel_center_quotient 2 K hadm hK⟩)
  rw [GH74.card_of_lieModel_PSp (by norm_num) hp2 hL]
  exact hQ

theorem compOrd_graph_psl {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (A : GL (Fin 5) K)
    (hA : orderOf (pureGraphAction 5 K A) = 2) (hQ : Q (Open.ordBC 2 (p ^ f))) :
    CompOrd Q (fixedSubgroup (pureGraphAction 5 K A)) := by
  intro L hL
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
  have hsq2 : pureGraphAction 5 K A ^ 2 = 1 := by
    rw [← hA, pow_orderOf_eq_one]
  have hsymm : (A : Matrix (Fin 5) (Fin 5) K)ᵀ = A := by
    rcases CatalogueBGraphForm.pureGraph_involution_form_data 5 K (by norm_num) hodd A hsq2 with
      h | ⟨-, h⟩
    · exact h
    · exact absurd h (by decide)
  set Z := center (SpecialLinearGroup (Fin 5) K)
  set ψ := slConjugation 5 K A * slGraphAut 5 K
  have hinv : Z.map ψ.toMonoidHom = Z := Subgroup.map_center_eq ψ
  have heq : pureGraphAction 5 K A = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : SpecialLinearGroup (Fin 5) K ⧸ Z)) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk]
      exact CatalogueBGraphForm.pureGraphAction_mk 5 K A g
  let eF := MulEquiv.subgroupCongr (congrArg fixedSubgroup heq)
  have hL' := LocalCores.isComponent_map_mulEquiv eF hL
  obtain ⟨M, hM, ⟨eLM⟩⟩ := CatLeafProof.exists_component_of_quotientFixed Z le_rfl ψ hinv hL'
  have hfix : ∀ x : GL (Fin 5) K, A * glGraphAut 5 K x * A⁻¹ = x ↔
      glTranspose 5 K x * A⁻¹ * x = A⁻¹ := by
    intro x
    have hT : glGraphAut 5 K x = (glTranspose 5 K x)⁻¹ := (inv_inv _).symm
    rw [hT]
    constructor
    · intro h
      calc glTranspose 5 K x * A⁻¹ * x =
          glTranspose 5 K x * A⁻¹ * (A * (glTranspose 5 K x)⁻¹ * A⁻¹) := by rw [h]
        _ = A⁻¹ := by group
    · intro h
      calc A * (glTranspose 5 K x)⁻¹ * A⁻¹ =
          A * (glTranspose 5 K x)⁻¹ * (glTranspose 5 K x * A⁻¹ * x) := by rw [h]
        _ = x := by group
  have hmap : (fixedSubgroup ψ).map SpecialLinearGroup.toGL =
      CatalogueBGraphForm.isometryGroup 5 K A⁻¹ ⊓
        CatalogueBGeneralLinear.specialLinearRange 5 K := by
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
  have hnormal : ((CatalogueBGraphForm.isometryGroup 5 K A⁻¹ ⊓
      CatalogueBGeneralLinear.specialLinearRange 5 K).subgroupOf
        (CatalogueBGraphForm.isometryGroup 5 K A⁻¹)).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨-, hxS⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(g * x * g⁻¹).2, ?_⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (CatalogueBGeneralLinear.specialLinearRangeNormal 5 K).conj_mem _ hxS (g : GL (Fin 5) K)
  have h2 := OddClassSelector.isComponentOf_of_normal_le h1 inf_le_left hnormal
  have h3 := (isComponentOf_iff_isComponent_subgroupOf h2.1).1 h2
  have hR := transpose_inv_of_transpose_eq A hsymm
  have hO : CompOrd Q (CatalogueBGraphForm.isometryGroup 5 K A⁻¹) :=
    CompOrd.of_mulEquiv (isometryGroupEquiv A⁻¹).symm
      (CompOrd.of_mulEquiv
        (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd A⁻¹ hR).symm)
        (compOrd_orthogonal_five hp hp2 hf hK _
          (polarBilin_matrixQuadraticForm_nondegenerate hodd A⁻¹ hR)
          (by rw [Module.finrank_fin_fun]) hQ))
  rw [card_centerQuotient_congr (L.equivMapOfInjective eF.toMonoidHom eF.injective),
    Nat.card_congr eLM.toEquiv, card_centerQuotient_congr
      ((M.equivMapOfInjective (fixedSubgroup ψ).subtype (subtype_injective _)).trans
        ((M.map (fixedSubgroup ψ).subtype).equivMapOfInjective SpecialLinearGroup.toGL
          SpecialLinearGroup.toGL_injective)),
    ← card_centerQuotient_congr (Subgroup.subgroupOfEquivOfLe h2.1)]
  exact hO _ h3

end P211X

end CFSG.ComponentClassification.GSThmB
