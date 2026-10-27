module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2E7S
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2E7T
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Fam

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open scoped MatrixGroups
open CFSG.ComponentClassification.Burgoyne.X10

theorem excInnerNoPSL2_E7
    (hO : LieOrderFormulasInput) : ExcInnerNoPSL2 .E7 := by
  intro K _ _ p f hp hp2 hK α g a hαg hα L hL
  have hf : 1 ≤ f := (one_le_and_three_le_of_card hp hp2 hK).1
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p K (AlgebraicClosure K)
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    LocalAnalysis.SteinbergBM.exists_mulEquiv_E7_inner_diagonal_fixed hp2 hf hK hαg hα2
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨n7, -, -⟩ :=
    rational_toral_twist_semilinear_pinning_normalization (k := AlgebraicClosure K) p hp2 f hf
  obtain ⟨r7, -, -⟩ :=
    rational_inner_involution_finite_toral_twist_reduction p (AlgebraicClosure K) hp2 f hf
  set R := fixedPointsIn (adjointGroup .E7 (AlgebraicClosure K))
    (frobTwistGL .E7 (AlgebraicClosure K) p f 1) with hR
  set N := ⁅R, R⁆ ⊓ Subgroup.centralizer {x} with hN
  have hRfin : Finite R := finite_fixedPointsIn_frobTwistGL p hf le_rfl (map_one _) (one_pow 1)
  have hNR : N ≤ R := fun y hy => Subgroup.commutator_le_self _ hy.1
  have : Finite N := Finite.of_injective _ (Subgroup.inclusion_injective hNR)
  let eA' : fixedSubgroup α ≃* N := eA
  set S' : Subgroup N := L.map eA'.toMonoidHom with hS'
  have hS'c : IsComponent S' := LocalCores.isComponent_map_mulEquiv eA' hL
  have hMN : S'.map N.subtype ≤ N := Subgroup.map_subtype_le _
  have hsub : (S'.map N.subtype).subgroupOf N = S' :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective S'
  have hS'N : Assembly.IsComponentOf (S'.map N.subtype) N :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hMN).2
      (by rw [hsub]; exact hS'c)
  obtain ⟨Dd, J₀, ⟨mr, hmr, l, hl, hDχ, hDθ⟩, hXfin, hJ₀X, hJ₀c, ⟨eL⟩⟩ :=
    LocalAnalysis.SteinbergCA.exists_datum_isPComponent_of_twistReduction p hp2 hk hf
      (Or.inr (Or.inr rfl)) (ρ := 1) (fun _ _ => rfl) (fun _ _ => rfl) h7.theta
      (fun l _ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ) (one_mem _)
      (map_conj_one_adjointGroup _ _) n7 (r7 x hxR hx2) (S'.map N.subtype) hMN
      (ExcSelector.isPComponent_two_subgroupOf hS'N)
  obtain ⟨J', hJ', hq⟩ := ExcSelector.exists_eq_orbitGroupC_of_isPComponent' Dd hXfin hJ₀X hJ₀c
  let e : L ≃* (Dd.withOrbit J').orbitGroup :=
    ((L.equivMapOfInjective _ eA'.injective).trans
      ((S'.equivMapOfInjective _ N.subtype_injective).trans
        (eL.trans (MulEquiv.subgroupCongr hJ')))).trans
      (Subgroup.subgroupOfEquivOfLe (Dd.withOrbit J').orbitGroup_le_adjointGroup)
  refine NoPSL2Odd.of_mulEquiv e ?_
  have hsplit : ∀ {m : ℕ}, (m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) → Dd.χ = signMaskChar .E7 m →
      l = [] → NoPSL2Odd (Dd.withOrbit J').orbitGroup := by
    intro m hm hχ hl0
    subst hl0
    exact e7_split_orbitGroup_noPSL2Odd hO Dd hm hχ
      (fun γ => by rw [hDθ γ, thetaMap_nil_one]) J' hq
  simp only [e7SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at hmr
  rcases hmr with rfl | rfl | rfl | rfl
  · simp only [e7OmegaWords0, List.mem_cons, List.mem_nil_iff, or_false] at hl
    exact hsplit (Or.inl rfl) hDχ hl
  · simp only [e7OmegaWords1, List.mem_cons, List.mem_nil_iff, or_false] at hl
    exact hsplit (Or.inr (Or.inl rfl)) hDχ hl
  · simp only [e7OmegaWords2, List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with hl | hl
    · exact hsplit (Or.inr (Or.inr (Or.inl rfl))) hDχ hl
    · subst hl
      exact noPSL2Odd_e7TwistedA7 hO Dd hDχ hDθ J' hq
  · simp only [e7OmegaWords3, List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with hl | hl
    · exact hsplit (Or.inr (Or.inr (Or.inr rfl))) hDχ hl
    · subst hl
      exact noPSL2Odd_e7_twisted_E6_orbitGroup hO Dd hDχ hDθ J' hq

theorem famInnerNoPSL2_E7
    (hO : LieOrderFormulasInput) : FamInnerNoPSL2 .E7 :=
  famInnerNoPSL2_of_explicit (τ := .E7) (by decide) (fun _ _ _ _ h => h.2) (excInnerNoPSL2_E7 hO)

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
