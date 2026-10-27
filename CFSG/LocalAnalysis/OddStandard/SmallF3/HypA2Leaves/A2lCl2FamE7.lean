module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamE7Twist
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamE7Split
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormUniform

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

@[expose] def Cl24E7Inner : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup .E7 K)) (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ),
      (∀ h : adjointGroup .E7 K, (α h : ModGL .E7 K) = (g : ModGL .E7 K) * rootDiagUnit .E7 a *
        (h : ModGL .E7 K) * (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 K)⁻¹) → orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L →
        Cl24Q p (fun f' => f' = f ∨ f' = 2 * f ∨ f' = 4 * f) L

section


theorem cl24_e7Inner_holds : Cl24E7Inner := by
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
  obtain ⟨Dd, ⟨mr, hmr, l, hl, hDχ, hDθ⟩, hDe, hXfin, hall⟩ :=
    exists_datum_uniform_of_twistReduction p hp2 hk hf
      (Or.inr (Or.inr rfl)) (ρ := 1) (fun _ _ => rfl) (fun _ _ => rfl) h7.theta
      (fun l _ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ) (one_mem _)
      (map_conj_one_adjointGroup _ _) n7 (r7 x hxR hx2) (S'.map N.subtype) hMN
      (ExcSelector.isPComponent_two_subgroupOf hS'N)
  obtain ⟨J₀, hJ₀X, hJ₀c, ⟨eL⟩⟩ := hall (S'.map N.subtype) hMN
    (ExcSelector.isPComponent_two_subgroupOf hS'N)
  obtain ⟨J', hJ', hq⟩ := ExcSelector.exists_eq_orbitGroupC_of_isPComponent' Dd hXfin hJ₀X hJ₀c
  let e : L ≃* (Dd.withOrbit J').orbitGroup :=
    ((L.equivMapOfInjective _ eA'.injective).trans
      ((S'.equivMapOfInjective _ N.subtype_injective).trans
        (eL.trans (MulEquiv.subgroupCongr hJ')))).trans
      (Subgroup.subgroupOfEquivOfLe (Dd.withOrbit J').orbitGroup_le_adjointGroup)
  refine cl24_of_mulEquiv e ?_
  have hsplit : ∀ {m : ℕ}, (m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) → Dd.χ = signMaskChar .E7 m →
      l = [] → Cl24Q p (fun f' => f' = f ∨ f' = 2 * f ∨ f' = 4 * f)
        (Dd.withOrbit J').orbitGroup := by
    intro m hm hχ hl0
    subst hl0
    exact cl24_e7_split_orbitGroup Dd hm hχ
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
      exact cl24_e7_twisted_A7 Dd hDχ hDθ J' hq
  · simp only [e7OmegaWords3, List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with hl | hl
    · exact hsplit (Or.inr (Or.inr (Or.inr rfl))) hDχ hl
    · subst hl
      exact cl24_e7_twisted_E6 Dd hDχ hDθ J' hq

end

section


variable {K : Type} [Field K] [Finite K]

theorem cl24_odd_E7_explicit
    (hinner : Cl24E7Inner) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (β : MulAut (adjointGroup .E7 K)) (hβ : orderOf β = 2)
    {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup β) {L : Subgroup X} (hL : IsComponent L) :
    Cl24Q p (fun f' => f' = f ∨ f' = 2 * f ∨ f' = 4 * f ∨ f = 2 * f') L := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have h1 : ∀ x : ModGL Tag.E7 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ : ∀ ε : Fin (exactE Tag.E7), exactQ Tag.E7 K ε = 1 := fun _ => rfl
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form Tag.E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨-, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF β
  have hσ2 := hsq β g a σ ε hgaσ hβ2
  by_cases hσ1 : σ = 1
  · subst hσ1
    refine (cl24_of_component_equiv Ψ
      (hinner K p f hp hp2 hK β g a (fun h => ?_) hβ) hL).mono fun _ h => by omega
    rw [hgaσ h, hQ, h1, mul_one, inv_one, mul_one]
  · obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hK σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hK]
    have hf2 := cl24_exp_eq_two_mul hp hK hKe
    exact (cl24_odd_field (t := .E7) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      hp hp2 he hKe σ hσc (g := g) (a := a) (fun h => by rw [hgaσ h, hQ, mul_one, inv_one,
        mul_one]) hβ2 Ψ hL).mono fun _ h => by omega

end

section


theorem cl24_family_E7 : Cl24OddFamily .E7 := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7
    ((GH74.chevalleyExceptionalModel_of_lieModel (t := .E7) (by decide) hm).2 :
      UntwistedChevalleyModel J .E7 (p ^ f))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact Or.inl ((cl24_odd_E7_explicit cl24_e7Inner_holds hp hp2 hadm.2.1 hF _ hβ
    (fixedSubgroupCongrEquiv e α) hKc).mono fun _ h => by unfold Cl24FieldRel; omega)

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
