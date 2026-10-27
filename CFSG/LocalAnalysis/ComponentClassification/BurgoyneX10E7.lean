module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Descent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10E7Split
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10E6Graph

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open scoped MatrixGroups

theorem excCompModel_of_E6_involution
    {J : Type} [Group J] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E6 n p f) (hm : Blueprint.LieModel J .E6 n p f)
    {α : MulAut J} (hα : orderOf α = 2) {Kc : Subgroup (fixedSubgroup α)} (hKc : IsComponent Kc) :
    ExcCompModel p Kc := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := LieType.Chevalley.nonempty_mulEquiv_adjointGroup .E6
    ((GH74.chevalleyExceptionalModel_of_lieModel (t := .E6) (by decide) hm).2 :
      UntwistedChevalleyModel J .E6 (p ^ f))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact excCompModel_E6_explicit excInnerModel_E6 e6GraphModel_holds hp hp2 hadm.2.1 hF _ hβ
    (fixedSubgroupCongrEquiv e α) hKc

@[expose] def E7TwistedP (P : CompPred) :
    Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (D : OrthogonalSemilinearFixedRootDatum .E7 p k) (m : ℕ), (m = 2 ∨ m = 3) →
    D.χ = signMaskChar .E7 m →
    (∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ)) →
    ∀ J' : Set.range D.classOrbit, IsQuasisimple (D.withOrbit J').orbitGroup →
      P.P p (D.withOrbit J').orbitGroup

section Datum

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem CompPred.e7_twisted_orbitGroup
    (P : CompPred) (D : OrthogonalSemilinearFixedRootDatum .E7 p k) {m : ℕ} (hm : m = 2 ∨ m = 3)
    (hχ : D.χ = signMaskChar .E7 m)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup)
    {S : Set (Fin (Tag.rank .E7) → ℤ)} (hS : simpleUnion (signMaskChar .E7 m) = S)
    (hcls : ∀ {χ : Multiplicative (Fin (Tag.rank .E7) → ℤ) →* ℤˣ}, χ = signMaskChar .E7 m →
      ∀ i : KernelComponent χ, simpleUnion χ ∩ componentRoots χ i = ∅ ∨
        simpleUnion χ ∩ componentRoots χ i = S)
    (hα₃ : Pi.single (e7Node 2) 1 ∈ S)
    (hfam : ∀ (K₂ : Type) [Field K₂] [Finite K₂], Nat.card K₂ = p ^ (D.e * 2) →
      ∀ α : MulAut (↥(pairSpan .E7 K₂ S) ⧸ Subgroup.center ↥(pairSpan .E7 K₂ S)),
        orderOf α = 2 → ∀ L : Subgroup (fixedSubgroup α), IsComponent L → P.P p L) :
    P.P p (D.withOrbit J').orbitGroup := by
  have hΔ : simpleUnion (D.withOrbit J').χ = S := by
    change simpleUnion D.χ = S
    rw [hχ]
    exact hS
  rcases simpleRootsJ_eq_empty_or_eq (D.withOrbit J') hΔ (hcls hχ) with h0 | hJS
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
  have hθ2 : ∀ β ∈ (D.withOrbit J').simpleRootsJ,
      (D.withOrbit J').θ ((D.withOrbit J').θ (toReal β)) = toReal β := by
    intro β hβ
    rw [hJS, ← hS] at hβ
    change D.θ (D.θ (toReal β)) = toReal β
    rw [hθ β, hθ, thetaMap_e7Word2_1_twice hm hβ]
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  have hθp : ThetaProperties 1 2 (D.withOrbit J').χ (ToralSign.wordElt .E7 e7Word2_1) := by
    change ThetaProperties 1 2 D.χ _
    rw [hχ]
    rcases hm with rfl | rfl
    · exact h7.theta ⟨2, 36, 2, e7OmegaWords2⟩ (by simp [e7SignDiagramReps]) e7Word2_1
        (by simp [e7OmegaWords2])
    · exact h7.theta ⟨3, 28, 2, e7OmegaWords3⟩ (by simp [e7SignDiagramReps]) e7Word3_1
        (by simp [e7OmegaWords3])
  have hcard : ∀ O ∈ (D.withOrbit J').orbits, orbitCard O = 1 ∨ orbitCard O = 2 := fun O hO =>
    ClassicalInvolution.ModelFacts.orbitCard_eq_of_thetaProperties (D.withOrbit J') hθp hθ hO
  have hα₃J : Pi.single (e7Node 2) 1 ∈ (D.withOrbit J').simpleRootsJ := hJS ▸ hα₃
  have hr3 : IsRoot .E7 (Pi.single (e7Node 2) 1) := isRoot_single _ _
  have hr7 : IsRoot .E7 (Pi.single (e7Node 6) 1) := isRoot_single _ _
  set y : adjointGroup .E7 k :=
    ⟨rootSL2 .E7 k (Pi.single (e7Node 2) 1) (uSL 1), rootSL2_mem_adjointGroup hr3 _⟩ with hy
  set x : adjointGroup .E7 k :=
    ⟨rootSL2 .E7 k (Pi.single (e7Node 2) 1) (vSL 1), rootSL2_mem_adjointGroup hr3 _⟩ with hx
  have hFy : ((D.withOrbit J').F y : ModGL .E7 k) =
      rootSL2 .E7 k (Pi.single (e7Node 6) 1) (uSL 1) := by
    have h := (D.withOrbit J').map_rootSL2 _ hα₃J.1 (Pi.single (e7Node 6) 1)
      (by change D.θ _ = _; rw [hθ, thetaMap_e7Word2_1_alpha3]) (uSL 1) y rfl
    rw [h, LieType.Chevalley.map_uSL, map_one]
  have hnc : ∃ y ∈ quadGens (D.withOrbit J'), ∃ x ∈ quadGens (D.withOrbit J'),
      ¬ Commute ((D.withOrbit J').F y * y⁻¹) x := by
    refine ⟨y, ⟨_, hα₃J, 1, one_mem _, Or.inl rfl⟩, x, ⟨_, hα₃J, 1, one_mem _, Or.inr rfl⟩,
      fun hc => ?_⟩
    have hc' := hc.map (adjointGroup .E7 k).subtype
    simp only [map_mul, map_inv, Subgroup.coe_subtype] at hc'
    rw [hFy] at hc'
    have ha : Commute (rootSL2 .E7 k (Pi.single (e7Node 6) 1) (uSL 1)) (x : ModGL .E7 k) := by
      have hmem7 : rootSL2 .E7 k (Pi.single (e7Node 6) 1) (uSL 1) ∈
          rootSubgroup .E7 k (Pi.single (e7Node 6) 1) := by
        rw [rootSL2_uSL_eq]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      obtain ⟨ε, -, hε⟩ := exists_rootSL2_vSL_eq (K := k) hr3
      have hmem3 : (x : ModGL .E7 k) ∈ rootSubgroup .E7 k (-Pi.single (e7Node 2) 1) := by
        change rootSL2 .E7 k _ (vSL 1) ∈ _
        rw [hε]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      exact (simply_laced_orthogonal_root_commutation .E7 (Or.inr (Or.inr (Or.inl rfl)))).2 k
        _ _ hr7 (IsRoot.neg hr3) (by decide) _ hmem7 _ hmem3
    have hb : Commute (y : ModGL .E7 k) (x : ModGL .E7 k) := by
      have h1 := ha.inv_left.mul_left hc'
      rw [← mul_assoc, inv_mul_cancel, one_mul] at h1
      simpa using h1.inv_left
    have hAB : rootSL2 .E7 k (Pi.single (e7Node 2) 1) (uSL 1 * vSL 1) =
        rootSL2 .E7 k (Pi.single (e7Node 2) 1) (vSL 1 * uSL 1) := by
      rw [map_mul, map_mul]
      exact hb.eq
    have h2 : ((uSL (1 : k) * vSL 1 : SL2 k) : Matrix (Fin 2) (Fin 2) k) 0 0 =
        ((vSL (1 : k) * uSL 1 : SL2 k) : Matrix (Fin 2) (Fin 2) k) 0 0 :=
      congrArg (fun A : SL2 k => (A : Matrix (Fin 2) (Fin 2) k) 0 0)
        (rootSL2_injective_of_field (Pi.single (e7Node 2) 1) hAB)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
    simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at h2
  have hK₂ : Nat.card (frobeniusFixedField k p (D.e * 2)) = p ^ (D.e * 2) :=
    card_frobeniusFixedField (by have := D.one_le_e; omega)
  have : Finite (frobeniusFixedField k p (D.e * 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hK₂]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let eY : quadGroup (D.withOrbit J') ≃* pairSpan .E7 (frobeniusFixedField k p (D.e * 2)) S :=
    (((quadGroup (D.withOrbit J')).equivMapOfInjective _
      (adjointGroup .E7 k).subtype_injective).trans
        (MulEquiv.subgroupCongr (map_subtype_quadGroup (D.withOrbit J')))).trans
      (((pairSpan .E7 _ _).equivMapOfInjective _ (baseChangeGL_injective _)).symm.trans
        (MulEquiv.subgroupCongr (congrArg (pairSpan .E7 _) hJS)))
  exact P.orbitGroup_of_quadGroup (D.withOrbit J') hθ2 hcard hnc hq
    (P.family_of_mulEquiv (QuotientGroup.congr _ _ eY (Subgroup.map_center_eq eY))
      (hfam _ hK₂))

theorem CompPred.e7_twisted_A7_orbitGroup
    (P : CompPred)
    (hpsl : ∀ (J : Type) [Group J] (f : ℕ), StatedLieAdmissible .PSL 8 p f → LieModel J .PSL 8 p f →
      ∀ α : MulAut J, orderOf α = 2 → ∀ L : Subgroup (fixedSubgroup α), IsComponent L → P.P p L)
    (D : OrthogonalSemilinearFixedRootDatum .E7 p k) (hχ : D.χ = signMaskChar .E7 2)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    P.P p (D.withOrbit J').orbitGroup := by
  have hp : p.Prime := Fact.out
  have hadm : StatedLieAdmissible .PSL 8 p (D.e * 2) :=
    ⟨hp, by have := D.one_le_e; omega, by norm_num, by simp, by simp⟩
  exact P.e7_twisted_orbitGroup D (Or.inl rfl) hχ hθ J' hq simpleUnion_e7_two
    (fun hχ' i => e7_simple_inter_two hχ' i) ⟨5, by decide⟩
    fun K₂ _ _ hK₂ _ hα _ hL => hpsl _ _ hadm (lieModel_pairSpan_A7 hp D.odd hK₂) _ hα _ hL

theorem CompPred.e7_twisted_E6_orbitGroup
    (P : CompPred) (D : OrthogonalSemilinearFixedRootDatum .E7 p k) (hχ : D.χ = signMaskChar .E7 3)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    P.P p (D.withOrbit J').orbitGroup := by
  have hp : p.Prime := Fact.out
  have hadm : StatedLieAdmissible .E6 0 p (D.e * 2) := ⟨hp, by have := D.one_le_e; omega, rfl⟩
  exact P.e7_twisted_orbitGroup D (Or.inr rfl) hχ hθ J' hq
    simpleUnion_e7_three (fun hχ' i => e7_simple_inter_three hχ' i) ⟨0, by decide⟩
    fun K₂ _ _ hK₂ _ hα _ hL => P.of_model D.odd (excCompModel_of_E6_involution hp D.odd hadm
      (lieModel_pairSpan_E6 hp D.odd hK₂) hα hL)
end Datum

@[expose] def E7TwistedA7P (P : CompPred)
    : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (D : OrthogonalSemilinearFixedRootDatum .E7 p k), D.χ = signMaskChar .E7 2 →
    (∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ)) →
    ∀ J' : Set.range D.classOrbit, IsQuasisimple (D.withOrbit J').orbitGroup →
      P.P p (D.withOrbit J').orbitGroup

theorem CompPred.e7TwistedA7_of_psl8 (P : CompPred)
    (hpsl : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (J : Type) [Group J] (f : ℕ),
      StatedLieAdmissible .PSL 8 p f → LieModel J .PSL 8 p f →
      ∀ α : MulAut J, orderOf α = 2 → ∀ L : Subgroup (fixedSubgroup α), IsComponent L → P.P p L) :
    E7TwistedA7P P := by
  intro p _ k _ _ _ D hχ hθ J' hq
  exact P.e7_twisted_A7_orbitGroup (hpsl p Fact.out D.odd) D hχ hθ J' hq

theorem CompPred.e7Twisted_of_A7 (P : CompPred)
    (hA7 : E7TwistedA7P P) : E7TwistedP P := by
  intro p _ k _ _ _ D m hm hχ hθ J' hq
  rcases hm with rfl | rfl
  · exact hA7 p k D hχ hθ J' hq
  · exact P.e7_twisted_E6_orbitGroup D hχ hθ J' hq

variable {K : Type} [Field K] [Finite K]

theorem CompPred.innerP_E7_of_twisted
    (P : CompPred) (htw : E7TwistedP P) : InnerP P .E7 := by
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
  refine P.of_mulEquiv e ?_
  have hsplit : ∀ {m : ℕ}, (m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) → Dd.χ = signMaskChar .E7 m →
      l = [] → P.P p (Dd.withOrbit J').orbitGroup := by
    intro m hm hχ hl0
    subst hl0
    exact P.of_model hp2 (e7_split_orbitGroup_excCompModel Dd hm hχ
      (fun γ => by rw [hDθ γ, thetaMap_nil_one]) J' hq)
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
      exact htw p _ Dd 2 (Or.inl rfl) hDχ hDθ J' hq
  · simp only [e7OmegaWords3, List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with hl | hl
    · exact hsplit (Or.inr (Or.inr (Or.inr rfl))) hDχ hl
    · subst hl
      exact htw p _ Dd 3 (Or.inr rfl) hDχ hDθ J' hq

theorem CompPred.E7_explicit
    (P : CompPred) (hinner : InnerP P .E7) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (β : MulAut (adjointGroup .E7 K)) (hβ : orderOf β = 2)
    {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup β) {L : Subgroup X} (hL : IsComponent L) :
    P.P p L := by
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
    refine P.of_component_equiv Ψ
      (hinner K p f hp hp2 hK β g a (fun h => ?_) hβ) hL
    rw [hgaσ h, hQ, h1, mul_one, inv_one, mul_one]
  · obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hK σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hK]
    exact P.of_model hp2 (excCompModel_odd_field (t := .E7)
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) hp hp2 he hKe σ hσc (g := g) (a := a)
      (fun h => by rw [hgaσ h, hQ, mul_one, inv_one, mul_one]) hβ2 Ψ hL)

theorem CompPred.familyP_of_explicit (P : CompPred)
    {t : StatedLieTag} {τ : Tag} (ht : t ∈ chevalleyExceptionalTags)
    (hmodel : ∀ (J : Type) [Group J] (p f : ℕ), ChevalleyExceptionalModel J t p f →
      UntwistedChevalleyModel J τ (p ^ f))
    (hexp : ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
      Nat.card K = p ^ f → ∀ β : MulAut (adjointGroup τ K), orderOf β = 2 →
        ∀ (X : Type) [Group X], (X ≃* fixedSubgroup β) → ∀ L : Subgroup X, IsComponent L →
          P.P p L) :
    FamilyP P t := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ
    (hmodel J p f (GH74.chevalleyExceptionalModel_of_lieModel ht hm))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact hexp F p f hp hp2 hadm.2.1 hF _ hβ _ (fixedSubgroupCongrEquiv e α) Kc hKc

theorem CompPred.familyP_E7 (P : CompPred)
    (hinner : InnerP P .E7) : FamilyP P .E7 :=
  P.familyP_of_explicit (τ := .E7) (by decide) (fun _ _ _ _ h => h.2)
    fun _ _ _ _ _ hp hp2 hf hK β hβ _ _ Ψ _ hL => P.E7_explicit hinner hp hp2 hf hK β hβ Ψ hL

theorem excFamilyModel_E7_of_A7
    (hA7 : E7TwistedA7P CompPred.model) : ExcFamilyModel .E7 :=
  fun J _ n p f hp hp2 hadm hm α hα Kc hKc => Or.inl (CompPred.model.familyP_E7
    (CompPred.model.innerP_E7_of_twisted (CompPred.model.e7Twisted_of_A7 hA7))
      J n p f hp hp2 hadm hm α hα Kc hKc)

theorem familyNoPSp4Odd_E7
    (hO : LieOrderFormulasInput) (hLin : GSThmB.CF81X10RowLin) :
    FamilyP (CompPred.noPSp4Odd hO) .E7 :=
  (CompPred.noPSp4Odd hO).familyP_E7 ((CompPred.noPSp4Odd hO).innerP_E7_of_twisted
    ((CompPred.noPSp4Odd hO).e7Twisted_of_A7 ((CompPred.noPSp4Odd hO).e7TwistedA7_of_psl8
      fun _ hp hp2 _ _ _ hadm hm _ hα _ hL =>
        noPSp4Odd_of_rowLin hO hLin (Or.inl rfl) (by norm_num) (by norm_num) hp hp2 hadm hm hα
          hL)))

end CFSG.ComponentClassification.Burgoyne.X10
