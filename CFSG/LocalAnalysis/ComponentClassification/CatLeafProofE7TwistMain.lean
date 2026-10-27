module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Twist
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddLieFamilies
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQuadDescentMain

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.ComponentClassification.CatLeaf
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem e7_twisted_orbitGroup_oddLieCentralQuotient
    (D : OrthogonalSemilinearFixedRootDatum .E7 p k) {m : ℕ} (hm : m = 2 ∨ m = 3)
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
        orderOf α = 2 → ∀ L : Subgroup (fixedSubgroup α), IsComponent L →
          OddLieCentralQuotient p L) :
    OddLieCentralQuotient p (D.withOrbit J').orbitGroup := by
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
  exact oddLieCentralQuotient_orbitGroup_of_quadGroup (D.withOrbit J') hθ2 hcard hnc hq
    (family_of_mulEquiv (QuotientGroup.congr _ _ eY (Subgroup.map_center_eq eY))
      (hfam _ hK₂))

theorem e7_twisted_A7_orbitGroup_oddLieCentralQuotient
    (D : OrthogonalSemilinearFixedRootDatum .E7 p k) (hχ : D.χ = signMaskChar .E7 2)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    OddLieCentralQuotient p (D.withOrbit J').orbitGroup := by
  have hp : p.Prime := Fact.out
  have hadm : StatedLieAdmissible .PSL 8 p (D.e * 2) :=
    ⟨hp, by have := D.one_le_e; omega, by norm_num, by simp, by simp⟩
  exact e7_twisted_orbitGroup_oddLieCentralQuotient D (Or.inl rfl) hχ hθ J' hq simpleUnion_e7_two
    (fun hχ' i => e7_simple_inter_two hχ' i) ⟨5, by decide⟩
    fun K₂ _ _ hK₂ _ hα _ hL => oddLieCentralQuotient_of_psl_involution hp D.odd hadm
      (lieModel_pairSpan_A7 hp D.odd hK₂) hα hL

theorem e7_twisted_E6_orbitGroup_oddLieCentralQuotient
    (hgraph : OddE6GraphInput)
    (D : OrthogonalSemilinearFixedRootDatum .E7 p k) (hχ : D.χ = signMaskChar .E7 3)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    OddLieCentralQuotient p (D.withOrbit J').orbitGroup := by
  have hp : p.Prime := Fact.out
  have hadm : StatedLieAdmissible .E6 0 p (D.e * 2) := ⟨hp, by have := D.one_le_e; omega, rfl⟩
  exact e7_twisted_orbitGroup_oddLieCentralQuotient D (Or.inr rfl) hχ hθ J' hq
    simpleUnion_e7_three (fun hχ' i => e7_simple_inter_three hχ' i) ⟨0, by decide⟩
    fun K₂ _ _ hK₂ _ hα _ hL => oddLieCentralQuotient_of_E6_involution hgraph hp D.odd hadm
      (lieModel_pairSpan_E6 hp D.odd hK₂) hα hL

theorem e7TwistedOrbitGroupInput_of_E6Graph
    (hgraph : OddE6GraphInput) : E7TwistedOrbitGroupInput := by
  intro p _ k _ _ _ D m hm hχ hθ J' hq
  rcases hm with rfl | rfl
  · exact e7_twisted_A7_orbitGroup_oddLieCentralQuotient D hχ hθ J' hq
  · exact e7_twisted_E6_orbitGroup_oddLieCentralQuotient hgraph D hχ hθ J' hq

theorem oddExcInnerDiagInput_E7_of_E6Graph
    (hgraph : OddE6GraphInput) : OddExcInnerDiagInput .E7 :=
  oddExcInnerDiagInput_E7_of_twisted (e7TwistedOrbitGroupInput_of_E6Graph hgraph)

end CFSG.ComponentClassification.CatLeafProof
