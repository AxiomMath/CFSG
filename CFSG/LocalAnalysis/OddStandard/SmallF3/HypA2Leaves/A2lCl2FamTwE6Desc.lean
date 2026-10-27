module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamDesc
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Kernel

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.ComponentClassification.CatLeaf
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

section


variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

variable {R : ℕ → Prop}

theorem cl24_e6_twisted_orbitGroup
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) {m : ℕ} (hm : m = 0 ∨ m = 20 ∨ m = 2)
    (hχ : D.χ = signMaskChar .E6 m)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup)
    {S : Set (Fin (Tag.rank .E6) → ℤ)} (hJS : (D.withOrbit J').simpleRootsJ = S)
    (hα₁ : Pi.single (e6Node 0) 1 ∈ S)
    (hfam : ∀ (K₂ : Type) [Field K₂] [Finite K₂], Nat.card K₂ = p ^ (D.e * 2) →
      ∀ α : MulAut (↥(pairSpan .E6 K₂ S) ⧸ Subgroup.center ↥(pairSpan .E6 K₂ S)),
        orderOf α = 2 → ∀ L : Subgroup (fixedSubgroup α), IsComponent L →
          Cl24Q p R L) :
    Cl24Q p R (D.withOrbit J').orbitGroup := by
  have hθ2 : ∀ β ∈ (D.withOrbit J').simpleRootsJ,
      (D.withOrbit J').θ ((D.withOrbit J').θ (toReal β)) = toReal β := by
    intro β _
    change D.θ (D.θ (toReal β)) = toReal β
    rw [hθ β, hθ, thetaMap_e6_twice]
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  have hθp : ThetaProperties TwistTag.E6.perm 2 (D.withOrbit J').χ
      (ToralSign.wordElt .E6 []) := by
    change ThetaProperties TwistTag.E6.perm 2 D.χ _
    rw [hχ]
    rcases hm with rfl | rfl | rfl
    · exact h6.theta ⟨0, 1, 1, e6OmegaWords0⟩ (by simp [e6SignDiagramReps]) []
        (by simp [e6OmegaWords0])
    · exact h6.theta ⟨20, 27, 1, e6OmegaWords20⟩ (by simp [e6SignDiagramReps]) []
        (by simp [e6OmegaWords20])
    · exact h6.theta ⟨2, 36, 1, e6OmegaWords2⟩ (by simp [e6SignDiagramReps]) []
        (by simp [e6OmegaWords2])
  have hcard : ∀ O ∈ (D.withOrbit J').orbits, orbitCard O = 1 ∨ orbitCard O = 2 := fun O hO =>
    ClassicalInvolution.ModelFacts.orbitCard_eq_of_thetaProperties (D.withOrbit J') hθp hθ hO
  have hα₁J : Pi.single (e6Node 0) 1 ∈ (D.withOrbit J').simpleRootsJ := hJS ▸ hα₁
  have hr1 : IsRoot .E6 (Pi.single (e6Node 0) 1) := isRoot_single _ _
  have hr6 : IsRoot .E6 (Pi.single (e6Node 5) 1) := isRoot_single _ _
  set y : adjointGroup .E6 k :=
    ⟨rootSL2 .E6 k (Pi.single (e6Node 0) 1) (uSL 1), rootSL2_mem_adjointGroup hr1 _⟩ with hy
  set x : adjointGroup .E6 k :=
    ⟨rootSL2 .E6 k (Pi.single (e6Node 0) 1) (vSL 1), rootSL2_mem_adjointGroup hr1 _⟩ with hx
  have hFy : ((D.withOrbit J').F y : ModGL .E6 k) =
      rootSL2 .E6 k (Pi.single (e6Node 5) 1) (uSL 1) := by
    have h := (D.withOrbit J').map_rootSL2 _ hα₁J.1 (Pi.single (e6Node 5) 1)
      (by change D.θ _ = _; rw [hθ, thetaMap_e6_alpha1]) (uSL 1) y rfl
    rw [h, LieType.Chevalley.map_uSL, map_one]
  have hnc : ∃ y ∈ quadGens (D.withOrbit J'), ∃ x ∈ quadGens (D.withOrbit J'),
      ¬ Commute ((D.withOrbit J').F y * y⁻¹) x := by
    refine ⟨y, ⟨_, hα₁J, 1, one_mem _, Or.inl rfl⟩, x, ⟨_, hα₁J, 1, one_mem _, Or.inr rfl⟩,
      fun hc => ?_⟩
    have hc' := hc.map (adjointGroup .E6 k).subtype
    simp only [map_mul, map_inv, Subgroup.coe_subtype] at hc'
    rw [hFy] at hc'
    have ha : Commute (rootSL2 .E6 k (Pi.single (e6Node 5) 1) (uSL 1)) (x : ModGL .E6 k) := by
      have hmem6 : rootSL2 .E6 k (Pi.single (e6Node 5) 1) (uSL 1) ∈
          rootSubgroup .E6 k (Pi.single (e6Node 5) 1) := by
        rw [rootSL2_uSL_eq]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      obtain ⟨ε, -, hε⟩ := exists_rootSL2_vSL_eq (K := k) hr1
      have hmem1 : (x : ModGL .E6 k) ∈ rootSubgroup .E6 k (-Pi.single (e6Node 0) 1) := by
        change rootSL2 .E6 k _ (vSL 1) ∈ _
        rw [hε]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      exact (simply_laced_orthogonal_root_commutation .E6 (Or.inr (Or.inl rfl))).2 k
        _ _ hr6 (IsRoot.neg hr1) (by decide) _ hmem6 _ hmem1
    have hb : Commute (y : ModGL .E6 k) (x : ModGL .E6 k) := by
      have h1 := ha.inv_left.mul_left hc'
      rw [← mul_assoc, inv_mul_cancel, one_mul] at h1
      simpa using h1.inv_left
    have hAB : rootSL2 .E6 k (Pi.single (e6Node 0) 1) (uSL 1 * vSL 1) =
        rootSL2 .E6 k (Pi.single (e6Node 0) 1) (vSL 1 * uSL 1) := by
      rw [map_mul, map_mul]
      exact hb.eq
    have h2 : ((uSL (1 : k) * vSL 1 : SL2 k) : Matrix (Fin 2) (Fin 2) k) 0 0 =
        ((vSL (1 : k) * uSL 1 : SL2 k) : Matrix (Fin 2) (Fin 2) k) 0 0 :=
      congrArg (fun A : SL2 k => (A : Matrix (Fin 2) (Fin 2) k) 0 0)
        (rootSL2_injective_of_field (Pi.single (e6Node 0) 1) hAB)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
    simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at h2
  have hK₂ : Nat.card (frobeniusFixedField k p (D.e * 2)) = p ^ (D.e * 2) :=
    card_frobeniusFixedField (by have := D.one_le_e; omega)
  have : Finite (frobeniusFixedField k p (D.e * 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hK₂]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let eY : quadGroup (D.withOrbit J') ≃* pairSpan .E6 (frobeniusFixedField k p (D.e * 2)) S :=
    (((quadGroup (D.withOrbit J')).equivMapOfInjective _
      (adjointGroup .E6 k).subtype_injective).trans
        (MulEquiv.subgroupCongr (map_subtype_quadGroup (D.withOrbit J')))).trans
      (((pairSpan .E6 _ _).equivMapOfInjective _ (baseChangeGL_injective _)).symm.trans
        (MulEquiv.subgroupCongr (congrArg (pairSpan .E6 _) hJS)))
  exact cl24_orbitGroup_of_quadGroup (D.withOrbit J') hθ2 hcard hnc hq
    (cl24_family_of_mulEquiv (QuotientGroup.congr _ _ eY (Subgroup.map_center_eq eY))
      (hfam _ hK₂))

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
