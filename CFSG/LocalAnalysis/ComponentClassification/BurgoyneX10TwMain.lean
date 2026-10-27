module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10TwDesc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10T1Main

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem thetaMap_e7Word2_1_alpha5 :
    thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 (Pi.single (e7Node 4) 1) =
      Pi.single (e7Node 4) 1 := by
  have h : applyWordIdx e7Certificate e7Word2_1 4 = 4 := by decide +kernel
  obtain ⟨hl4, hr4⟩ := root_fin e7Certificate_check (e7Node 4)
  obtain ⟨-, he⟩ := applyWordIdx_spec e7Certificate_check e7Word2_1 hl4
  rw [thetaMap_one_apply, ← hr4, ← he]
  change e7Certificate.root (applyWordIdx e7Certificate e7Word2_1 4) = _
  rw [h]
  rfl

theorem twE6A5P_model :
    TwE6A5P CompPred.model := by
  intro p _ k _ _ _ D hχ hθ J' hq hA
  have hp : p.Prime := Fact.out
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
    exact h6.theta ⟨2, 36, 1, e6OmegaWords2⟩ (by simp [e6SignDiagramReps]) []
      (by simp [e6OmegaWords2])
  have hcard : ∀ O ∈ (D.withOrbit J').orbits, orbitCard O = 1 ∨ orbitCard O = 2 := fun O hO =>
    ClassicalInvolution.ModelFacts.orbitCard_eq_of_thetaProperties (D.withOrbit J') hθp hθ hO
  have hθα₄ : (D.withOrbit J').θ (toReal (e6A5Root 2)) = toReal (e6A5Root 2) := by
    change D.θ (toReal (Pi.single (e6Node 3) 1)) = toReal (Pi.single (e6Node 3) 1)
    rw [hθ]
    exact congrArg toReal thetaMap_e6_alpha4
  have hK₂ : Nat.card (frobeniusFixedField k p ((D.withOrbit J').e * 2)) =
      p ^ ((D.withOrbit J').e * 2) :=
    card_frobeniusFixedField (by have := D.one_le_e; change 0 < D.e * 2; omega)
  have : Finite (frobeniusFixedField k p ((D.withOrbit J').e * 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hK₂]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨Ψ, hker, hrange, hrk⟩ := exists_psi_A5_E6_rankOne hp D.odd hK₂
  exact excCompModel_orbitGroup_of_slFrame (D.withOrbit J') hA hθ2 hcard hq (m := 5)
    (Or.inl rfl) (isRoot_single _ _) ⟨2, rfl⟩ hθα₄ 2 ⟨Ψ, hker, hrange, hrk 2⟩

theorem e7TwistedA7P_model :
    E7TwistedA7P CompPred.model := by
  intro p _ k _ _ _ D hχ hθ J' hq
  have hp : p.Prime := Fact.out
  have hΔ : simpleUnion (D.withOrbit J').χ = Set.range e7A7Root := by
    change simpleUnion D.χ = _
    rw [hχ]
    exact simpleUnion_e7_two
  rcases simpleRootsJ_eq_empty_or_eq (D.withOrbit J') hΔ (e7_simple_inter_two hχ) with h0 | hJS
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
  have hθ2 : ∀ β ∈ (D.withOrbit J').simpleRootsJ,
      (D.withOrbit J').θ ((D.withOrbit J').θ (toReal β)) = toReal β := by
    intro β hβ
    rw [hJS, ← simpleUnion_e7_two] at hβ
    change D.θ (D.θ (toReal β)) = toReal β
    rw [hθ β, hθ, thetaMap_e7Word2_1_twice (Or.inl rfl) hβ]
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  have hθp : ThetaProperties 1 2 (D.withOrbit J').χ (ToralSign.wordElt .E7 e7Word2_1) := by
    change ThetaProperties 1 2 D.χ _
    rw [hχ]
    exact h7.theta ⟨2, 36, 2, e7OmegaWords2⟩ (by simp [e7SignDiagramReps]) e7Word2_1
      (by simp [e7OmegaWords2])
  have hcard : ∀ O ∈ (D.withOrbit J').orbits, orbitCard O = 1 ∨ orbitCard O = 2 := fun O hO =>
    ClassicalInvolution.ModelFacts.orbitCard_eq_of_thetaProperties (D.withOrbit J') hθp hθ hO
  have h3 : e7A7Root 3 = Pi.single (e7Node 4) 1 := by
    simp [e7A7Root, e7A7Node]
  have hθα₅ : (D.withOrbit J').θ (toReal (e7A7Root 3)) = toReal (e7A7Root 3) := by
    rw [h3]
    change D.θ _ = _
    rw [hθ]
    exact congrArg toReal thetaMap_e7Word2_1_alpha5
  have hK₂ : Nat.card (frobeniusFixedField k p ((D.withOrbit J').e * 2)) =
      p ^ ((D.withOrbit J').e * 2) :=
    card_frobeniusFixedField (by have := D.one_le_e; change 0 < D.e * 2; omega)
  have : Finite (frobeniusFixedField k p ((D.withOrbit J').e * 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hK₂]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨Ψ, hker, hrange, hrk⟩ := exists_psi_A7_E7_rankOne hp D.odd hK₂
  exact excCompModel_orbitGroup_of_slFrame (D.withOrbit J') hJS hθ2 hcard hq (m := 7)
    (Or.inr rfl) (by rw [h3]; exact isRoot_single _ _) ⟨3, rfl⟩ hθα₅ 3 ⟨Ψ, hker, hrange, hrk 3⟩

theorem excFamilyModel_twistedE6_holds :
    ExcFamilyModel .twistedE6 :=
  excFamilyModel_twistedE6_of twE6TwentyP_model twE6A5P_model

theorem excFamilyModel_E7_holds :
    ExcFamilyModel .E7 :=
  excFamilyModel_E7_of_A7 e7TwistedA7P_model

end CFSG.ComponentClassification.Burgoyne.X10
