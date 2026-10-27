module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2E7T
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2T1
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Fam

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open scoped MatrixGroups
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups
open CFSG.ComponentClassification.Burgoyne.X10

theorem noPSL2Odd_pairSpan_hiE6
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hq : IsQuasisimple (pairSpan .E6 K {hiE6})) :
    NoPSL2Odd (pairSpan .E6 K {hiE6}) := by
  obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨-, ⟨eQ⟩, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components .E6 K hK2 isRoot_hiE6
  let e₀ : pairSpan .E6 K {hiE6} ≃*
      (rootSubgroup .E6 K hiE6 ⊔ rootSubgroup .E6 K (-hiE6) : Subgroup (ModGL .E6 K)) :=
    MulEquiv.subgroupCongr (pairSpan_singleton .E6 K hiE6)
  by_cases h5 : 5 ≤ Nat.card K
  · exact noPSL2Odd_of_mulEquiv_SL2 hK2 (e₀.trans eQ.symm)
  · exfalso
    have h3' : Nat.card K = 3 := by
      have hodd : Odd (Nat.card K) := by
        rw [hK]
        exact (hp.eq_two_or_odd'.resolve_left hp2).pow
      obtain ⟨k, hk⟩ := hodd
      omega
    have := (hfin.1 h3').1
    exact LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hq
      (Group.isSolvable_of_isSolvable_injective (f := e₀.toMonoidHom) e₀.injective)

section Datum

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem noPSL2Odd_e6_twisted_orbitGroup
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) {m : ℕ} (hm : m = 0 ∨ m = 20 ∨ m = 2)
    (hχ : D.χ = signMaskChar .E6 m)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup)
    {S : Set (Fin (Tag.rank .E6) → ℤ)} (hJS : (D.withOrbit J').simpleRootsJ = S)
    (hα₁ : Pi.single (e6Node 0) 1 ∈ S)
    (hfam : ∀ (K₂ : Type) [Field K₂] [Finite K₂], Nat.card K₂ = p ^ (D.e * 2) →
      ∀ α : MulAut (↥(pairSpan .E6 K₂ S) ⧸ Subgroup.center ↥(pairSpan .E6 K₂ S)),
        orderOf α = 2 → ∀ L : Subgroup (fixedSubgroup α), IsComponent L → NoPSL2Odd L) :
    NoPSL2Odd (D.withOrbit J').orbitGroup := by
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
  exact noPSL2Odd_orbitGroup_of_quadGroup (D.withOrbit J') hθ2 hcard hnc hq
    (noPSL2Odd_family_of_mulEquiv (QuotientGroup.congr _ _ eY (Subgroup.map_center_eq eY))
      (hfam _ hK₂))

theorem noPSL2Odd_e6_twisted_zero_orbitGroup
    (hO : LieOrderFormulasInput) (D : OrthogonalSemilinearFixedRootDatum .E6 p k)
    (hχ : D.χ = signMaskChar .E6 0)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    NoPSL2Odd (D.withOrbit J').orbitGroup := by
  have hp : p.Prime := Fact.out
  have hadm : StatedLieAdmissible .E6 0 p (D.e * 2) := ⟨hp, by have := D.one_le_e; omega, rfl⟩
  have hΔ : simpleUnion (D.withOrbit J').χ = Set.range e6SimpleRoot := by
    change simpleUnion D.χ = _
    rw [hχ]
    exact simpleUnion_e6_zero
  rcases simpleRootsJ_eq_empty_or_eq (D.withOrbit J') hΔ (fun i => e6_simple_inter_zero hχ i)
    with h0 | hJS
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
  · exact noPSL2Odd_e6_twisted_orbitGroup D (Or.inl rfl) hχ hθ J' hq hJS ⟨0, rfl⟩
      fun K₂ _ _ hK₂ _ hα _ hL => noPSL2Odd_of_E6_involution hO
        hp D.odd hadm (lieModel_pairSpan_e6Simple hp D.odd hK₂) hα hL

theorem noPSL2Odd_e6_two_theta_orbitGroup
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup)
    (hJS : (D.withOrbit J').simpleRootsJ = {hiE6}) :
    NoPSL2Odd (D.withOrbit J').orbitGroup := by
  have hfix : ∀ β ∈ (D.withOrbit J').simpleRootsJ,
      (D.withOrbit J').θ (toReal β) = toReal β := by
    intro β hβ
    rw [hJS, Set.mem_singleton_iff] at hβ
    subst hβ
    change D.θ _ = _
    rw [hθ, thetaMap_e6_hiE6]
  have horb := orbitGroup_eq_map_pairSpan (D.withOrbit J') hfix
  rw [hJS] at horb
  have hK : Nat.card (frobeniusFixedField k p D.e) = p ^ D.e :=
    card_frobeniusFixedField D.one_le_e
  have : Finite (frobeniusFixedField k p D.e) :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let e : (D.withOrbit J').orbitGroup ≃* pairSpan .E6 (frobeniusFixedField k p D.e) {hiE6} :=
    (MulEquiv.subgroupCongr horb).trans
      ((Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective _)).symm)
  exact NoPSL2Odd.of_mulEquiv e
    (noPSL2Odd_pairSpan_hiE6 (Fact.out : p.Prime) D.odd hK
      (LocalCores.isQuasisimple_of_mulEquiv e hq))

theorem noPSL2Odd_twE6A5
    (hO : LieOrderFormulasInput) (D : OrthogonalSemilinearFixedRootDatum .E6 p k)
    (hχ : D.χ = signMaskChar .E6 2)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup)
    (hA : (D.withOrbit J').simpleRootsJ = Set.range e6A5Root) :
    NoPSL2Odd (D.withOrbit J').orbitGroup := by
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
  exact noPSL2Odd_orbitGroup_of_slFrame hO (D.withOrbit J') hA hθ2 hcard hq (m := 5)
    (Or.inl rfl) (isRoot_single _ _) ⟨2, rfl⟩ hθα₄ 2 ⟨Ψ, hker, hrange, hrk 2⟩

theorem noPSL2Odd_e6_twisted_two_orbitGroup
    (hO : LieOrderFormulasInput) (D : OrthogonalSemilinearFixedRootDatum .E6 p k)
    (hχ : D.χ = signMaskChar .E6 2)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    NoPSL2Odd (D.withOrbit J').orbitGroup := by
  rcases e6_two_simpleRootsJ D hχ hθ J' with h0 | hA | hT
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
  · exact noPSL2Odd_twE6A5 hO D hχ hθ J' hq hA
  · exact noPSL2Odd_e6_two_theta_orbitGroup D hθ J' hq hT

set_option maxHeartbeats 800000 in
theorem noPSL2Odd_twE6Twenty
    (hO : LieOrderFormulasInput) (D : OrthogonalSemilinearFixedRootDatum .E6 p k)
    (hχ : D.χ = signMaskChar .E6 20)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    NoPSL2Odd (D.withOrbit J').orbitGroup := by
  have hp : p.Prime := Fact.out
  have he : 1 ≤ D.e := D.one_le_e
  have hΔ : simpleUnion (D.withOrbit J').χ = Set.range e6D5TwRoot := by
    change simpleUnion D.χ = _
    rw [hχ]
    exact simpleUnion_e6_twenty
  rcases simpleRootsJ_eq_empty_or_eq (D.withOrbit J') hΔ (fun i => e6_simple_inter_twenty hχ i)
    with h0 | hJS
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
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
    exact h6.theta ⟨20, 27, 1, e6OmegaWords20⟩ (by simp [e6SignDiagramReps]) []
      (by simp [e6OmegaWords20])
  have hcard : ∀ O ∈ (D.withOrbit J').orbits, orbitCard O = 1 ∨ orbitCard O = 2 := fun O hO =>
    ClassicalInvolution.ModelFacts.orbitCard_eq_of_thetaProperties (D.withOrbit J') hθp hθ hO
  refine noPSL2Odd_orbitGroup_of_quadGroup_at (D.withOrbit J') hθ2 hcard hq fun L hL => ?_
  have hK₂ : Nat.card (frobeniusFixedField k p (D.e * 2)) = p ^ (D.e * 2) :=
    card_frobeniusFixedField (by omega)
  have : Finite (frobeniusFixedField k p (D.e * 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hK₂]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨eY₀, heY₀⟩ := exists_quadGroup_equiv_pairSpan (D.withOrbit J') hJS
  let eY : quadGroup (D.withOrbit J') ≃*
      pairSpan .E6 (frobeniusFixedField k p (D.e * 2)) (Set.range e6D5TwRoot) := eY₀
  have heY : ∀ y, baseChangeGL (frobeniusFixedField k p (D.e * 2)).subtype
      ((eY y : pairSpan .E6 (frobeniusFixedField k p (D.e * 2)) (Set.range e6D5TwRoot)) :
        ModGL .E6 (frobeniusFixedField k p (D.e * 2))) =
      ((y : adjointGroup .E6 k) : ModGL .E6 k) := heY₀
  obtain ⟨θ, hθs, hθk, N, r, hN2, hN0, hr, hR1, hR2⟩ := exists_pairSpan_e6D5Tw_proj hp D.odd hK₂
  let Φ : ↥(quadGroup (D.withOrbit J')) ⧸ Subgroup.center ↥(quadGroup (D.withOrbit J')) ≃*
      matrixProjectiveDerived (coordinateQuadPlus 5 (frobeniusFixedField k p (D.e * 2))) :=
    (QuotientGroup.congr _ _ eY (Subgroup.map_center_eq eY)).trans
      ((QuotientGroup.quotientMulEquivOfEq hθk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective θ hθs))
  have hΦ : ∀ y : quadGroup (D.withOrbit J'),
      Φ (y : ↥(quadGroup (D.withOrbit J')) ⧸ Subgroup.center ↥(quadGroup (D.withOrbit J'))) =
        θ (eY y) := fun y => rfl
  have hα₄ : e6D5TwRoot 0 ∈ (D.withOrbit J').simpleRootsJ := hJS ▸ e6D5TwRoot_zero_mem
  have hr4 : IsRoot .E6 (e6D5TwRoot 0) := isRoot_single _ _
  let y : frobeniusFixedField k p (D.e * 2) → quadGroup (D.withOrbit J') := fun c =>
    ⟨⟨rootSL2 .E6 k (e6D5TwRoot 0) (uSL (c : k)), rootSL2_mem_adjointGroup hr4 _⟩,
      Subgroup.subset_closure ⟨_, hα₄, (c : k), c.2, Or.inl rfl⟩⟩
  have heYy : ∀ c, eY (y c) = ⟨rootSL2 .E6 _ (e6D5TwRoot 0) (uSL c),
      rootSL2_uSL_mem_pairSpan e6D5TwRoot_zero_mem c⟩ := by
    intro c
    apply Subtype.ext
    apply baseChangeGL_injective (frobeniusFixedField k p (D.e * 2)).subtype
    rw [heY, baseChangeGL_rootSL2_of_field, CFSG.LieType.Chevalley.map_uSL]
    rfl
  have hθα₄ : (D.withOrbit J').θ (toReal (e6D5TwRoot 0)) = toReal (e6D5TwRoot 0) := by
    change D.θ _ = _
    rw [hθ]
    exact congrArg toReal thetaMap_e6_alpha4
  have hσy : ∀ c, quadAut (D.withOrbit J') hθ2 (y c) = y (c ^ p ^ D.e) := by
    intro c
    apply Subtype.ext
    apply Subtype.ext
    have h := (D.withOrbit J').map_rootSL2 _ hα₄.1 _ hθα₄ (uSL (c : k)) (y c).1 rfl
    change ((D.withOrbit J').F (y c).1 : ModGL .E6 k) = _
    rw [h, CFSG.LieType.Chevalley.map_uSL]
    change rootSL2 .E6 k _ (uSL (iterateFrobenius k p D.e (c : k))) =
      rootSL2 .E6 k _ (uSL ((c ^ p ^ D.e : frobeniusFixedField k p (D.e * 2)) : k))
    rw [iterateFrobenius_def, SubmonoidClass.coe_pow]
  set α := MulAut.congr Φ (quadAutBar (D.withOrbit J') hθ2) with hα
  set w : frobeniusFixedField k p (D.e * 2) →
      matrixProjectiveDerived (coordinateQuadPlus 5 (frobeniusFixedField k p (D.e * 2))) :=
    fun c => θ ⟨rootSL2 .E6 _ (e6D5TwRoot 0) (uSL c),
      rootSL2_uSL_mem_pairSpan e6D5TwRoot_zero_mem c⟩ with hw
  have hwy : ∀ c, w c = Φ (y c : ↥(quadGroup (D.withOrbit J')) ⧸
      Subgroup.center ↥(quadGroup (D.withOrbit J'))) := fun c => by
    rw [hΦ, heYy]
  have hact : ∀ c, α (w c) = w (c ^ p ^ D.e) := by
    intro c
    rw [hwy, hwy, hα, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, quadAutBar_mk, hσy]
  have hα2 : α ^ 2 = 1 := by
    rw [hα, ← map_pow, quadAutBar_sq, map_one]
  have hfix := card_pow_fixed_frobeniusFixedField (k := k) (p := p) he
  have h1 : Nat.card {c : frobeniusFixedField k p (D.e * 2) // c ^ p ^ D.e = c} ≠ 1 := by
    rw [hfix]
    exact (Nat.one_lt_pow (by omega) hp.one_lt).ne'
  have hKc : Nat.card {c : frobeniusFixedField k p (D.e * 2) // c ^ p ^ D.e = c} ≠
      Nat.card (frobeniusFixedField k p (D.e * 2)) := by
    rw [hfix, hK₂]
    intro h
    have := Nat.pow_right_injective hp.two_le h
    omega
  refine noPSL2Odd_of_component_equiv (fixedSubgroupCongrEquiv Φ _) (fun M hM => ?_) hL
  exact noPSL2Odd_of_root_fixed hO hp D.odd (by omega) hK₂ α hα2 hN2 hN0 r hr w
    (fun c => c ^ p ^ D.e) hR1 hR2 hact h1 hKc M hM

end Datum

theorem twE6InnerNoPSL2_holds
    (hO : LieOrderFormulasInput) :
    ∀ (J : Type) [Group J] (p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible .twistedE6 0 p f →
      Blueprint.LieModel J .twistedE6 0 p f → ∀ α : MulAut J, orderOf α = 2 →
        α ∈ (MulAut.conj : J →* MulAut J).range →
        ∀ L : Subgroup (fixedSubgroup α), IsComponent L → NoPSL2Odd L := by
  intro J _ p f hp hp2 hadm hm α hα hαi L hL
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, σ, hF, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp hf
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  have hF2 : Nat.card F = (p ^ f) ^ 2 := hF
  have : CharP F p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (show 1 ≤ f * 2 by omega) (by rw [hF2, ← pow_mul])
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p F (AlgebraicClosure F)
  have hα' : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hα'2 : MulAut.congr e α ^ 2 = 1 := by
    rw [← hα']
    exact pow_orderOf_eq_one _
  have hα'i : MulAut.congr e α ∈ twistedE6Inn F σ := by
    obtain ⟨g, hg⟩ := hαi
    exact ⟨e g, by rw [← hg, mulAut_congr_conj_twistedE6]⟩
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    LocalAnalysis.SteinbergCE.exists_mulEquiv_twisted_E6_inner_fixed hp2 hf hF2 σ hσ hα'2 hα'i
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, n6, -⟩ :=
    rational_toral_twist_semilinear_pinning_normalization (k := AlgebraicClosure F) p hp2 f hf
  obtain ⟨-, r6, -⟩ :=
    rational_inner_involution_finite_toral_twist_reduction p (AlgebraicClosure F) hp2 f hf
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure F))
    (frobTwistGL TwistTag.E6.tag (AlgebraicClosure F) p f
      (diagramMap TwistTag.E6 (AlgebraicClosure F))) with hR
  set N := ⁅R, R⁆ ⊓ Subgroup.centralizer {x} with hN
  have hRfin : Finite R := finite_fixedPointsIn_frobTwistGL p hf (by decide)
    (units_map_entrywiseHom_diagramMap (t := TwistTag.E6)
      (iterateFrobenius (AlgebraicClosure F) p f))
    (diagramMap_pow_order TwistTag.E6 (AlgebraicClosure F))
  have hNR : N ≤ R := fun y hy => Subgroup.commutator_le_self _ hy.1
  have hNfin : Finite N := Finite.of_injective _ (Subgroup.inclusion_injective hNR)
  let Ψ : fixedSubgroup α ≃* N := (fixedSubgroupCongrEquiv e α).trans eA
  set S' : Subgroup N := L.map Ψ.toMonoidHom with hS'
  have hS'c : IsComponent S' := LocalCores.isComponent_map_mulEquiv Ψ hL
  have hMN : S'.map N.subtype ≤ N := Subgroup.map_subtype_le _
  have hsub : (S'.map N.subtype).subgroupOf N = S' :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective S'
  have hS'N : Assembly.IsComponentOf (S'.map N.subtype) N :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hMN).2
      (by rw [hsub]; exact hS'c)
  obtain ⟨Dd, J₀, ⟨mr, hmr, l, hl, hDχ, hDθ⟩, hXfin, hJ₀X, hJ₀c, ⟨eL⟩⟩ :=
    LocalAnalysis.SteinbergCA.exists_datum_isPComponent_of_twistReduction p hp2 hk hf
      (Or.inr (Or.inl rfl)) TwistTag.E6.cartan_perm symmetrizedCartan_perm_E6 h6.theta
      (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.E6 l hγ)
      (diagramMap_mem_normalizer TwistTag.E6) (map_conj_diagramMap TwistTag.E6 _ (Or.inl rfl))
      n6 (r6 x hxR hx2) (S'.map N.subtype) hMN
      (@ExcSelector.isPComponent_two_subgroupOf _ _ _ _ hNfin hS'N)
  obtain ⟨J', hJ', hq⟩ := ExcSelector.exists_eq_orbitGroupC_of_isPComponent' Dd hXfin hJ₀X hJ₀c
  let eLJ : L ≃* (Dd.withOrbit J').orbitGroup :=
    ((L.equivMapOfInjective _ Ψ.injective).trans
      ((S'.equivMapOfInjective _ N.subtype_injective).trans
        (eL.trans (MulEquiv.subgroupCongr hJ')))).trans
      (Subgroup.subgroupOfEquivOfLe (Dd.withOrbit J').orbitGroup_le_adjointGroup)
  refine NoPSL2Odd.of_mulEquiv eLJ ?_
  simp only [e6SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at hmr
  rcases hmr with rfl | rfl | rfl
  · simp only [e6OmegaWords0, List.mem_cons, List.mem_nil_iff, or_false] at hl
    subst hl
    exact noPSL2Odd_e6_twisted_zero_orbitGroup hO Dd hDχ hDθ J' hq
  · simp only [e6OmegaWords20, List.mem_cons, List.mem_nil_iff, or_false] at hl
    subst hl
    exact noPSL2Odd_twE6Twenty hO Dd hDχ hDθ J' hq
  · simp only [e6OmegaWords2, List.mem_cons, List.mem_nil_iff, or_false] at hl
    subst hl
    exact noPSL2Odd_e6_twisted_two_orbitGroup hO Dd hDχ hDθ J' hq

theorem famInnerNoPSL2_twistedE6
    (hO : LieOrderFormulasInput) : FamInnerNoPSL2 .twistedE6 := by
  intro J _ n p f hp hp2 hadm hm g hg L hL
  obtain rfl : n = 0 := hadm.2.2
  exact twE6InnerNoPSL2_holds hO J p f hp hp2 hadm hm (MulAut.conj g) hg ⟨g, rfl⟩ L hL

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
