module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Kernel
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeReturn
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Twist
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQuadDescentMain

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.ComponentClassification.CatLeaf
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem e6_twisted_orbitGroup_oddLieCentralQuotient
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
          OddLieCentralQuotient p L) :
    OddLieCentralQuotient p (D.withOrbit J').orbitGroup := by
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
  exact oddLieCentralQuotient_orbitGroup_of_quadGroup (D.withOrbit J') hθ2 hcard hnc hq
    (family_of_mulEquiv (QuotientGroup.congr _ _ eY (Subgroup.map_center_eq eY))
      (hfam _ hK₂))

theorem e6_two_simpleRootsJ
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) (hχ : D.χ = signMaskChar .E6 2)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) :
    (D.withOrbit J').simpleRootsJ = ∅ ∨ (D.withOrbit J').simpleRootsJ = Set.range e6A5Root ∨
      (D.withOrbit J').simpleRootsJ = {hiE6} := by
  classical
  set P : (Fin (Tag.rank .E6) → ℤ) → Prop := fun v => v (e6Node 1) ≠ 0
  have hP : ∀ α β : kernelRoots D.χ, iform (α : Fin (Tag.rank .E6) → ℤ) β ≠ 0 → P α → P β :=
    fun α β hαβ hα => e6_two_invariant ⟨α, hχ ▸ α.2⟩ ⟨β, hχ ▸ β.2⟩ hαβ hα
  have hcl : ∀ a b : kernelRoots D.χ, (⟦a⟧ : KernelComponent D.χ) = ⟦b⟧ → P a → P b :=
    fun a b hab ha => Classical.byContradiction fun hb => mk_ne_of_invariant P hP ha hb hab
  have hcls : ∀ (i : KernelComponent D.χ), ∀ β ∈ componentRoots D.χ i,
      ∀ β' ∈ componentRoots D.χ i, (P β ↔ P β') := by
    rintro i β ⟨hβ, hβi⟩ β' ⟨hβ', hβ'i⟩
    exact ⟨hcl ⟨β, hβ⟩ ⟨β', hβ'⟩ (hβi.trans hβ'i.symm),
      hcl ⟨β', hβ'⟩ ⟨β, hβ⟩ (hβ'i.trans hβi.symm)⟩
  have hpow : ∀ (n : ℕ) (γ : Fin (Tag.rank .E6) → ℤ), (D.θ ^ n) (toReal γ) =
      toReal ((thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm)^[n] γ) := by
    intro n
    induction n with
    | zero => intro γ; simp
    | succ n ih =>
      intro γ
      rw [pow_succ, Module.End.mul_apply, hθ, ih, Function.iterate_succ_apply]
  have hPθ : ∀ (n : ℕ) (γ : Fin (Tag.rank .E6) → ℤ),
      ((thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm)^[n] γ) (e6Node 1) =
        γ (e6Node 1) := by
    intro n
    induction n with
    | zero => intro γ; rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply, ih, thetaMap_e6_node1]
  obtain ⟨i₀, hi₀⟩ := J'.2
  have hJ : ∀ i ∈ (J' : Set (KernelComponent D.χ)), ∀ β ∈ componentRoots D.χ i,
      ∃ a ∈ componentRoots D.χ i₀, (P β ↔ P a) := by
    intro i hi β hβ
    rw [← hi₀] at hi
    obtain ⟨n, a, ha, b, hb, hab⟩ := hi
    rw [hpow] at hab
    refine ⟨a, ha, (hcls i β hβ b hb).trans ?_⟩
    rw [← toReal_injective hab]
    exact Iff.of_eq (congrArg (· ≠ 0) (hPθ n a))
  have hJP : ∀ i ∈ (J' : Set (KernelComponent D.χ)), ∀ i' ∈ (J' : Set (KernelComponent D.χ)),
      ∀ β ∈ componentRoots D.χ i, ∀ β' ∈ componentRoots D.χ i', (P β ↔ P β') := by
    intro i hi i' hi' β hβ β' hβ'
    obtain ⟨a, ha, h⟩ := hJ i hi β hβ
    obtain ⟨a', ha', h'⟩ := hJ i' hi' β' hβ'
    exact h.trans ((hcls i₀ a ha a' ha').trans h'.symm)
  have hmem : ∀ β, β ∈ (D.withOrbit J').simpleRootsJ ↔ β ∈ simpleUnion D.χ ∧
      ∃ i ∈ (J' : Set (KernelComponent D.χ)), β ∈ componentRoots D.χ i := fun β => by
    constructor
    · rintro ⟨⟨i, -, hβi⟩, h, hJβ⟩
      exact ⟨Set.mem_iUnion.2 ⟨i, hβi⟩, _, hJβ, h, rfl⟩
    · rintro ⟨hβ, i, hi, h, rfl⟩
      obtain ⟨i', hi'⟩ := Set.mem_iUnion.1 hβ
      exact ⟨⟨i', Set.mem_univ _, hi'⟩, h, hi⟩
  have hc := fun i => e6_simple_inter_two hχ i
  by_cases hA : ∃ i ∈ (J' : Set (KernelComponent D.χ)),
      simpleUnion D.χ ∩ componentRoots D.χ i = Set.range e6A5Root
  · obtain ⟨i, hi, hiA⟩ := hA
    have hA0 : e6A5Root 0 ∈ componentRoots D.χ i := by
      have h : e6A5Root 0 ∈ simpleUnion D.χ ∩ componentRoots D.χ i := hiA ▸ ⟨0, rfl⟩
      exact h.2
    refine Or.inr (Or.inl (Set.ext fun β => ⟨fun hβ => ?_, fun hβ => ?_⟩))
    · obtain ⟨hβΔ, i', hi', hβi'⟩ := (hmem β).1 hβ
      have hβ' : β ∈ simpleUnion D.χ ∩ componentRoots D.χ i' := ⟨hβΔ, hβi'⟩
      rcases hc i' with h | h | h
      · rw [h] at hβ'
        exact absurd hβ' (Set.notMem_empty β)
      · rwa [h] at hβ'
      · rw [h, Set.mem_singleton_iff] at hβ'
        subst hβ'
        exact absurd ((hJP i' hi' i hi _ hβi' _ hA0).1 (show hiE6 (e6Node 1) ≠ 0 by decide))
          (show ¬ e6A5Root 0 (e6Node 1) ≠ 0 by decide)
    · rw [← hiA] at hβ
      exact (hmem β).2 ⟨hβ.1, i, hi, hβ.2⟩
  · by_cases hT : ∃ i ∈ (J' : Set (KernelComponent D.χ)),
        simpleUnion D.χ ∩ componentRoots D.χ i = {hiE6}
    · obtain ⟨i, hi, hiT⟩ := hT
      refine Or.inr (Or.inr (Set.ext fun β => ⟨fun hβ => ?_, fun hβ => ?_⟩))
      · obtain ⟨hβΔ, i', hi', hβi'⟩ := (hmem β).1 hβ
        have hβ' : β ∈ simpleUnion D.χ ∩ componentRoots D.χ i' := ⟨hβΔ, hβi'⟩
        rcases hc i' with h | h | h
        · rw [h] at hβ'
          exact absurd hβ' (Set.notMem_empty β)
        · exact absurd ⟨i', hi', h⟩ hA
        · rwa [h] at hβ'
      · rw [← hiT] at hβ
        exact (hmem β).2 ⟨hβ.1, i, hi, hβ.2⟩
    · refine Or.inl (Set.eq_empty_of_forall_notMem fun β hβ => ?_)
      obtain ⟨hβΔ, i', hi', hβi'⟩ := (hmem β).1 hβ
      rcases hc i' with h | h | h
      · exact (Set.eq_empty_iff_forall_notMem.1 h) β ⟨hβΔ, hβi'⟩
      · exact hA ⟨i', hi', h⟩
      · exact hT ⟨i', hi', h⟩

end CFSG.ComponentClassification.CatLeafProof
