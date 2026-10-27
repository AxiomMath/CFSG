module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBStabilizerFamily
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixDerived matrixProjectiveDerived matrixProjectiveImage matrixProjectiveProjection
    matrixLinearEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus projectivePointFamilyAut plusIndexEquiv reindexVectorEquiv
    reindexQuadraticForm_map)
open scoped Pointwise

namespace ThreeFamily

section Counting

variable {M X : Type*} [Group M] [MulAction M X]

theorem card_fixed_smul_set {c η : M} (h : η * c = c * η) (S : Set X) :
    Nat.card {x : X // x ∈ η • S ∧ c • x = x} = Nat.card {x : X // x ∈ S ∧ c • x = x} := by
  have h' : c * η⁻¹ = η⁻¹ * c := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h, mul_inv_cancel_right]
  exact Nat.card_congr
    { toFun := fun x => ⟨η⁻¹ • x.1, Set.mem_smul_set_iff_inv_smul_mem.mp x.2.1, by
        rw [smul_smul, h', mul_smul, x.2.2]⟩
      invFun := fun x => ⟨η • x.1, Set.smul_mem_smul_set x.2.1, by
        rw [smul_smul, ← h, mul_smul, x.2.2]⟩
      left_inv := fun x => Subtype.ext (smul_inv_smul η x.1)
      right_inv := fun x => Subtype.ext (inv_smul_smul η x.1) }

theorem smul_eq_of_fixed_counts {c η : M} (hη : η ^ 3 = 1) (h : η * c = c * η)
    {S C₁ C₂ : Set X} (h1 : η • S ∈ ({S, C₁, C₂} : Set (Set X)))
    (h2 : (η * η) • S ∈ ({S, C₁, C₂} : Set (Set X)))
    (hcount : Nat.card {x : X // x ∈ C₁ ∧ c • x = x} + Nat.card {x : X // x ∈ C₂ ∧ c • x = x} ≠
      2 * Nat.card {x : X // x ∈ S ∧ c • x = x}) : η • S = S := by
  by_contra hne
  have hne2 : (η * η) • S ≠ S := by
    intro h2'
    apply hne
    calc η • S = η • ((η * η) • S) := by rw [h2']
      _ = (η * (η * η)) • S := by rw [smul_smul]
      _ = S := by rw [← pow_three, hη, one_smul]
  have hne12 : (η * η) • S ≠ η • S := by
    intro h12
    apply hne
    have h3 := congrArg (fun T : Set X => η⁻¹ • T) h12
    simp only [mul_smul, inv_smul_smul] at h3
    exact h3
  have hc1 := card_fixed_smul_set h S
  have hc2 : Nat.card {x : X // x ∈ (η * η) • S ∧ c • x = x} =
      Nat.card {x : X // x ∈ S ∧ c • x = x} := by
    rw [mul_smul, card_fixed_smul_set h, card_fixed_smul_set h]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  rcases h1 with h1 | h1 | h1
  · exact hne h1
  all_goals rcases h2 with h2 | h2 | h2
  all_goals first
    | exact hne2 h2
    | exact hne12 (h2.trans h1.symm)
    | (rw [← h1, ← h2] at hcount; omega)

theorem card_fixed_image {α β : Type*} (s : α → β) {S : Set α} (hs : Set.InjOn s S)
    (φ : α → α) (ψ : β → β) (hφ : ∀ a ∈ S, φ a ∈ S) (hcomm : ∀ a ∈ S, ψ (s a) = s (φ a)) :
    Nat.card {b : β // b ∈ s '' S ∧ ψ b = b} = Nat.card {a : α // a ∈ S ∧ φ a = a} := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun a => ⟨s a.1, ⟨a.1, a.2.1, rfl⟩, by rw [hcomm _ a.2.1, a.2.2]⟩) ⟨?_, ?_⟩)
  · intro a b hab
    exact Subtype.ext (hs a.2.1 b.2.1 (congrArg Subtype.val hab))
  · rintro ⟨_, ⟨a, ha, rfl⟩, hfix⟩
    refine ⟨⟨a, ha, hs (hφ a ha) ha ?_⟩, rfl⟩
    rw [← hcomm a ha, hfix]

end Counting

section Congr

variable {K : Type*} [Field K] {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
  [Module K V']

theorem card_invariant_singular_congr {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}
    (r : V ≃ₗ[K] V') (hr : ∀ x, Q' (r x) = Q x) {g : V ≃ₗ[K] V} {g' : V' ≃ₗ[K] V'}
    (hg : ∀ x, g' (r x) = r (g x)) (k : ℕ) :
    Nat.card {L' : Submodule K V' //
        L' ∈ singularSubspaces Q' k ∧ L'.map (g' : V' →ₗ[K] V') = L'} =
      Nat.card {L : Submodule K V //
        L ∈ singularSubspaces Q k ∧ L.map (g : V →ₗ[K] V) = L} := by
  have hcomp : (g' : V' →ₗ[K] V').comp (r : V →ₗ[K] V') =
      (r : V →ₗ[K] V').comp (g : V →ₗ[K] V) := LinearMap.ext hg
  have hg' : ∀ x, g (r.symm x) = r.symm (g' x) := fun x =>
    r.injective (by rw [← hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
  have hcomp' : (g : V →ₗ[K] V).comp (r.symm : V' →ₗ[K] V) =
      (r.symm : V' →ₗ[K] V).comp (g' : V' →ₗ[K] V') := LinearMap.ext hg'
  have hr' : ∀ x, Q (r.symm x) = Q' x := fun x => by rw [← hr, LinearEquiv.apply_symm_apply]
  have hfwd : ∀ L : {L : Submodule K V // L ∈ singularSubspaces Q k ∧ L.map (g : V →ₗ[K] V) = L},
      L.1.map (r : V →ₗ[K] V') ∈ singularSubspaces Q' k ∧
        (L.1.map (r : V →ₗ[K] V')).map (g' : V' →ₗ[K] V') = L.1.map (r : V →ₗ[K] V') := by
    intro L
    refine ⟨⟨by rw [LinearEquiv.finrank_map_eq]; exact L.2.1.1, ?_⟩, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [LinearEquiv.coe_coe, hr]
      exact L.2.1.2 y hy
    · rw [← Submodule.map_comp, hcomp, Submodule.map_comp, L.2.2]
  have hbwd : ∀ L : {L' : Submodule K V' //
      L' ∈ singularSubspaces Q' k ∧ L'.map (g' : V' →ₗ[K] V') = L'},
      L.1.map (r.symm : V' →ₗ[K] V) ∈ singularSubspaces Q k ∧
        (L.1.map (r.symm : V' →ₗ[K] V)).map (g : V →ₗ[K] V) =
          L.1.map (r.symm : V' →ₗ[K] V) := by
    intro L
    refine ⟨⟨by rw [LinearEquiv.finrank_map_eq]; exact L.2.1.1, ?_⟩, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [LinearEquiv.coe_coe, hr']
      exact L.2.1.2 y hy
    · rw [← Submodule.map_comp, hcomp', Submodule.map_comp, L.2.2]
  symm
  exact Nat.card_congr
    { toFun := fun L => ⟨L.1.map (r : V →ₗ[K] V'), hfwd L⟩
      invFun := fun L => ⟨L.1.map (r.symm : V' →ₗ[K] V), hbwd L⟩
      left_inv := fun L => Subtype.ext (by
        change (L.1.map (r : V →ₗ[K] V')).map (r.symm : V' →ₗ[K] V) = L.1
        rw [← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id])
      right_inv := fun L => Subtype.ext (by
        change (L.1.map (r.symm : V' →ₗ[K] V)).map (r : V →ₗ[K] V') = L.1
        rw [← Submodule.map_comp, LinearEquiv.comp_symm, Submodule.map_id]) }

end Congr

section Stated

variable {n : ℕ} {K : Type} [Field K]

theorem conj_mk_smul_stabilizer (A : StatedOmega (StatedQuadPlus n K))
    (W : Submodule K (Fin n ⊕ Fin n → K)) :
    MulAut.conj (QuotientGroup.mk' _ A : StatedProj (StatedOmega (StatedQuadPlus n K))) •
        statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) W =
      statedProjectiveSubspaceStabilizer (StatedQuadPlus n K)
        (W.map (toLinEquiv _ K A.val).toLinearMap) := by
  rw [← statedProjectiveSubspaceAction_mk_apply]
  exact statedProjectiveSubspaceStabilizer_map_conj _ _ W

theorem statedPointFamily_eq_image :
    statedPointFamily (coe_quadPlus n K) =
      statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) ''
        singularSubspaces (quadPlus n K) 1 := by
  ext U
  constructor
  · rintro ⟨L, rfl⟩
    exact ⟨L.val, L.property, (statedPointStabilizer_eq_subspaceStabilizer L).symm⟩
  · rintro ⟨W, hW, rfl⟩
    exact ⟨⟨W, hW⟩, statedPointStabilizer_eq_subspaceStabilizer ⟨W, hW⟩⟩

theorem stabilizer_injOn_lines (hn : 3 ≤ n) :
    Set.InjOn (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K))
      (singularSubspaces (quadPlus n K) 1) := by
  intro W₁ h₁ W₂ h₂ h
  have h₁' : Module.finrank K W₁ = 1 ∧ ∀ x ∈ W₁, quadPlus n K x = 0 := h₁
  have h₂' : Module.finrank K W₂ = 1 ∧ ∀ x ∈ W₂, quadPlus n K x = 0 := h₂
  have hinj := (stated_intrinsic (K := K) hn).2.1
  have h' := @hinj ⟨W₁, h₁'⟩ ⟨W₂, h₂'⟩
    ((statedPointStabilizer_eq_subspaceStabilizer ⟨W₁, h₁'⟩).trans
      (h.trans (statedPointStabilizer_eq_subspaceStabilizer ⟨W₂, h₂'⟩).symm))
  exact congrArg Subtype.val h'

theorem stabilizer_injOn_maximal (hn : 3 ≤ n) :
    Set.InjOn (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K))
      (singularSubspaces (quadPlus n K) n) := by
  intro M₁ h₁ M₂ h₂ h
  have hD := congrArg (Subgroup.comap (QuotientGroup.mk'
    ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K))))) h
  rw [statedProjectiveSubspaceStabilizer_comap_mk,
    statedProjectiveSubspaceStabilizer_comap_mk] at hD
  have hE := congrArg (Subgroup.map (statedOmegaEquiv (coe_quadPlus n K)
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus hn)).toMonoidHom) hD
  rw [statedDerivedSubspaceStabilizer_map_elementary,
    statedDerivedSubspaceStabilizer_map_elementary] at hE
  have hdim : Module.finrank K (Fin n ⊕ Fin n → K) = 2 * Module.finrank K M₁ := by
    rw [h₁.1, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  exact (CatalogueBOrthogonalStabilizerRigidity.elementaryStabilizer_eq_iff
    (nondegenerate_polarBilin_quadPlus n K) h₁.2 hdim (by rw [h₁.1]; omega)
    (by rw [h₁.1, h₂.1])).mp hE

theorem conjugacyFamily_eq_image (hn : 3 ≤ n) (X₀ : Submodule K (Fin n ⊕ Fin n → K)) :
    conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) X₀) =
      statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) ''
        MulAction.orbit (orthElementaryGroup (quadPlus n K)) X₀ := by
  ext U
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact ⟨X₀.map (toLinEquiv _ K A.val).toLinearMap,
      mem_orbit_elementary.2 ⟨_, (plusDerivedEquiv n K hn A).property, rfl⟩,
      (conj_mk_smul_stabilizer A X₀).symm⟩
  · rintro ⟨M, hM, rfl⟩
    obtain ⟨a, ha, rfl⟩ := mem_orbit_elementary.1 hM
    refine ⟨QuotientGroup.mk' _ ((plusDerivedEquiv n K hn).symm ⟨a, ha⟩), ?_⟩
    change MulAut.conj (QuotientGroup.mk' _ ((plusDerivedEquiv n K hn).symm ⟨a, ha⟩) :
        StatedProj (StatedOmega (StatedQuadPlus n K))) •
      statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) X₀ = _
    rw [conj_mk_smul_stabilizer]
    have h := plusDerivedEquiv_val n K hn ((plusDerivedEquiv n K hn).symm ⟨a, ha⟩)
    rw [MulEquiv.apply_symm_apply] at h
    rw [← h]
    rfl

theorem map_mem_orbit (hn : 3 ≤ n) (A : StatedOmega (StatedQuadPlus n K))
    {X₀ M : Submodule K (Fin n ⊕ Fin n → K)}
    (hM : M ∈ MulAction.orbit (orthElementaryGroup (quadPlus n K)) X₀) :
    M.map (toLinEquiv _ K A.val).toLinearMap ∈
      MulAction.orbit (orthElementaryGroup (quadPlus n K)) X₀ := by
  obtain ⟨a, ha, rfl⟩ := mem_orbit_elementary.1 hM
  exact mem_orbit_elementary.2 ⟨toLinEquiv _ K A.val * a,
    mul_mem (plusDerivedEquiv n K hn A).property ha, mul_smul _ _ _⟩

theorem card_fixed_pointFamily (hn : 3 ≤ n) (A : StatedOmega (StatedQuadPlus n K)) :
    Nat.card {U // U ∈ statedPointFamily (coe_quadPlus n K) ∧
        MulAut.conj (QuotientGroup.mk' _ A : StatedProj (StatedOmega (StatedQuadPlus n K))) • U =
          U} =
      Nat.card {L : Submodule K (Fin n ⊕ Fin n → K) // L ∈ singularSubspaces (quadPlus n K) 1 ∧
        L.map (toLinEquiv _ K A.val).toLinearMap = L} := by
  rw [statedPointFamily_eq_image]
  exact card_fixed_image _ (stabilizer_injOn_lines hn) _ _
    (fun L hL => map_mem_singularSubspaces
      (orthElementaryGroup_le _ (plusDerivedEquiv n K hn A).property) hL)
    (fun L _ => conj_mk_smul_stabilizer A L)

theorem card_fixed_conjugacyFamily (hn : 3 ≤ n) (A : StatedOmega (StatedQuadPlus n K))
    {X₀ : Submodule K (Fin n ⊕ Fin n → K)} (hX₀ : X₀ ∈ singularSubspaces (quadPlus n K) n) :
    Nat.card {U // U ∈
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) X₀) ∧
        MulAut.conj (QuotientGroup.mk' _ A : StatedProj (StatedOmega (StatedQuadPlus n K))) • U =
          U} =
      Nat.card {M : Submodule K (Fin n ⊕ Fin n → K) //
        M ∈ MulAction.orbit (orthElementaryGroup (quadPlus n K)) X₀ ∧
          M.map (toLinEquiv _ K A.val).toLinearMap = M} := by
  rw [conjugacyFamily_eq_image hn]
  have hsub : MulAction.orbit (orthElementaryGroup (quadPlus n K)) X₀ ⊆
      singularSubspaces (quadPlus n K) n := by
    intro M hM
    obtain ⟨a, ha, rfl⟩ := mem_orbit_elementary.1 hM
    exact map_mem_singularSubspaces (orthElementaryGroup_le _ ha) hX₀
  exact card_fixed_image _ ((stabilizer_injOn_maximal hn).mono hsub) _ _
    (fun M hM => map_mem_orbit hn A hM) (fun M _ => conj_mk_smul_stabilizer A M)

theorem card_fixed_maximal [Finite K] (hn : 3 ≤ n)
    (g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) :
    Nat.card {M // M ∈ MulAction.orbit (orthElementaryGroup (quadPlus n K)) (flag n K n) ∧
        M.map (g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) = M} +
      Nat.card {M // M ∈ MulAction.orbit (orthElementaryGroup (quadPlus n K))
          (Xstar n K (by omega)) ∧
        M.map (g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) = M} =
      Nat.card {M // M ∈ singularSubspaces (quadPlus n K) n ∧
        M.map (g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) = M} := by
  obtain ⟨-, -, hsX, hsXs, hcover, hdisj, -⟩ :=
    orthogonal_geometry_split_maximal_family_orbits (K := K) hn
  have e1 : ∀ S : Set (Submodule K (Fin n ⊕ Fin n → K)),
      Nat.card {M // M ∈ S ∧ M.map (g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) = M} =
        ({M | M ∈ S ∧ M.map (g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) = M} :
          Set _).ncard :=
    fun S => Nat.card_coe_set_eq _
  have hd : Disjoint
      ({M | M ∈ MulAction.orbit (orthElementaryGroup (quadPlus n K)) (flag n K n) ∧
        M.map (g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) = M} : Set _)
      {M | M ∈ MulAction.orbit (orthElementaryGroup (quadPlus n K)) (Xstar n K (by omega)) ∧
        M.map (g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) = M} :=
    Set.disjoint_left.2 fun M h1 h2 => Set.disjoint_left.1 hdisj h1.1 h2.1
  rw [e1, e1, e1, ← Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)]
  congr 1
  ext M
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨hsX h1, h2⟩
    · exact ⟨hsXs h1, h2⟩
  · rintro ⟨h1, h2⟩
    rcases hcover M h1 with h | h
    · exact Or.inl ⟨h, h2⟩
    · exact Or.inr ⟨h, h2⟩

theorem stated_smul_pointFamily_eq [Finite K] (A : StatedOmega (StatedQuadPlus 4 K))
    (η : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) (hη : orderOf η = 3)
    (hc : η * MulAut.conj (QuotientGroup.mk' _ A : StatedProj (StatedOmega (StatedQuadPlus 4 K))) =
      MulAut.conj (QuotientGroup.mk' _ A : StatedProj (StatedOmega (StatedQuadPlus 4 K))) * η)
    (hm : Nat.card {M : Submodule K (Fin 4 ⊕ Fin 4 → K) //
        M ∈ singularSubspaces (quadPlus 4 K) 4 ∧ M.map (toLinEquiv _ K A.val).toLinearMap = M} ≠
      2 * Nat.card {L : Submodule K (Fin 4 ⊕ Fin 4 → K) //
        L ∈ singularSubspaces (quadPlus 4 K) 1 ∧ L.map (toLinEquiv _ K A.val).toLinearMap = L}) :
    η • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  have hO := stated_pointFamily_orbit_subset (K := K) (n := 4) rfl
  obtain ⟨hX, hXs, -⟩ := orthogonal_geometry_split_maximal_family_orbits (K := K) (r := 4)
    (by norm_num)
  have hη3 : η ^ 3 = 1 := by
    rw [← hη]
    exact pow_orderOf_eq_one η
  refine smul_eq_of_fixed_counts hη3 hc (hO (MulAction.mem_orbit _ η))
    (hO (MulAction.mem_orbit _ (η * η))) ?_
  rw [card_fixed_conjugacyFamily (by norm_num) A hX, card_fixed_conjugacyFamily (by norm_num) A hXs,
    card_fixed_maximal (by norm_num), card_fixed_pointFamily (by norm_num)]
  exact hm

end Stated

@[expose] def D4ThreeFamilyObstruction (G : Type) [Group G] (p f : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
    ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)),
      projectivePointFamilyAut (coordinateQuadPlus 4 K) =
          matrixProjectiveImage (coordinateQuadPlus 4 K) ∧
      ∀ (g : matrixDerived (coordinateQuadPlus 4 K))
        (η : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))), orderOf η = 3 →
        η * MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) * η⁻¹ =
          MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) →
        Nat.card {M : Submodule K (Fin (2 * 4) → K) //
            M ∈ singularSubspaces (coordinateQuadPlus 4 K) 4 ∧
              M.map (matrixLinearEquiv g.val : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)) =
                M} ≠
          2 * Nat.card {L : Submodule K (Fin (2 * 4) → K) //
            L ∈ singularSubspaces (coordinateQuadPlus 4 K) 1 ∧
              L.map (matrixLinearEquiv g.val : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)) =
                L} →
        η ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K) ∧
          η ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)

theorem d4ThreeFamilyObstruction (G : Type) [Group G] {p f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 p f) : D4ThreeFamilyObstruction G p f := by
  intro K _ _ hK e
  have himage := CatalogueBOrthogonalPointData.coordinate_plus_family_eq_matrixImage h K hK e
  refine ⟨himage, fun g η hη hc hm => ?_⟩
  obtain ⟨A, rfl⟩ :=
    (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).surjective g
  set ψ := plusCoordinateEquiv 4 K with hψ
  have hψA : ψ (QuotientGroup.mk' _ A) = matrixProjectiveProjection (coordinateQuadPlus 4 K)
      (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A) :=
    statedProjectiveReindexEquiv_mk (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A
  have hconj : MulAut.congr ψ (MulAut.conj (QuotientGroup.mk' _ A)) =
      MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
        (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) := by
    rw [automorphismTransport_conj, hψA]
  set η' := (MulAut.congr ψ).symm η with hη'
  have hηη' : MulAut.congr ψ η' = η := MulEquiv.apply_symm_apply _ _
  have hη'3 : orderOf η' = 3 := by
    rw [hη', MulEquiv.orderOf_eq, hη]
  have hc' : η' * MulAut.conj (QuotientGroup.mk' _ A) =
      MulAut.conj (QuotientGroup.mk' _ A) * η' := by
    apply (MulAut.congr ψ).injective
    rw [map_mul, map_mul, hηη', hconj]
    exact mul_inv_eq_iff_eq_mul.mp hc
  have hvec : ∀ x, matrixLinearEquiv
      (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A).val
        (reindexVectorEquiv (plusIndexEquiv 4) x) =
      reindexVectorEquiv (plusIndexEquiv 4) (toLinEquiv _ K A.val x) :=
    statedDerivedReindexEquiv_vector (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A
  have hr : ∀ x, coordinateQuadPlus 4 K (reindexVectorEquiv (plusIndexEquiv 4) x) =
      quadPlus 4 K x := reindexQuadraticForm_map (plusIndexEquiv 4) (quadPlus 4 K)
  rw [card_invariant_singular_congr _ hr hvec, card_invariant_singular_congr _ hr hvec] at hm
  have hfix := stated_smul_pointFamily_eq A η' hη'3 hc' hm
  have hmem := CatalogueBOrthogonalInvolutionConjugacy.congr_mem_pointFamilyAut η' hfix
  rw [hηη'] at hmem
  exact ⟨hmem, himage ▸ hmem⟩

end ThreeFamily

open ThreeFamily in
theorem d4_three_family_fixed_count_obstruction (G : Type) [Group G] (f : ℕ)
    (h : StatedClassicalModel G .POmegaPlus 4 2 f) : D4ThreeFamilyObstruction G 2 f :=
  d4ThreeFamilyObstruction G h

end CFSG.ComponentClassification.UnbalancedCatalog
