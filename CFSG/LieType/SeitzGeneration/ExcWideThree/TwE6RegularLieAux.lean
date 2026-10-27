module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieConj

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

section Aux

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise


theorem twE6_fixed_decomp {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {h : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hA : h ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr h = h) :
    ∃ u ∈ twistedE6RootGroup K σ, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      h = baseChangeGL (algebraMap K (AlgebraicClosure K)) u * t := by
  obtain ⟨-, hmul, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order (ℓ := ℓ) (f := f) hℓ hf K
      hK σ.toRingHom hσ (AlgebraicClosure K) Fr hFr
  have hinv : h⁻¹ ∈ twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr :=
    Subgroup.inv_mem _ ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K)
      Fr).2 ⟨hA, hF⟩)
  have hmem : h⁻¹ ∈
      (graphFixedTorus TwistTag.E6 (AlgebraicClosure K) Fr :
        Set (ModGL TwistTag.E6.tag (AlgebraicClosure K))) *
      ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
        (baseChangeGL (algebraMap K (AlgebraicClosure K))) :
        Set (ModGL TwistTag.E6.tag (AlgebraicClosure K))) := by
    rw [← hmul]
    exact hinv
  obtain ⟨t, ht, c', hc', hx⟩ := hmem
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hc'
  refine ⟨u⁻¹, Subgroup.inv_mem _ hu, t⁻¹, Subgroup.inv_mem _ (Subgroup.mem_inf.1 ht).1, ?_⟩
  have hx' : t * baseChangeGL (algebraMap K (AlgebraicClosure K)) u = h⁻¹ := hx
  have : h = (t * baseChangeGL (algebraMap K (AlgebraicClosure K)) u)⁻¹ := by
    rw [hx', inv_inv]
  rw [this, mul_inv_rev, map_inv]

theorem rootSpan_le_centralizer_rootDiagUnit {L : Type} [Field L]
    (a : Fin TwistTag.E6.tag.rank → Lˣ) {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot TwistTag.E6.tag α ∧ rootChar a α = 1) :
    rootSpan TwistTag.E6.tag L S ≤
      Subgroup.centralizer ({rootDiagUnit TwistTag.E6.tag a} : Set (ModGL TwistTag.E6.tag L)) := by
  refine iSup₂_le fun α hα => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.1 hh]
  have := rootDiagUnit_conj_pinnedX a (hS α hα).1 c
  rw [(hS α hα).2] at this
  simp only [Units.val_one, one_mul] at this
  exact mul_inv_eq_iff_eq_mul.1 this

theorem torus_sup_rootSpan_le_centralizer_rootDiagUnit {L : Type} [Field L] [IsAlgClosed L]
    (a : Fin TwistTag.E6.tag.rank → Lˣ) {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot TwistTag.E6.tag α ∧ rootChar a α = 1) :
    torusGroup TwistTag.E6.tag L ⊔ rootSpan TwistTag.E6.tag L S ≤
      Subgroup.centralizer ({rootDiagUnit TwistTag.E6.tag a} : Set (ModGL TwistTag.E6.tag L)) := by
  refine sup_le ?_ (rootSpan_le_centralizer_rootDiagUnit a hS)
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.1 hh]
  exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup (rootDiagUnit_mem_torusGroup a))
    (torusGroup_le_diagonalGroup ht)

theorem psi_pinnedX {L : Type} [Field L] (Fr : L →+* L) (u : WeylGroup TwistTag.E6.tag)
    {α β : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hαβ : u • permLattice TwistTag.E6.perm α = β) :
    ∃ a : L, a ≠ 0 ∧ ∀ c : L,
      canonicalRep (coxeterSystem TwistTag.E6.tag) L u *
          twistHom TwistTag.E6 L Fr (pinnedX TwistTag.E6.tag L α c) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) L u)⁻¹ =
        pinnedX TwistTag.E6.tag L β (a * Fr c) := by
  obtain ⟨ε, hε, hεc⟩ := diagramMap_conj_pinnedX (K := L) TwistTag.E6 hα
  have hρ : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm α) :=
    hα.permLattice TwistTag.E6.cartan_perm
  obtain ⟨ε', hε', hε'c⟩ := exists_canonicalRep_mul_pinnedX_mul_inv (τ := TwistTag.E6.tag) L u hρ
  refine ⟨ε' * ε, ?_, fun c => ?_⟩
  · intro h0
    have : ε' * ε * (ε' * ε) = 1 := by linear_combination (ε' * ε') * hε + hε'
    rw [h0] at this
    simp at this
  · have h1 : twistHom TwistTag.E6 L Fr (pinnedX TwistTag.E6.tag L α c) =
        diagramMap TwistTag.E6 L * Units.map (entrywiseHom Fr) (pinnedX TwistTag.E6.tag L α c) *
          (diagramMap TwistTag.E6 L)⁻¹ := rfl
    have h2 : Units.map (entrywiseHom Fr) (pinnedX TwistTag.E6.tag L α c) =
        pinnedX TwistTag.E6.tag L α (Fr c) := Units.ext (entrywise_pinnedX Fr α c)
    rw [h1, h2, hεc, hε'c, hαβ, mul_assoc]

theorem torus_sup_rootSpan_parabolicRoots_le_normalizer_radical {L : Type} [Field L]
    (J : Set (Fin TwistTag.E6.tag.rank)) :
    torusGroup TwistTag.E6.tag L ⊔ rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag J) ≤
      Subgroup.normalizer (parabolicRadical TwistTag.E6.tag L J : Set (ModGL TwistTag.E6.tag L)) := by
  refine le_trans ?_ (parabolicSubgroup_le_normalizer_parabolicRadical J)
  refine sup_le (torusGroup_le_parabolicSubgroup J) (iSup₂_le fun γ hγ => ?_)
  exact (CFSG.RankThree.PartOne.D4RC.rcp_rootSubgroup_le_parabolicLevi hγ).trans
    (parabolicLevi_le_parabolicSubgroup J)

theorem torus_sup_rootSpan_levi_le_normalizer_rootSubgroup {L : Type} [Field L] :
    torusGroup TwistTag.E6.tag L ⊔
        rootSpan TwistTag.E6.tag L (parabolicRoots TwistTag.E6.tag e6LeviNodes) ≤
      Subgroup.normalizer
        (rootSubgroup TwistTag.E6.tag L e6HighestRoot : Set (ModGL TwistTag.E6.tag L)) := by
  refine sup_le (torusGroup_le_normalizer_rootSubgroup isRoot_e6HighestRoot) ?_
  have hcomm := rootSpan_commute_of_orth (τ := TwistTag.E6.tag) (L := L) (Or.inr (Or.inl rfl))
    (S₁ := parabolicRoots TwistTag.E6.tag e6LeviNodes)
    (S₂ := ({e6HighestRoot} : Set (Fin TwistTag.E6.tag.rank → ℤ)))
    (fun r hr => (mem_parabolicRoots_e6LeviNodes.1 hr).1)
    (by
      rintro r rfl
      exact isRoot_e6HighestRoot)
    (by
      intro α hα β hβ
      rw [dotProduct_mulVec_eq_iform, Set.mem_singleton_iff.1 hβ, iform_comm, iform_e6HighestRoot]
      exact (mem_parabolicRoots_e6LeviNodes.1 hα).2)
  intro x hx
  have hxc : x ∈ Subgroup.centralizer
      (rootSubgroup TwistTag.E6.tag L e6HighestRoot : Set (ModGL TwistTag.E6.tag L)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ rootSpan TwistTag.E6.tag L ({e6HighestRoot} : Set (Fin TwistTag.E6.tag.rank → ℤ)) := by
      rw [rootSpan_singleton]
      exact hy
    exact (hcomm x hx y hy').symm
  exact (Subgroup.centralizer_le_normalizer _) hxc

theorem rootSpan_le_adjoint_E6 {L : Type} [Field L] (S : Set (Fin TwistTag.E6.tag.rank → ℤ)) :
    rootSpan TwistTag.E6.tag L S ≤ adjointGroup TwistTag.E6.tag L :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem torusGroup_le_adjoint_E6 {L : Type} [Field L] :
    torusGroup TwistTag.E6.tag L ≤ adjointGroup TwistTag.E6.tag L :=
  (torus_le_familyGroup (fun (_ : Unit) (_ : Fin TwistTag.E6.tag.rank) => (1 : Lˣ))).trans
    (familyGroup_le_adjoint _)

end Aux

end CFSG.LieType.SeitzGeneration.ExcWideThree
