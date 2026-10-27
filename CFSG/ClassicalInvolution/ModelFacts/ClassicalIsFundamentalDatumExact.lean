module

public import CFSG.LieType.AlgebraicGroups.ToralTwistSemilinearDatum

public noncomputable section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_datum_mulEquiv_exact (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j) {r : ℕ}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ} {ω : WeylGroup τ}
    (hθ : ThetaProperties ρ r χ ω) {Q₀ : ModGL τ k}
    (hQ₀ : ∀ γ, IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      Q₀ * pinnedX τ k γ c * Q₀⁻¹ = pinnedX τ k (thetaMap ω ρ γ) (μ * c))
    (hQ₀T : Q₀ ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hQ₀G : (adjointGroup τ k).map (MulAut.conj Q₀).toMonoidHom = adjointGroup τ k)
    (hpin : IsTwistPinningNormalization τ k p e χ (thetaMap ω ρ) Q₀)
    (hne : (kernelRoots χ).Nonempty) :
    ∃ D : OrthogonalSemilinearFixedRootDatum τ p k, D.χ = χ ∧ D.e = e ∧
      Nonempty (D.totalFixedGroup ≃* fixedPointsIn
        (torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)) (frobTwistGL τ k p e Q₀)) := by
  classical
  obtain ⟨h, hhT, hpinΔ, -, -, -, -, u, -, hconj⟩ := hpin
  set θZ := thetaMap ω ρ with hθZ
  set c := h * Q₀ with hc_def
  set M := torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) with hM_def
  have hMG : M ≤ adjointGroup τ k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  have hcX : ∀ γ, IsRoot τ γ → ∃ μ : kˣ, ∀ z : k,
      c * pinnedX τ k γ z * c⁻¹ = pinnedX τ k (θZ γ) (μ * z) := by
    intro γ hγ
    obtain ⟨μ, hμ⟩ := hQ₀ γ hγ
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
    refine ⟨rootChar a (θZ γ) * μ, fun z => ?_⟩
    calc c * pinnedX τ k γ z * c⁻¹ = h * (Q₀ * pinnedX τ k γ z * Q₀⁻¹) * h⁻¹ := by
          rw [hc_def]
          group
      _ = _ := by
        rw [hμ, ha, rootDiagUnit_conj_pinnedX a (isRoot_thetaMap hA hγ), Units.val_mul,
          mul_assoc]
  have hcT : c ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)) :=
    mul_mem (Subgroup.le_normalizer hhT) hQ₀T
  have hcG : (adjointGroup τ k).map (MulAut.conj c).toMonoidHom = adjointGroup τ k := by
    have e1 : (MulAut.conj c).toMonoidHom =
        (MulAut.conj h).toMonoidHom.comp (MulAut.conj Q₀).toMonoidHom := by
      ext y
      simp only [hc_def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.comp_apply,
        mul_inv_rev]
      group
    rw [e1, ← Subgroup.map_map, hQ₀G]
    exact map_conj_eq_of_mem_normalizer
      (Subgroup.le_normalizer (torusGroup_le_adjointGroup hhT))
  obtain ⟨S, hS⟩ := ((exceptional_Lang_root_coordinate_surjectivity p k).1 τ e he).1
  let C : MulAut (adjointGroup τ k) := ((adjointGroup τ k).equivMapOfInjective
    (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hcG)
  let F : MulAut (adjointGroup τ k) := S.trans C
  have hF : ∀ x : adjointGroup τ k, (F x : ModGL τ k) = frobTwistGL τ k p e c x := by
    intro x
    rw [frobTwistGL_apply]
    change _ = c * Units.map (entrywiseHom (iterateFrobenius k p e)) (x : ModGL τ k) * c⁻¹
    rw [← hS x]
    rfl
  set θR := latticeRealExt (thetaHom ω ρ) with hθR_def
  have hθR : ∀ v, θR (toReal v) = toReal (θZ v) := fun v => latticeRealExt_toReal _ v
  have horbit : ∀ α, thetaOrbit θR α = iterOrbit θZ α := by
    intro α
    ext β
    constructor
    · rintro ⟨m, hm⟩
      rw [latticeRealExt_pow_toReal] at hm
      exact ⟨m, toReal_injective hm⟩
    · rintro ⟨m, rfl⟩
      exact ⟨m, latticeRealExt_pow_toReal _ m α⟩
  have hle : orbitReflectionGroup θZ (simpleUnion χ) ≤ Subgroup.closure
      ((fun β => setReflection (thetaOrbit θR β)) '' unionSimpleRoots χ Set.univ) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, O, hO, rfl⟩
    refine Subgroup.subset_closure ⟨β, (simpleUnion_eq_unionSimpleRoots χ) ▸ hβ, ?_⟩
    change setReflection (thetaOrbit θR β) = orbitReflection O
    rw [horbit, ← hO, orbitReflection]
    exact setReflection_eq_list_prod O.finite_toSet
      (fun x hx y hy _ => hθ.commute_rootReflection β hβ x (hO ▸ hx) y (hO ▸ hy))
      (Finset.nodup_toList O) fun γ => Finset.mem_toList.trans Finset.mem_coe.symm
  obtain ⟨α₀, hα₀⟩ := hne
  let D : OrthogonalSemilinearFixedRootDatum τ p k :=
    { tag_mem := hτ
      odd := hp
      isAlgebraic := hk
      e := e
      one_le_e := he
      χ := χ
      θ := θR
      isometry := latticeRealExt_isometry _ (iform_thetaMap hB)
      bijOn_kernelRoots := bijOn_latticeRealExt thetaMap_injective hθ.image_kernelRoots
      bijOn_simpleRoots := bijOn_latticeRealExt thetaMap_injective
        (by rw [← simpleUnion_eq_unionSimpleRoots]; exact hθ.image_simpleUnion)
      orbit_orthogonal := fun α hα β hβ γ hγ hβγ => by
        rw [horbit] at hβ hγ
        rw [← dotProduct_mulVec_eq_iform]
        exact hθ.pairwise_iterOrbit α hα hβ hγ hβγ
      orbit_reflection := fun α hα => by
        obtain ⟨g, hg, β, hβ, himg⟩ := hθ.exists_image_iterOrbit α hα
        refine ⟨g, hle hg, β, (simpleUnion_eq_unionSimpleRoots χ) ▸ hβ, ?_⟩
        rw [horbit, horbit]
        exact himg
      F := F
      map_torusGroup := map_subgroupOf_adjointGroup hF torusGroup_le_adjointGroup
        (map_frobTwistGL_torusGroup p e hcT)
      map_rootSubgroup := fun α hα α' hα' => by
        have hα'' : α' = θZ α := toReal_injective (hα'.symm.trans (hθR α))
        subst hα''
        exact map_subgroupOf_adjointGroup hF (rootSubgroup_le_adjointGroup α)
          (map_frobTwistGL_rootSubgroup_of_conj p e hcX hα.1)
      map_rootSL2 := fun β hβ β' hβ' A x hx => by
        have hβ'' : β' = θZ β := toReal_injective (hβ'.symm.trans (hθR β))
        subst hβ''
        rw [hF, hx]
        exact hpinΔ β hβ A
      J := {i | ∃ m : ℕ, ∃ α ∈ componentRoots χ ⟦⟨α₀, hα₀⟩⟧, ∃ β ∈ componentRoots χ i,
        (θR ^ m) (toReal α) = toReal β}
      isThetaOrbit := ⟨⟦⟨α₀, hα₀⟩⟧, rfl⟩ }
  have hX : D.totalFixedGroup.map (adjointGroup τ k).subtype =
      fixedPointsIn M (frobTwistGL τ k p e c) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxM, hxF⟩ := D.mem_totalFixedGroup.1 hx
      refine mem_fixedPointsIn.2 ⟨hxM, ?_⟩
      change frobTwistGL τ k p e c (x : ModGL τ k) = x
      rw [← hF x]
      exact congrArg Subtype.val hxF
    · intro hy
      obtain ⟨hyM, hyF⟩ := mem_fixedPointsIn.1 hy
      refine ⟨⟨y, hMG hyM⟩, D.mem_totalFixedGroup.2 ⟨hyM, Subtype.ext ?_⟩, rfl⟩
      change (F ⟨y, hMG hyM⟩ : ModGL τ k) = y
      rw [hF]
      exact hyF
  exact ⟨D, rfl, rfl, ⟨((D.totalFixedGroup.equivMapOfInjective _
    (adjointGroup τ k).subtype_injective).trans (MulEquiv.subgroupCongr hX)).trans
      (((fixedPointsIn M (frobTwistGL τ k p e c)).equivMapOfInjective _
        (MulAut.conj u).injective).trans (MulEquiv.subgroupCongr hconj))⟩⟩


end CFSG.ClassicalInvolution.ModelFacts
