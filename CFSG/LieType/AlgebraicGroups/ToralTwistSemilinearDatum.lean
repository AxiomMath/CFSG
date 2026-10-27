module

public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear
public import CFSG.LieType.AlgebraicGroups.RootCoordinateLang
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedTotalComponents

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section RealExtension

variable {τ : Tag}

@[expose] def latticeRealExt (f : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) :
    (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ) :=
  Matrix.toLin' (Matrix.of fun i j => ((f (Pi.single j 1) i : ℤ) : ℝ))

theorem sum_smul_single_eq (v : Fin τ.rank → ℤ) :
    ∑ j, v j • (Pi.single j 1 : Fin τ.rank → ℤ) = v := by
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem latticeRealExt_toReal (f : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (v : Fin τ.rank → ℤ) :
    latticeRealExt f (toReal v) = toReal (f v) := by
  have hv : f v = ∑ j, v j • f (Pi.single j 1) := by
    conv_lhs => rw [← sum_smul_single_eq v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_zsmul f (v j) _
  ext i
  rw [hv]
  simp only [latticeRealExt, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
    toReal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem latticeRealExt_pow_toReal (f : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) (m : ℕ)
    (v : Fin τ.rank → ℤ) : (latticeRealExt f ^ m) (toReal v) = toReal (f^[m] v) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, latticeRealExt_toReal,
      Function.iterate_succ_apply']

theorem eq_sum_smul_toReal_single (x : Fin τ.rank → ℝ) :
    x = ∑ i, x i • toReal (Pi.single i 1 : Fin τ.rank → ℤ) := by
  ext j
  simp [toReal, Pi.single_apply, Finset.sum_apply]

theorem latticeRealExt_isometry (f : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    (hf : ∀ u v, iform (f u) (f v) = iform u v) (x y : Fin τ.rank → ℝ) :
    rform (latticeRealExt f x) (latticeRealExt f y) = rform x y := by
  have hA : ∀ z : Fin τ.rank → ℝ,
      latticeRealExt f z = ∑ i, z i • toReal (f (Pi.single i 1)) := by
    intro z
    conv_lhs => rw [eq_sum_smul_toReal_single z]
    simp only [map_sum, map_smul, latticeRealExt_toReal]
  have hxy : rform x y = ∑ i, ∑ j, x i * y j *
      rform (toReal (Pi.single i 1 : Fin τ.rank → ℤ)) (toReal (Pi.single j 1)) := by
    conv_lhs => rw [eq_sum_smul_toReal_single x, eq_sum_smul_toReal_single y]
    exact rform_sum_sum _ _ _ _ _ _
  rw [hA, hA, rform_sum_sum, hxy]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [rform_toReal, rform_toReal, hf]

theorem bijOn_latticeRealExt {f : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)}
    (hf : Function.Injective f) {S : Set (Fin τ.rank → ℤ)} (hS : f '' S = S) :
    Set.BijOn (latticeRealExt f) (toReal '' S) (toReal '' S) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨α, hα, rfl⟩
    refine ⟨f α, ?_, (latticeRealExt_toReal f α).symm⟩
    rw [← hS]
    exact ⟨α, hα, rfl⟩
  · rintro _ ⟨α, -, rfl⟩ _ ⟨β, -, rfl⟩ h
    rw [latticeRealExt_toReal, latticeRealExt_toReal] at h
    rw [hf (toReal_injective h)]
  · rintro _ ⟨β, hβ, rfl⟩
    rw [← hS] at hβ
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨toReal α, ⟨α, hα, rfl⟩, latticeRealExt_toReal f α⟩

@[expose] def thetaHom
    (ω : WeylGroup τ) (ρ : Equiv.Perm (Fin τ.rank)) :
    (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) where
  toFun := thetaMap ω ρ
  map_zero' := by
    change ω • permLattice ρ 0 = 0
    rw [show permLattice ρ (0 : Fin τ.rank → ℤ) = 0 from rfl, smul_zero]
  map_add' := thetaMap_add

end RealExtension

section Groups

variable {τ : Tag} {k : Type} [Field k]

theorem torusGroup_le_adjointGroup
    : torusGroup τ k ≤ adjointGroup τ k :=
  (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2

theorem map_subgroupOf_adjointGroup {F : MulAut (adjointGroup τ k)} {f : ModGL τ k →* ModGL τ k}
    (hF : ∀ x : adjointGroup τ k, (F x : ModGL τ k) = f x) {K K' : Subgroup (ModGL τ k)}
    (hK : K ≤ adjointGroup τ k) (h : K.map f = K') :
    (K.subgroupOf (adjointGroup τ k)).map F.toMonoidHom = K'.subgroupOf (adjointGroup τ k) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, hF, ← h]
    exact ⟨y, hy, rfl⟩
  · intro hx
    rw [Subgroup.mem_subgroupOf, ← h] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    refine ⟨⟨z, hK hz⟩, hz, Subtype.ext ?_⟩
    rw [MulEquiv.coe_toMonoidHom, hF]
    exact hzx

theorem not_isPComponent_of_kernelRoots_eq_empty
    {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ}
    (hK : kernelRoots χ = ∅) {Y : Subgroup (ModGL τ k)}
    (hY : Y ≤ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)) {ℓ : ℕ} (L : Subgroup Y) :
    ¬ CFSG.IsPComponent ℓ L := by
  intro hL
  have := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_nontrivial hL
  have := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hL
  rw [hK, rootSpan, iSup_emptyset, sup_bot_eq] at hY
  exact Group.IsPerfect.not_isMulCommutative L ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup (hY a.1.2))
      (torusGroup_le_diagonalGroup (hY b.1.2))))⟩⟩

end Groups

section Datum

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_datum_mulEquiv
    (hp : p ≠ 2)
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
    ∃ D : OrthogonalSemilinearFixedRootDatum τ p k, D.χ = χ ∧
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
  exact ⟨D, rfl, ⟨((D.totalFixedGroup.equivMapOfInjective _
    (adjointGroup τ k).subtype_injective).trans (MulEquiv.subgroupCongr hX)).trans
      (((fixedPointsIn M (frobTwistGL τ k p e c)).equivMapOfInjective _
        (MulAut.conj u).injective).trans (MulEquiv.subgroupCongr hconj))⟩⟩

end Datum

end CFSG.LieType.AlgebraicGroups
