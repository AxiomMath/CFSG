module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddDatum
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddLattice
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionFixedComponents

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

section Datum

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_datum_mulEquiv_orbits (hp : p ≠ 2)
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
      (∀ β ∈ kernelRoots χ, (thetaOrbit D.θ β).ncard = 1 ∨ (thetaOrbit D.θ β).ncard = r) ∧
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
  refine ⟨D, rfl, fun β hβ => ?_, ⟨((D.totalFixedGroup.equivMapOfInjective _
    (adjointGroup τ k).subtype_injective).trans (MulEquiv.subgroupCongr hX)).trans
      (((fixedPointsIn M (frobTwistGL τ k p e c)).equivMapOfInjective _
        (MulAut.conj u).injective).trans (MulEquiv.subgroupCongr hconj))⟩⟩
  change (thetaOrbit θR β).ncard = 1 ∨ (thetaOrbit θR β).ncard = r
  rw [horbit]
  exact hθ.ncard_iterOrbit β hβ

end Datum

section Single

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem orbitPairing'_eq_iform {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (δ : Fin τ.rank → ℤ) :
    orbitPairing' D O δ = iform (∑ j ∈ Finset.range (orbitCard O), D.orbitVec O j) δ := by
  rw [orbitPairing', iform_finset_sum_left]
  exact Finset.sum_congr rfl fun j _ => corootPair_eq_iform' D (D.isRoot_orbitVec hO j) δ

theorem iform_orbitSum_self {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    iform (∑ j ∈ Finset.range (orbitCard O), D.orbitVec O j)
      (∑ j ∈ Finset.range (orbitCard O), D.orbitVec O j) = 2 * orbitCard O := by
  rw [iform_finset_sum_left]
  have h : ∀ j ∈ Finset.range (orbitCard O),
      iform (D.orbitVec O j) (∑ j ∈ Finset.range (orbitCard O), D.orbitVec O j) = 2 := by
    intro j hj
    rw [iform_finset_sum_right, Finset.sum_eq_single j]
    · rw [iform_orbitVec_eq' D hO (Finset.mem_range.1 hj) (Finset.mem_range.1 hj)]
      simp
    · intro j' hj' hne
      rw [iform_orbitVec_eq' D hO (Finset.mem_range.1 hj) (Finset.mem_range.1 hj')]
      simp [Ne.symm hne]
    · intro h
      exact absurd hj h
  rw [Finset.sum_congr rfl h]
  simp [mul_comm]

theorem orbitMap_neg_one_ne_one {r₀ : ℕ} (hr₀ : ((τ = .E6 ∨ τ = .E7) ∧ r₀ = 2) ∨
      (τ = .D4 ∧ r₀ = 3)) {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hcard : orbitCard O = 1 ∨ orbitCard O = r₀) : D.orbitMap O (-1) ≠ 1 := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero D.ringChar_ne_two
  have hF : ringChar (D.orbitField O) ≠ 2 := ringChar_subfield_ne_two D.ringChar_ne_two _
  rcases hcard with h1 | hr
  · intro h
    have h' : D.orbitMap O (-1) = D.orbitMap O 1 := by rw [h, D.orbitMap_one]
    exact neg_one_ne_one_sl2 hF (orbitMap_injective_of_orbitCard_eq_one' D h1 h')
  have hodd : ∃ i, Odd (iform (∑ j ∈ Finset.range (orbitCard O), D.orbitVec O j)
      (Pi.single i 1)) := by
    have hss := iform_orbitSum_self D hO
    rcases hr₀ with ⟨hτ, rfl⟩ | ⟨rfl, rfl⟩
    · exact exists_odd_iform_single_four hτ (by rw [hss, hr]; norm_num)
    · exact exists_odd_iform_single_six (by rw [hss, hr]; norm_num)
  obtain ⟨i, hi⟩ := hodd
  intro h
  have hact := orbitMap_neg_one_act' D hO (isRoot_single τ i)
  rw [orbitPairing'_eq_iform D hO, hi.neg_one_zpow, h] at hact
  simp only [Units.val_one, Module.End.one_apply, Units.val_neg] at hact
  have hne : rootVec τ k (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single τ i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  apply hne
  have h3 : (2 : k) • rootVec τ k (Pi.single i 1) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hact]
    simp
  exact (smul_eq_zero.1 h3).resolve_left h2

end Single

section Main

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem not_smallType_of_isFiniteToralTwistReduction (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j) {r₀ : ℕ}
    (hr₀ : ((τ = .E6 ∨ τ = .E7) ∧ r₀ = 2) ∨ (τ = .D4 ∧ r₀ = 3))
    {reps : List (SignRep τ)}
    (htheta : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      ThetaProperties ρ r₀ (signMaskChar τ m.mask) (ToralSign.wordElt τ l))
    {D : ModGL τ k}
    (hDX : ∀ (l : List (Fin τ.rank)) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      (wordWeylMatrix τ k l * D) * pinnedX τ k γ c * (wordWeylMatrix τ k l * D)⁻¹ =
        pinnedX τ k (thetaMap (ToralSign.wordElt τ l) ρ γ) (μ * c))
    (hDT : D ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hDG : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k)
    (hpin : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      IsTwistPinningNormalization τ k p e (signMaskChar τ m.mask)
        (thetaMap (ToralSign.wordElt τ l) ρ) (wordWeylMatrix τ k l * D))
    (hRfin : Finite (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)))
    {x : ModGL τ k} (hred : IsFiniteToralTwistReduction τ k p e D reps x)
    {L : Subgroup (ModGL τ k)}
    (hL : Assembly.IsComponentOf L (⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x})) :
    ¬ SmallType L := by
  classical
  obtain ⟨r, hr, l, hl, -, hQfin, g₁, -, hcomp⟩ := hred
  set R := fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D) with hR
  set Y := ⁅R, R⁆ ⊓ Subgroup.centralizer {x} with hY
  have hYR : Y ≤ R := fun y hy => Subgroup.commutator_le_self _ hy.1
  have : Finite Y := Finite.of_injective _ (Subgroup.inclusion_injective hYR)
  have hL2 := isPComponent_two_subgroupOf hL
  obtain ⟨hL₁, hL₁c⟩ := ((hcomp 2 Nat.prime_two).1 L).1 ⟨hL.1, hL2⟩
  set χ := signMaskChar τ r.mask with hχdef
  rcases (kernelRoots χ).eq_empty_or_nonempty with hK | hK
  · exact absurd hL₁c (not_isPComponent_of_kernelRoots_eq_empty hK inf_le_left _)
  obtain ⟨Dd, hχ, hsize, ⟨eqv⟩⟩ := exists_datum_mulEquiv_orbits p hp hk he hτ hA hB
    (htheta r hr l hl) (hDX l) (mul_mem (wordWeylMatrix_mem_normalizer l) hDT)
    (map_conj_wordWeylMatrix_mul l hDG) (hpin r hr l hl) hK
  have hX : Finite Dd.totalFixedGroup := Finite.of_equiv _ eqv.symm.toEquiv
  set Q := fixedPointsIn (torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ))
    (frobTwistGL τ k p e (wordWeylMatrix τ k l * D)) with hQ
  set L' := L.map (MulAut.conj g₁).toMonoidHom with hL'
  set J : Subgroup Q := L'.subgroupOf Q with hJ
  set J₁ : Subgroup Dd.totalFixedGroup := J.map eqv.symm.toMonoidHom with hJ₁
  set J₀ : Subgroup (adjointGroup τ k) := J₁.map Dd.totalFixedGroup.subtype with hJ₀
  have hle : J₀ ≤ Dd.totalFixedGroup := Subgroup.map_subtype_le _
  have hsub : J₀.subgroupOf Dd.totalFixedGroup = J₁ :=
    Subgroup.comap_map_eq_self_of_injective Dd.totalFixedGroup.subtype_injective J₁
  have hJ₀c : CFSG.IsPComponent 2 (J₀.subgroupOf Dd.totalFixedGroup) := by
    rw [hsub]
    exact LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 eqv.symm hL₁c
  obtain ⟨J', hJ', hq⟩ := exists_eq_orbitGroupC_of_isPComponent' Dd hX hle hJ₀c
  set D' := Dd.withOrbit J' with hD'
  have : Nontrivial D'.orbitGroup := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hns : ¬ SmallType D'.orbitGroup := orbitGroup_not_smallType D' fun O hO _ => by
    refine orbitMap_neg_one_ne_one D' hr₀ hO ?_
    obtain ⟨β, hβ, rfl⟩ := hO
    have hβK := D'.mem_kernelRoots_of_mem_simpleRootsJ hβ
    rw [show D'.χ = Dd.χ from rfl, hχ] at hβK
    exact hsize β hβK
  have e₁ : L ≃* L' := L.equivMapOfInjective _ (MulAut.conj g₁).injective
  have e₂ : L' ≃* J := (Subgroup.subgroupOfEquivOfLe hL₁).symm
  have e₃ : J ≃* J₁ := J.equivMapOfInjective _ eqv.symm.injective
  have e₄ : J₁ ≃* J₀ := J₁.equivMapOfInjective _ Dd.totalFixedGroup.subtype_injective
  have e₅ : J₀ ≃* D'.orbitGroupC := MulEquiv.subgroupCongr hJ'
  have e₆ : D'.orbitGroupC ≃* D'.orbitGroup :=
    Subgroup.subgroupOfEquivOfLe D'.orbitGroup_le_adjointGroup
  exact fun hs => hns ((smallType_congr
    (e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans e₆)))))).1 hs)

variable (k) in
@[expose] def NoSmallInvolutionComponent (τ : Tag) (e : ℕ) (D : ModGL τ k) : Prop :=
  ∀ x ∈ fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D), x ^ 2 = 1 →
    ∀ L : Subgroup (ModGL τ k),
      Assembly.IsComponentOf L (⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
        fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x}) →
      ¬ SmallType L

variable (k) in
theorem e7_twisted_e6_triality_rational_inner_not_smallType (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (e : ℕ) (he : 1 ≤ e) :
    NoSmallInvolutionComponent p k .E7 e 1 ∧
    NoSmallInvolutionComponent p k TwistTag.E6.tag e (diagramMap TwistTag.E6 k) ∧
    NoSmallInvolutionComponent p k TwistTag.D4.tag e (diagramMap TwistTag.D4 k) := by
  obtain ⟨h7, h6, h4⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨r7, r6, r4⟩ := rational_inner_involution_finite_toral_twist_reduction p k hp e he
  obtain ⟨n7, n6, n4⟩ := rational_toral_twist_semilinear_pinning_normalization p k hp e he
  have hdiag : ∀ t : TwistTag, Finite (fixedPointsIn (adjointGroup t.tag k)
      (frobTwistGL t.tag k p e (diagramMap t k))) := fun t =>
    finite_fixedPointsIn_frobTwistGL p he (by cases t <;> decide)
      (units_map_entrywiseHom_diagramMap (t := t) (iterateFrobenius k p e))
      (diagramMap_pow_order t k)
  refine ⟨fun x hx hx2 L hL => ?_, fun x hx hx2 L hL => ?_, fun x hx hx2 L hL => ?_⟩
  · exact not_smallType_of_isFiniteToralTwistReduction p hp hk he (Or.inr (Or.inr rfl))
      (ρ := 1) (fun _ _ => rfl) (fun _ _ => rfl) (Or.inl ⟨Or.inr rfl, rfl⟩) h7.theta
      (fun l _ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ) (one_mem _)
      (map_conj_one_adjointGroup _ k) n7
      (finite_fixedPointsIn_frobTwistGL p he le_rfl (map_one _) (one_pow 1)) (r7 x hx hx2) hL
  · exact not_smallType_of_isFiniteToralTwistReduction p hp hk he (Or.inr (Or.inl rfl))
      TwistTag.E6.cartan_perm symmetrizedCartan_perm_E6 (Or.inl ⟨Or.inl rfl, rfl⟩) h6.theta
      (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.E6 l hγ)
      (diagramMap_mem_normalizer TwistTag.E6) (map_conj_diagramMap TwistTag.E6 k (Or.inl rfl))
      n6 (hdiag TwistTag.E6) (r6 x hx hx2) hL
  · exact not_smallType_of_isFiniteToralTwistReduction p hp hk he (Or.inl rfl)
      TwistTag.D4.cartan_perm symmetrizedCartan_perm_D4 (Or.inr ⟨rfl, rfl⟩) h4.theta
      (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.D4 l hγ)
      (diagramMap_mem_normalizer TwistTag.D4) (map_conj_diagramMap TwistTag.D4 k (Or.inl rfl))
      n4 (hdiag TwistTag.D4) (r4 x hx hx2) hL

end Main

end CFSG.ComponentClassification.ExcSelector
