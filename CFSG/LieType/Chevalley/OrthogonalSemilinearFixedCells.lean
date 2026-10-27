module

public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedUnipotent

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise commutatorElement

variable (τ) in
@[expose] def rootWeylOne
    (k : Type) [Field k] (β : Fin τ.rank → ℤ) : ModGL τ k :=
  rootWeylSL2 τ k β 1

theorem rootWeylOne_spec
    {τ : Tag} {K : Type} [Field K] {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootWeylOne τ K β ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ∧
      rootWeylOne τ K β ∈ monomialSubgroup τ K ∧
      MapsRootLines (rootWeylOne τ K β) (rootReflection β) := by
  have h := exceptional_Lang_root_rank_one_torus_transport τ K hβ
  obtain ⟨hN, hw⟩ := h.2.2.1 1
  refine ⟨?_, hN, ?_⟩
  · rw [← h.1]
    exact ⟨_, rfl⟩
  · have := mapsRootLines_weylQuotientHom (⟨_, hN⟩ : monomialSubgroup τ K)
    rwa [hw] at this

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

@[expose] def fixedTorus :
    Subgroup (adjointGroup τ k) :=
  D.torusJ.subgroupOf (adjointGroup τ k) ⊓ D.F.toMonoidHom.eqLocus (MonoidHom.id _)

@[expose] def orbitGroupC :
    Subgroup (adjointGroup τ k) :=
  D.orbitGroup.subgroupOf (adjointGroup τ k)

@[expose] def inversionRootsJ
    (w : WeylGroup τ) : Set (Fin τ.rank → ℤ) :=
  {α | α ∈ D.posRootsJ ∧ w • α ∈ negRoots D.roots}

@[expose] def orbitMonomial :
    Subgroup (ModGL τ k) :=
  Subgroup.closure ((D.orbitTorus : Set (ModGL τ k)) ∪ {g | ∃ O ∈ D.orbits, g = D.orbitN O})

theorem orbitGroup_le_adjointGroup :
    D.orbitGroup ≤ adjointGroup τ k := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨O, -, c, rfl | rfl⟩ <;> exact D.orbitMap_mem_adjointGroup O _

theorem mem_fixedTorus
    {x : adjointGroup τ k} :
    x ∈ D.fixedTorus ↔ (x : ModGL τ k) ∈ D.torusJ ∧ D.F x = x := by
  rw [fixedTorus, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rfl

theorem mem_fixedUnipotent
    {x : adjointGroup τ k} :
    x ∈ D.fixedUnipotent ↔ (x : ModGL τ k) ∈ D.unipotentJ ∧ D.F x = x := by
  rw [fixedUnipotent, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rfl

theorem mem_fixedGroup
    {x : adjointGroup τ k} :
    x ∈ D.fixedGroup ↔ (x : ModGL τ k) ∈ D.rootSpanJ ∧ D.F x = x := by
  rw [fixedGroup, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rfl

theorem orbitGroupC_le_fixedGroup :
    D.orbitGroupC ≤ D.fixedGroup := by
  intro x hx
  have hx' : (x : ModGL τ k) ∈ D.orbitGroup := Subgroup.mem_subgroupOf.1 hx
  have key : ∀ g (hg : g ∈ D.orbitGroup),
      (⟨g, D.orbitGroup_le_adjointGroup hg⟩ : adjointGroup τ k) ∈ D.fixedGroup := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨O, hO, c, rfl | rfl⟩ := hg
      · exact D.orbitMap_mem_fixedGroup hO _
      · exact D.orbitMap_mem_fixedGroup hO _
    | one => exact one_mem _
    | mul g h _ _ hg hh => exact mul_mem hg hh
    | inv g _ hg => exact inv_mem hg
  exact key _ hx'

theorem coe_mem_orbitGroup_of_mem_orbitGroupC
    {x : adjointGroup τ k} (hx : x ∈ D.orbitGroupC) :
    (x : ModGL τ k) ∈ D.orbitGroup :=
  Subgroup.mem_subgroupOf.1 hx

theorem rootWeylOne_union_spec :
    ∀ β ∈ unionSimpleRoots D.χ D.J,
    rootWeylOne τ k β ∈ rootSubgroup τ k β ⊔ rootSubgroup τ k (-β) ∧
      rootWeylOne τ k β ∈ monomialSubgroup τ k ∧
      MapsRootLines (rootWeylOne τ k β) (rootReflection β) :=
  fun _ hβ => rootWeylOne_spec (isRoot_of_mem_unionSimpleRoots hβ)

theorem orbitN_mem_unionMonomial
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.orbitN O ∈ unionMonomial k D.χ D.J (rootWeylOne τ k) := by
  rw [orbitN, orbitMap_eq_prod]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  rw [D.orbitFactor_WSL]
  exact lift_mem_unionMonomial (n := rootWeylOne τ k)
    (D.mem_unionSimpleRoots_of_mem_orbits hO (D.orbitVec_mem hO j))

theorem mem_unionLifts_of_isOrbitLift
    {n : ModGL τ k} {w : WeylGroup τ} (h : D.IsOrbitLift n w) :
    n ∈ unionLifts k D.χ D.J (rootWeylOne τ k) w := by
  obtain ⟨-, ⟨hN, hw⟩, -⟩ := D.isOrbitLift_spec h
  refine ⟨?_, by
    have := mapsRootLines_weylQuotientHom (⟨n, hN⟩ : monomialSubgroup τ k)
    rwa [hw] at this⟩
  obtain ⟨l, hl, -, rfl⟩ := h
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨O, hO, rfl⟩ := List.mem_map.1 hx
    exact D.orbitN_mem_unionMonomial (hl O hO)

theorem bijOn_unionSimpleRoots :
    Set.BijOn D.θ (toReal '' unionSimpleRoots D.χ D.J) (toReal '' unionSimpleRoots D.χ D.J) := by
  rw [← D.simpleRootsJ_eq]
  exact D.bijOn_simpleRootsJ

theorem coe_F_rootWeylOne
    {β β' : Fin τ.rank → ℤ} (hβ : β ∈ unionSimpleRoots D.χ Set.univ)
    (h : D.θ (toReal β) = toReal β') {x : adjointGroup τ k}
    (hx : (x : ModGL τ k) = rootWeylOne τ k β) : (D.F x : ModGL τ k) = rootWeylOne τ k β' := by
  rw [D.map_rootSL2 β hβ β' h (nSL 1) x hx, nSL_one, map_WSL]
  rfl

theorem exists_isUnionWeylConj_F_mem_unionCell_iff
    {w : WeylGroup τ}
    (hw : w ∈ unionWeylGroup D.χ D.J) :
    ∃ w' ∈ unionWeylGroup D.χ D.J, IsUnionWeylConj D.χ D.J D.θ w w' ∧
      (∀ u ∈ unionWeylGroup D.χ D.J, IsUnionWeylConj D.χ D.J D.θ w u → u = w') ∧
      ∀ x : adjointGroup τ k, ((D.F x : ModGL τ k) ∈ unionCell k D.χ D.J (rootWeylOne τ k) w' ↔
        (x : ModGL τ k) ∈ unionCell k D.χ D.J (rootWeylOne τ k) w) :=
  exists_isUnionWeylConj_mulAut_mem_unionCell_iff D.rootWeylOne_union_spec D.isometry
    D.bijOn_roots D.bijOn_unionSimpleRoots D.map_torusGroup
    (fun α hα α' _ h => D.map_rootSubgroup α hα.1 α' h)
    (fun β hβ β' _ h x hx => ⟨1, one_mem _, by
      rw [one_mul]
      obtain ⟨i, -, hi⟩ := hβ
      exact D.coe_F_rootWeylOne ⟨i, Set.mem_univ i, hi⟩ h hx⟩) hw

theorem mem_fixedWeyl_of_mem_unionCell
    {g : adjointGroup τ k} (hgF : D.F g = g)
    {w : WeylGroup τ} (hw : w ∈ unionWeylGroup D.χ D.J)
    (hg : (g : ModGL τ k) ∈ unionCell k D.χ D.J (rootWeylOne τ k) w) : w ∈ D.fixedWeyl := by
  obtain ⟨w', hw', hc, -, hiff⟩ := D.exists_isUnionWeylConj_F_mem_unionCell_iff hw
  have h1 := (hiff g).2 hg
  rw [hgF] at h1
  have hww : w = w' := by
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_unionCell D.rootWeylOne_union_spec hne) hg h1
  subst hww
  exact D.mem_fixedWeyl_iff.2 ⟨hw, hc⟩

theorem inversionRootsJ_eq
    {w : WeylGroup τ} (hw : w ∈ unionWeylGroup D.χ D.J) :
    D.inversionRootsJ w = unionInversionRoots D.χ D.J w := by
  ext α
  refine and_congr_right fun hα => ?_
  exact mem_negRoots_iff_height_neg (smul_mem_unionRoots hw hα.1)

theorem mapsTo_inversionRootsJ
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) :
    Set.MapsTo D.θ (toReal '' D.inversionRootsJ w) (toReal '' D.inversionRootsJ w) := by
  obtain ⟨hwJ, hc⟩ := D.mem_fixedWeyl_iff.1 hw
  rintro _ ⟨α, ⟨hα, hwα⟩, rfl⟩
  obtain ⟨α', hα', e⟩ := D.mapsTo_roots ⟨α, hα.1, rfl⟩
  refine ⟨α', ⟨D.mem_posRootsJ_of_theta hα hα' e.symm, ?_⟩, e⟩
  obtain ⟨γ, hγ, e'⟩ := D.mapsTo_negRoots ⟨_, hwα, rfl⟩
  have h := hc α hα.1 α' hα' e.symm
  rw [← e', ] at h
  rwa [← toReal_injective h]

theorem bijOn_inversionRootsJ
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) :
    Set.BijOn D.θ (toReal '' D.inversionRootsJ w) (toReal '' D.inversionRootsJ w) :=
  (Set.Finite.injOn_iff_bijOn_of_mapsTo
    ((D.finite_roots.subset fun _ hα => hα.1.1).image _) (D.mapsTo_inversionRootsJ hw)).1
    D.theta_injective.injOn

theorem inversionRootsJ_closed
    {w : WeylGroup τ} (hw : w ∈ unionWeylGroup D.χ D.J) :
    ∀ α ∈ D.inversionRootsJ w, ∀ β ∈ D.inversionRootsJ w, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • α + b • β) → a • α + b • β ∈ D.inversionRootsJ w := by
  intro α hα β hβ a b ha hb hr
  have hpos := nsmul_add_mem_posRoots_unionRoots hα.1 hβ.1 a b ha hb hr
  refine ⟨hpos, (mem_negRoots_iff_height_neg (smul_mem_unionRoots hw hpos.1)).2 ?_⟩
  have h1 := (mem_negRoots_iff_height_neg (smul_mem_unionRoots hw hα.1.1)).1 hα.2
  have h2 := (mem_negRoots_iff_height_neg (smul_mem_unionRoots hw hβ.1.1)).1 hβ.2
  rw [smul_add, smul_comm w a α, smul_comm w b β, height_add, ← Nat.cast_smul_eq_nsmul ℤ a,
    ← Nat.cast_smul_eq_nsmul ℤ b, height_zsmul, height_zsmul]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

theorem posRootsJ_closed :
    ∀ α ∈ D.posRootsJ, ∀ β ∈ D.posRootsJ, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • α + b • β) → a • α + b • β ∈ D.posRootsJ :=
  fun _ hα _ hβ a b ha hb hr => nsmul_add_mem_posRoots_unionRoots hα hβ a b ha hb hr

theorem fixedUnipotent_le_orbitGroupC
    : D.fixedUnipotent ≤ D.orbitGroupC := fun _ hx =>
  Subgroup.mem_subgroupOf.2 (D.mem_orbitGroup_of_mem_fixedRootSpan (S := D.posRootsJ)
    le_rfl (fun _ hα => D.thetaOrbit_subset_posRootsJ hα) D.posRootsJ_closed
    (D.mem_fixedRootSpan.2 (D.mem_fixedUnipotent.1 hx)))

theorem fixedRootSpan_inversionRootsJ_le
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) :
    D.fixedRootSpan (D.inversionRootsJ w) ≤ D.orbitGroupC := fun _ hx =>
  Subgroup.mem_subgroupOf.2 (D.mem_orbitGroup_of_mem_fixedRootSpan (fun _ hα => hα.1)
    (fun _ hα => thetaOrbit_subset_of_mapsTo (D.mapsTo_inversionRootsJ hw) hα)
    (D.inversionRootsJ_closed (D.mem_unionWeylGroup_of_mem_fixedWeyl hw)) hx)

end OrthogonalSemilinearFixedRootDatum

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem coe_F_mem_of_map_eq
    {H : Subgroup (ModGL τ k)}
    (hH : (H.subgroupOf (adjointGroup τ k)).map D.F.toMonoidHom = H.subgroupOf (adjointGroup τ k))
    {x : adjointGroup τ k} (hx : (x : ModGL τ k) ∈ H) : (D.F x : ModGL τ k) ∈ H := by
  have h1 : D.F x ∈ (H.subgroupOf (adjointGroup τ k)).map D.F.toMonoidHom :=
    ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  rw [hH] at h1
  exact Subgroup.mem_subgroupOf.1 h1

theorem mem_adjointGroup_of_mem_rootSpanJ
    {g : ModGL τ k} (hg : g ∈ D.rootSpanJ) :
    g ∈ adjointGroup τ k :=
  unionRootSpan_le_adjointGroup hg

theorem exists_torus_mul_unipotent
    {b : ModGL τ k} (hb : b ∈ unionBorel k D.χ D.J) :
    ∃ t : adjointGroup τ k, (t : ModGL τ k) ∈ D.torusJ ∧ ∃ u : adjointGroup τ k,
      (u : ModGL τ k) ∈ D.unipotentJ ∧ (t : ModGL τ k) * u = b := by
  have hb' : b ∈ (unionTorus k D.χ D.J : Set (ModGL τ k)) *
      (unionUnipotent k D.χ D.J : Set (ModGL τ k)) := by
    rw [← coe_unionBorel]
    exact hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb'
  exact ⟨⟨t, D.mem_adjointGroup_of_mem_rootSpanJ (unionTorus_le_unionRootSpan ht)⟩, ht,
    ⟨u, D.mem_adjointGroup_of_mem_rootSpanJ (unionUnipotent_le_unionRootSpan hu)⟩, hu, rfl⟩

theorem coe_F_mem_unionBorel
    {x : adjointGroup τ k}
    (hx : (x : ModGL τ k) ∈ unionBorel k D.χ D.J) :
    (D.F x : ModGL τ k) ∈ unionBorel k D.χ D.J := by
  obtain ⟨t, ht, u, hu, htu⟩ := D.exists_torus_mul_unipotent hx
  have e : x = t * u := Subtype.ext htu.symm
  rw [e, map_mul, Subgroup.coe_mul]
  exact mul_mem (unionTorus_le_unionBorel (D.coe_F_mem_of_map_eq D.map_torusJ ht))
    (unionUnipotent_le_unionBorel (D.coe_F_mem_of_map_eq D.map_unipotentJ hu))

theorem exists_fixed_torus_mul_unipotent
    {b : adjointGroup τ k}
    (hb : (b : ModGL τ k) ∈ unionBorel k D.χ D.J) (hbF : D.F b = b) :
    ∃ t ∈ D.fixedTorus, ∃ u ∈ D.fixedUnipotent, b = t * u := by
  obtain ⟨t, ht, u, hu, htu⟩ := D.exists_torus_mul_unipotent hb
  have e : b = t * u := Subtype.ext htu.symm
  have hFt := D.coe_F_mem_of_map_eq D.map_torusJ ht
  have hFu := D.coe_F_mem_of_map_eq D.map_unipotentJ hu
  have h1 : (D.F t : ModGL τ k) * D.F u = t * u := by
    rw [← Subgroup.coe_mul, ← map_mul, ← e, hbF, e, Subgroup.coe_mul]
  obtain ⟨h2, h3⟩ := eq_and_eq_of_mul_eq_mul hFt ht hFu hu h1
  exact ⟨t, D.mem_fixedTorus.2 ⟨ht, Subtype.ext h2⟩, u, D.mem_fixedUnipotent.2 ⟨hu, Subtype.ext h3⟩,
    e⟩

theorem fixed_factorization
    {g : adjointGroup τ k} (hgF : D.F g = g) {w : WeylGroup τ}
    (hw : w ∈ unionWeylGroup D.χ D.J)
    (hg : (g : ModGL τ k) ∈ unionCell k D.χ D.J (rootWeylOne τ k) w)
    {x : adjointGroup τ k} (hx : (x : ModGL τ k) ∈ unionLifts k D.χ D.J (rootWeylOne τ k) w)
    (hxF : D.F x = x) :
    ∃ t ∈ D.fixedTorus, ∃ u ∈ D.fixedUnipotent, ∃ v ∈ D.fixedRootSpan (D.inversionRootsJ w),
      g = t * u * x * v := by
  have hw0 := D.mem_fixedWeyl_of_mem_unionCell hgF hw hg
  have hbij := bijOn_mul_unionCell D.rootWeylOne_union_spec hw hx
  rw [← doubleCoset_eq_unionCell D.rootWeylOne_union_spec hx] at hg
  obtain ⟨⟨b, v⟩, ⟨hb, hv⟩, hbv⟩ := hbij.surjOn hg
  have hbA : b ∈ adjointGroup τ k :=
    D.mem_adjointGroup_of_mem_rootSpanJ (unionBorel_le_unionRootSpan hb)
  rw [← D.inversionRootsJ_eq hw] at hv
  have hvA : v ∈ adjointGroup τ k :=
    D.mem_adjointGroup_of_mem_rootSpanJ (rootSpan_mono (fun _ hα => hα.1.1) hv)
  set b' : adjointGroup τ k := ⟨b, hbA⟩ with hb'
  set v' : adjointGroup τ k := ⟨v, hvA⟩ with hv'
  have hgbv : g = b' * x * v' := Subtype.ext hbv.symm
  have hFb : (D.F b' : ModGL τ k) ∈ unionBorel k D.χ D.J := D.coe_F_mem_unionBorel hb
  have hFv : (D.F v' : ModGL τ k) ∈ rootSpan τ k (D.inversionRootsJ w) :=
    D.coe_F_mem_of_map_eq (D.map_rootSpan_subgroupOf (fun α hα => hα.1.1.1)
      (D.bijOn_inversionRootsJ hw0)) hv
  rw [D.inversionRootsJ_eq hw] at hFv hv
  have hFg : (D.F b' : ModGL τ k) * x * (D.F v' : ModGL τ k) = b * x * v := by
    have := congrArg Subtype.val (show D.F (b' * x * v') = b' * x * v' by rw [← hgbv, hgF])
    rw [map_mul, map_mul, hxF] at this
    exact this
  have huniq := hbij.injOn (x₁ := ((D.F b' : ModGL τ k), (D.F v' : ModGL τ k))) ⟨hFb, hFv⟩
    ⟨hb, hv⟩ hFg
  have hFb' : D.F b' = b' := Subtype.ext (congrArg Prod.fst huniq)
  have hFv' : D.F v' = v' := Subtype.ext (congrArg Prod.snd huniq)
  obtain ⟨t, ht, u, hu, hbtu⟩ := D.exists_fixed_torus_mul_unipotent hb hFb'
  rw [← D.inversionRootsJ_eq hw] at hv
  exact ⟨t, ht, u, hu, v', D.mem_fixedRootSpan.2 ⟨hv, hFv'⟩, by rw [hgbv, hbtu]⟩

theorem exists_fixedWeyl_mem_unionCell
    {g : adjointGroup τ k} (hg : g ∈ D.fixedGroup) :
    ∃ w ∈ D.fixedWeyl, (g : ModGL τ k) ∈ unionCell k D.χ D.J (rootWeylOne τ k) w := by
  obtain ⟨hgS, hgF⟩ := D.mem_fixedGroup.1 hg
  have h := (coe_unionRootSpan_eq_iUnion D.rootWeylOne_union_spec).subset hgS
  simp only [Set.mem_iUnion, exists_prop] at h
  obtain ⟨w, hw, hgw⟩ := h
  exact ⟨w, D.mem_fixedWeyl_of_mem_unionCell hgF hw hgw, hgw⟩

end OrthogonalSemilinearFixedRootDatum

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem fixedTorus_le_fixedGroup
    : D.fixedTorus ≤ D.fixedGroup := fun _ ht =>
  D.mem_fixedGroup.2 ⟨unionTorus_le_unionRootSpan (D.mem_fixedTorus.1 ht).1,
    (D.mem_fixedTorus.1 ht).2⟩

theorem exists_fixed_lift
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) :
    ∃ x : adjointGroup τ k, D.IsOrbitLift (x : ModGL τ k) w ∧ D.F x = x := by
  obtain ⟨n, hn⟩ := D.exists_isOrbitLift hw
  obtain ⟨-, -, x, rfl, hxF⟩ := D.isOrbitLift_spec hn
  exact ⟨x, hn, hxF⟩

theorem coe_fixedGroup_eq_mul :
    (D.fixedGroup : Set (adjointGroup τ k)) =
      (D.fixedTorus : Set (adjointGroup τ k)) * (D.orbitGroupC : Set (adjointGroup τ k)) := by
  ext g
  constructor
  · intro hg
    obtain ⟨w, hw, hgw⟩ := D.exists_fixedWeyl_mem_unionCell hg
    obtain ⟨x, hx, hxF⟩ := D.exists_fixed_lift hw
    obtain ⟨t, ht, u, hu, v, hv, rfl⟩ := D.fixed_factorization (D.mem_fixedGroup.1 hg).2
      (D.mem_unionWeylGroup_of_mem_fixedWeyl hw) hgw (D.mem_unionLifts_of_isOrbitLift hx) hxF
    refine ⟨t, ht, u * x * v, mul_mem (mul_mem (D.fixedUnipotent_le_orbitGroupC hu)
      (Subgroup.mem_subgroupOf.2 (D.isOrbitLift_spec hx).1))
      (D.fixedRootSpan_inversionRootsJ_le hw hv), by group⟩
  · rintro ⟨t, ht, c, hc, rfl⟩
    exact mul_mem (D.fixedTorus_le_fixedGroup ht) (D.orbitGroupC_le_fixedGroup hc)

theorem conj_mem_orbitGroupC_of_mem_fixedTorus
    {t : adjointGroup τ k} (ht : t ∈ D.fixedTorus)
    {c : adjointGroup τ k} (hc : c ∈ D.orbitGroupC) : t * c * t⁻¹ ∈ D.orbitGroupC := by
  obtain ⟨htT, htF⟩ := D.mem_fixedTorus.1 ht
  have htH : (t : ModGL τ k) ∈ torusGroup τ k := unionTorus_le_torusGroup htT
  have hgen : ∀ (S : Set (Fin τ.rank → ℤ)), (∀ γ ∈ S, IsRoot τ γ) → ∀ y ∈ D.fixedRootSpan S,
      t * y * t⁻¹ ∈ D.fixedRootSpan S := by
    intro S hS y hy
    obtain ⟨hyU, hyF⟩ := D.mem_fixedRootSpan.1 hy
    refine D.mem_fixedRootSpan.2 ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSpan hS htH) _).1 hyU
    · rw [map_mul, map_mul, map_inv, htF, hyF]
  have key : ∀ g (hg : g ∈ D.orbitGroup),
      (t : ModGL τ k) * g * (t : ModGL τ k)⁻¹ ∈ D.orbitGroup := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨O, hO, c, rfl | rfl⟩ := hg
      · have hX := hgen O (fun γ hγ => D.isRoot_of_mem_orbits hO hγ) _
          (D.orbitX_mem_fixedRootSpan hO c)
        have h1 : ((t * ⟨D.orbitX O c, D.orbitMap_mem_adjointGroup O _⟩ * t⁻¹ :
            adjointGroup τ k) : ModGL τ k) ∈ Set.range (D.orbitX O) := by
          rw [D.range_orbitX hO]
          exact ⟨_, hX, rfl⟩
        exact D.range_orbitMap_subset hO (by
          obtain ⟨c', hc'⟩ := h1
          exact ⟨_, hc'⟩)
      · have hY : (⟨D.orbitY O c, D.orbitMap_mem_adjointGroup O _⟩ : adjointGroup τ k) ∈
            D.fixedRootSpan ((fun γ => -γ) '' O) := by
          have h1 : D.orbitY O c ∈ Set.range (D.orbitY O) := ⟨c, rfl⟩
          rw [D.range_orbitY hO] at h1
          obtain ⟨y, hy, hye⟩ := h1
          have e : y = ⟨D.orbitY O c, D.orbitMap_mem_adjointGroup O _⟩ := Subtype.ext hye
          rwa [← e]
        have hY' := hgen _ (by
          rintro _ ⟨γ, hγ, rfl⟩
          exact IsRoot.neg (D.isRoot_of_mem_orbits hO hγ)) _ hY
        have h1 : ((t * ⟨D.orbitY O c, D.orbitMap_mem_adjointGroup O _⟩ * t⁻¹ :
            adjointGroup τ k) : ModGL τ k) ∈ Set.range (D.orbitY O) := by
          rw [D.range_orbitY hO]
          exact ⟨_, hY', rfl⟩
        obtain ⟨c', hc'⟩ := h1
        exact D.range_orbitMap_subset hO ⟨_, hc'⟩
    | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
    | mul g h _ _ hg hh =>
      have e : (t : ModGL τ k) * (g * h) * (t : ModGL τ k)⁻¹ =
          ((t : ModGL τ k) * g * (t : ModGL τ k)⁻¹) *
            ((t : ModGL τ k) * h * (t : ModGL τ k)⁻¹) := by
        group
      rw [e]
      exact mul_mem hg hh
    | inv g _ hg =>
      have e : (t : ModGL τ k) * g⁻¹ * (t : ModGL τ k)⁻¹ =
          ((t : ModGL τ k) * g * (t : ModGL τ k)⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hg
  exact Subgroup.mem_subgroupOf.2 (key _ (Subgroup.mem_subgroupOf.1 hc))

theorem orbitGroupC_normal
    : (D.orbitGroupC.subgroupOf D.fixedGroup).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg : (g : adjointGroup τ k) ∈ (D.fixedTorus : Set (adjointGroup τ k)) *
      (D.orbitGroupC : Set (adjointGroup τ k)) := by
    rw [← D.coe_fixedGroup_eq_mul]
    exact g.2
  obtain ⟨t, ht, c, hc, hgtc⟩ := hg
  have e : ((g * n * g⁻¹ : D.fixedGroup) : adjointGroup τ k) =
      t * (c * (n : adjointGroup τ k) * c⁻¹) * t⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hgtc]
    group
  rw [e]
  exact D.conj_mem_orbitGroupC_of_mem_fixedTorus ht (mul_mem (mul_mem hc hn) (inv_mem hc))

theorem commutator_fixedGroup_le
    : ⁅D.fixedGroup, D.fixedGroup⁆ ≤ D.orbitGroupC := by
  have hN := D.orbitGroupC_normal
  set H := D.orbitGroupC.subgroupOf D.fixedGroup with hH
  have hdec : ∀ a : D.fixedGroup, ∃ t ∈ D.fixedTorus, ∃ ht : t ∈ D.fixedGroup,
      QuotientGroup.mk' H a = QuotientGroup.mk' H ⟨t, ht⟩ := by
    intro a
    have ha : (a : adjointGroup τ k) ∈ (D.fixedTorus : Set (adjointGroup τ k)) *
        (D.orbitGroupC : Set (adjointGroup τ k)) := by
      rw [← D.coe_fixedGroup_eq_mul]
      exact a.2
    obtain ⟨t, ht, c, hc, htc⟩ := ha
    refine ⟨t, ht, D.fixedTorus_le_fixedGroup ht, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.2 ?_
    have e : ((a⁻¹ * ⟨t, D.fixedTorus_le_fixedGroup ht⟩ : D.fixedGroup) : adjointGroup τ k) =
        c⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← htc]
      show (t * c)⁻¹ * t = c⁻¹
      group
    rw [e]
    exact inv_mem hc
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨t₁, ht₁, ht₁', e₁⟩ := hdec ⟨g₁, hg₁⟩
  obtain ⟨t₂, ht₂, ht₂', e₂⟩ := hdec ⟨g₂, hg₂⟩
  have hcomm : (⟨t₁, ht₁'⟩ : D.fixedGroup) * ⟨t₂, ht₂'⟩ = ⟨t₂, ht₂'⟩ * ⟨t₁, ht₁'⟩ :=
    Subtype.ext (Subtype.ext (mul_comm_of_mem_unionTorus (D.mem_fixedTorus.1 ht₁).1
      (D.mem_fixedTorus.1 ht₂).1))
  have h1 : QuotientGroup.mk' H ⁅(⟨g₁, hg₁⟩ : D.fixedGroup), ⟨g₂, hg₂⟩⁆ = 1 := by
    rw [map_commutatorElement, e₁, e₂, ← map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.2 hcomm, map_one]
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)

end OrthogonalSemilinearFixedRootDatum

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

@[expose] def fixedUnipotentM :
    Subgroup (ModGL τ k) :=
  D.fixedUnipotent.map (adjointGroup τ k).subtype

theorem mem_unionBorel_of_mem_borelGroup
    {g : ModGL τ k} (hgS : g ∈ D.rootSpanJ)
    (hgB : g ∈ borelGroup τ k) : g ∈ unionBorel k D.χ D.J := by
  have h := (coe_unionRootSpan_eq_iUnion D.rootWeylOne_union_spec).subset hgS
  simp only [Set.mem_iUnion, exists_prop] at h
  obtain ⟨w, -, hgw⟩ := h
  have hw1 : w = 1 := by
    by_contra hne
    have h1 := unionCell_subset_bruhatCell D.rootWeylOne_union_spec w hgw
    have h2 : g ∈ bruhatCell τ k 1 :=
      mem_bruhatCell.2 ⟨g, hgB, 1, one_mem _, by rw [canonicalRep_one, mul_one, mul_one]⟩
    exact Set.disjoint_left.1 (disjoint_bruhatCell hne) h1 h2
  subst hw1
  obtain ⟨b, hb, x, hx, b', hb', rfl⟩ := mem_unionCell.1 hgw
  have hxT := mem_unionTorus_of_mapsRootLines_one D.rootWeylOne_union_spec hx.1 hx.2
  exact mul_mem (mul_mem hb (unionTorus_le_unionBorel hxT)) hb'

theorem mk_mem_orbitGroupC
    {g : ModGL τ k} (hg : g ∈ D.orbitGroup) :
    (⟨g, D.orbitGroup_le_adjointGroup hg⟩ : adjointGroup τ k) ∈ D.orbitGroupC :=
  Subgroup.mem_subgroupOf.2 hg

theorem orbitGroup_le_rootSpanJ
    : D.orbitGroup ≤ D.rootSpanJ := fun _ hg =>
  (D.mem_fixedGroup.1 (D.orbitGroupC_le_fixedGroup (D.mk_mem_orbitGroupC hg))).1

theorem orbitBorel_le_unionBorel
    : D.orbitBorel ≤ unionBorel k D.χ D.J := fun _ hg =>
  D.mem_unionBorel_of_mem_borelGroup (D.orbitGroup_le_rootSpanJ hg.1) hg.2

theorem orbitTorus_le_torusJ
    : D.orbitTorus ≤ D.torusJ := fun _ hg =>
  Subgroup.mem_inf.2 ⟨D.orbitGroup_le_rootSpanJ hg.1, hg.2⟩

theorem fixedUnipotentM_le_orbitBorel
    : D.fixedUnipotentM ≤ D.orbitBorel := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨Subgroup.mem_subgroupOf.1 (D.fixedUnipotent_le_orbitGroupC hu),
    Subgroup.mem_sup_right (unionUnipotent_le_posUnipotent (D.mem_fixedUnipotent.1 hu).1)⟩

theorem coe_orbitBorel_eq_mul :
    (D.orbitBorel : Set (ModGL τ k)) =
      (D.orbitTorus : Set (ModGL τ k)) * (D.fixedUnipotentM : Set (ModGL τ k)) := by
  ext c
  constructor
  · intro hc
    have hcA := D.orbitGroup_le_adjointGroup hc.1
    have hcΓ := D.orbitGroupC_le_fixedGroup (D.mk_mem_orbitGroupC hc.1)
    obtain ⟨t, ht, u, hu, e⟩ := D.exists_fixed_torus_mul_unipotent
      (D.orbitBorel_le_unionBorel hc) (D.mem_fixedGroup.1 hcΓ).2
    have huC := Subgroup.mem_subgroupOf.1 (D.fixedUnipotent_le_orbitGroupC hu)
    have htC : (t : ModGL τ k) ∈ D.orbitGroup := by
      have e' : (t : ModGL τ k) = c * (u : ModGL τ k)⁻¹ := by
        rw [show c = ((⟨c, hcA⟩ : adjointGroup τ k) : ModGL τ k) from rfl, e, Subgroup.coe_mul]
        group
      rw [e']
      exact mul_mem hc.1 (inv_mem huC)
    refine ⟨t, ⟨htC, unionTorus_le_torusGroup (D.mem_fixedTorus.1 ht).1⟩, u, ⟨u, hu, rfl⟩, ?_⟩
    rw [show c = ((⟨c, hcA⟩ : adjointGroup τ k) : ModGL τ k) from rfl, e, Subgroup.coe_mul]
  · rintro ⟨t, ht, _, ⟨u, hu, rfl⟩, rfl⟩
    have hu' := D.fixedUnipotentM_le_orbitBorel ⟨u, hu, rfl⟩
    exact mul_mem (⟨ht.1, torusGroup_le_borelGroup ht.2⟩ : t ∈ D.orbitBorel) hu'

theorem eq_and_eq_of_orbitBorel
    {t t' u u' : ModGL τ k} (ht : t ∈ D.orbitTorus)
    (ht' : t' ∈ D.orbitTorus) (hu : u ∈ D.fixedUnipotentM) (hu' : u' ∈ D.fixedUnipotentM)
    (h : t * u = t' * u') : t = t' ∧ u = u' := by
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  obtain ⟨u₀', hu₀', rfl⟩ := hu'
  exact eq_and_eq_of_mul_eq_mul (D.orbitTorus_le_torusJ ht) (D.orbitTorus_le_torusJ ht')
    (D.mem_fixedUnipotent.1 hu₀).1 (D.mem_fixedUnipotent.1 hu₀').1 h

theorem fixedUnipotentM_normal
    : (D.fixedUnipotentM.subgroupOf D.orbitBorel).Normal := by
  refine ⟨fun n hn b => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨u, hu, hun⟩ := hn
  have hb := b.2
  have hbA := D.orbitGroup_le_adjointGroup hb.1
  have hbΓ := D.orbitGroupC_le_fixedGroup (D.mk_mem_orbitGroupC hb.1)
  obtain ⟨t, ht, u', hu', e⟩ := D.exists_fixed_torus_mul_unipotent
    (D.orbitBorel_le_unionBorel hb) (D.mem_fixedGroup.1 hbΓ).2
  set b' : adjointGroup τ k := ⟨(b : ModGL τ k), hbA⟩
  refine ⟨b' * u * b'⁻¹, D.mem_fixedUnipotent.2 ⟨?_, ?_⟩, ?_⟩
  · rw [e]
    have hTN := unionTorus_le_normalizer (D.mem_fixedTorus.1 ht).1
    show ((t * u' * u * (t * u')⁻¹ : adjointGroup τ k) : ModGL τ k) ∈ D.unipotentJ
    have e' : ((t * u' * u * (t * u')⁻¹ : adjointGroup τ k) : ModGL τ k) =
        (t : ModGL τ k) * ((u' : ModGL τ k) * u * (u' : ModGL τ k)⁻¹) * (t : ModGL τ k)⁻¹ := by
      push_cast
      group
    rw [e']
    exact (Subgroup.mem_normalizer_iff.1 hTN _).1 (mul_mem (mul_mem (D.mem_fixedUnipotent.1 hu').1
      (D.mem_fixedUnipotent.1 hu).1) (inv_mem (D.mem_fixedUnipotent.1 hu').1))
  · rw [map_mul, map_mul, map_inv, (D.mem_fixedGroup.1 hbΓ).2, (D.mem_fixedUnipotent.1 hu).2]
  · show ((b' * u * b'⁻¹ : adjointGroup τ k) : ModGL τ k) =
      ((b * n * b⁻¹ : D.orbitBorel) : ModGL τ k)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, ← hun]
    rfl

theorem isNilpotent_fixedUnipotent
    : Group.IsNilpotent D.fixedUnipotent := by
  have := isNilpotent_unionUnipotent (K := k) (χ := D.χ) (J := D.J)
  let f : D.fixedUnipotent →* unionUnipotent k D.χ D.J :=
    { toFun := fun x => ⟨((x : adjointGroup τ k) : ModGL τ k), (D.mem_fixedUnipotent.1 x.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Subgroup.isNilpotent_of_ker_le_center f ?_
  have hker : f.ker = ⊥ := by
    refine (MonoidHom.ker_eq_bot_iff f).2 fun x y h => Subtype.ext (Subtype.ext ?_)
    have := congrArg Subtype.val h
    exact this
  rw [hker]
  exact bot_le

theorem mul_comm_of_mem_orbitTorus
    {x y : ModGL τ k} (hx : x ∈ D.orbitTorus)
    (hy : y ∈ D.orbitTorus) : x * y = y * x :=
  mul_comm_of_mem_unionTorus (D.orbitTorus_le_torusJ hx) (D.orbitTorus_le_torusJ hy)

end OrthogonalSemilinearFixedRootDatum

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem orbitN_mem_orbitMonomial
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.orbitN O ∈ D.orbitMonomial :=
  Subgroup.subset_closure (Or.inr ⟨O, hO, rfl⟩)

theorem orbitTorus_le_orbitMonomial :
    D.orbitTorus ≤ D.orbitMonomial := fun _ ht =>
  Subgroup.subset_closure (Or.inl ht)

theorem orbitMonomial_le_monomialSubgroup :
    D.orbitMonomial ≤ monomialSubgroup τ k := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (ht | ⟨O, hO, rfl⟩)
  · exact Subgroup.mem_sup_left ht.2
  · exact (D.orbitN_mem_monomialSubgroup hO).1

theorem orbitMonomial_le_orbitGroup
    : D.orbitMonomial ≤ D.orbitGroup := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (ht | ⟨O, hO, rfl⟩)
  · exact ht.1
  · exact D.orbitMap_mem_orbitGroup hO _

theorem weylQuotientHom_mem_fixedWeyl
    {n : ModGL τ k} (hn : n ∈ D.orbitMonomial) :
    weylQuotientHom τ k ⟨n, D.orbitMonomial_le_monomialSubgroup hn⟩ ∈ D.fixedWeyl := by
  induction hn using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ht | ⟨O, hO, rfl⟩
    · rw [weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup ht.2)]
      exact one_mem _
    · rw [D.weylQuotientHom_orbitN hO]
      exact D.setReflection_mem_fixedWeyl hO
  | one =>
    have e : (⟨1, D.orbitMonomial_le_monomialSubgroup (one_mem _)⟩ : monomialSubgroup τ k) = 1 :=
      rfl
    rw [e, map_one]
    exact one_mem _
  | mul x y hx hy ihx ihy =>
    have e : (⟨x * y, D.orbitMonomial_le_monomialSubgroup (mul_mem hx hy)⟩ :
        monomialSubgroup τ k) = ⟨x, D.orbitMonomial_le_monomialSubgroup hx⟩ *
          ⟨y, D.orbitMonomial_le_monomialSubgroup hy⟩ := rfl
    rw [e, map_mul]
    exact mul_mem ihx ihy
  | inv x hx ihx =>
    have e : (⟨x⁻¹, D.orbitMonomial_le_monomialSubgroup (inv_mem hx)⟩ :
        monomialSubgroup τ k) = (⟨x, D.orbitMonomial_le_monomialSubgroup hx⟩)⁻¹ := rfl
    rw [e, map_inv]
    exact inv_mem ihx

@[expose] def orbitWeylHom :
    D.orbitMonomial →* D.fixedWeyl :=
  MonoidHom.codRestrict ((weylQuotientHom τ k).comp
    (Subgroup.inclusion D.orbitMonomial_le_monomialSubgroup)) D.fixedWeyl
    fun n => D.weylQuotientHom_mem_fixedWeyl n.2

theorem coe_orbitWeylHom
    (n : D.orbitMonomial) :
    (D.orbitWeylHom n : WeylGroup τ) =
      weylQuotientHom τ k ⟨n, D.orbitMonomial_le_monomialSubgroup n.2⟩ :=
  rfl

theorem orbitWeylHom_surjective
    : Function.Surjective D.orbitWeylHom := by
  intro w
  have key : ∀ u ∈ Subgroup.closure (setReflection '' D.orbits),
      ∃ n : D.orbitMonomial, (D.orbitWeylHom n : WeylGroup τ) = u := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨O, hO, rfl⟩ := hx
      exact ⟨⟨_, D.orbitN_mem_orbitMonomial hO⟩, D.weylQuotientHom_orbitN hO⟩
    | one => exact ⟨1, by rw [map_one]; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨n, hn⟩ := hx
      obtain ⟨n', hn'⟩ := hy
      exact ⟨n * n', by rw [map_mul, Subgroup.coe_mul, hn, hn']⟩
    | inv x _ hx =>
      obtain ⟨n, hn⟩ := hx
      exact ⟨n⁻¹, by rw [map_inv, Subgroup.coe_inv, hn]⟩
  obtain ⟨n, hn⟩ := key w (D.fixedWeyl_eq_closure ▸ w.2)
  exact ⟨n, Subtype.ext hn⟩

theorem ker_orbitWeylHom
    : D.orbitWeylHom.ker = D.orbitTorus.subgroupOf D.orbitMonomial := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : weylQuotientHom τ k ⟨n, D.orbitMonomial_le_monomialSubgroup n.2⟩ = 1 := by
      rw [← D.coe_orbitWeylHom, h]
      rfl
    have hmaps := mapsRootLines_weylQuotientHom
      (⟨n, D.orbitMonomial_le_monomialSubgroup n.2⟩ : monomialSubgroup τ k)
    rw [h1] at hmaps
    exact ⟨D.orbitMonomial_le_orbitGroup n.2,
      mem_torusGroup_of_mapsRootLines_one (D.orbitMonomial_le_monomialSubgroup n.2) hmaps⟩
  · intro h
    apply Subtype.ext
    rw [D.coe_orbitWeylHom, weylQuotientHom_eq (g := ⟨n, D.orbitMonomial_le_monomialSubgroup n.2⟩)
      (mapsRootLines_of_mem_torusGroup h.2)]
    rfl

@[expose] def fixedCell
    (n : ModGL τ k) : Set (ModGL τ k) :=
  (D.orbitBorel : Set (ModGL τ k)) * {n} * (D.orbitBorel : Set (ModGL τ k))

theorem mem_fixedCell
    {n g : ModGL τ k} :
    g ∈ D.fixedCell n ↔ ∃ b ∈ D.orbitBorel, ∃ b' ∈ D.orbitBorel, b * n * b' = g := by
  simp only [fixedCell, Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩
    exact ⟨b, hb, b', hb', rfl⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩

theorem fixedCell_subset_unionCell
    {n : ModGL τ k} {w : WeylGroup τ} (hn : D.IsOrbitLift n w) :
    D.fixedCell n ⊆ unionCell k D.χ D.J (rootWeylOne τ k) w := by
  intro g hg
  obtain ⟨b, hb, b', hb', rfl⟩ := D.mem_fixedCell.1 hg
  exact mem_unionCell.2 ⟨b, D.orbitBorel_le_unionBorel hb, n,
    D.mem_unionLifts_of_isOrbitLift hn, b', D.orbitBorel_le_unionBorel hb', rfl⟩

theorem fixedCell_subset_orbitGroup
    {n : ModGL τ k} {w : WeylGroup τ} (hn : D.IsOrbitLift n w) :
    D.fixedCell n ⊆ D.orbitGroup := by
  intro g hg
  obtain ⟨b, hb, b', hb', rfl⟩ := D.mem_fixedCell.1 hg
  exact mul_mem (mul_mem hb.1 (D.isOrbitLift_spec hn).1) hb'.1

theorem mem_orbitBorel_of_fixedRootSpan
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl)
    {v : adjointGroup τ k} (hv : v ∈ D.fixedRootSpan (D.inversionRootsJ w)) :
    (v : ModGL τ k) ∈ D.orbitBorel :=
  ⟨Subgroup.mem_subgroupOf.1 (D.fixedRootSpan_inversionRootsJ_le hw hv),
    Subgroup.mem_sup_right (rootSpan_le_posUnipotent (fun _ hα =>
      isRoot_height_pos_of_mem_posRoots_unionRoots hα.1) (D.mem_fixedRootSpan.1 hv).1)⟩

theorem exists_orbitBorel_mul_of_mem
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl)
    {x : adjointGroup τ k} (hx : D.IsOrbitLift (x : ModGL τ k) w) (hxF : D.F x = x)
    {c : ModGL τ k} (hc : c ∈ D.orbitGroup)
    (hcw : c ∈ unionCell k D.χ D.J (rootWeylOne τ k) w) :
    ∃ b ∈ D.orbitBorel, ∃ v ∈ D.fixedRootSpan (D.inversionRootsJ w),
      b * x * (v : ModGL τ k) = c := by
  have hcA := D.orbitGroup_le_adjointGroup hc
  have hcΓ := D.orbitGroupC_le_fixedGroup (D.mk_mem_orbitGroupC hc)
  obtain ⟨t, ht, u, hu, v, hv, e⟩ := D.fixed_factorization (g := ⟨c, hcA⟩)
    (D.mem_fixedGroup.1 hcΓ).2 (D.mem_unionWeylGroup_of_mem_fixedWeyl hw) hcw
    (D.mem_unionLifts_of_isOrbitLift hx) hxF
  have hvB := D.mem_orbitBorel_of_fixedRootSpan hw hv
  have hc' : c = (t : ModGL τ k) * u * x * v := by
    rw [show c = ((⟨c, hcA⟩ : adjointGroup τ k) : ModGL τ k) from rfl, e]
    rfl
  have hxC := (D.isOrbitLift_spec hx).1
  refine ⟨(t : ModGL τ k) * u, Subgroup.mem_inf.2 ⟨?_, ?_⟩, v, hv, by rw [hc']⟩
  · have e' : (t : ModGL τ k) * u = c * (v : ModGL τ k)⁻¹ * (x : ModGL τ k)⁻¹ := by
      rw [hc']
      group
    rw [e']
    exact mul_mem (mul_mem hc (inv_mem (Subgroup.mem_inf.1 hvB).1)) (inv_mem hxC)
  · exact mul_mem (torusGroup_le_borelGroup (unionTorus_le_torusGroup (D.mem_fixedTorus.1 ht).1))
      (Subgroup.mem_sup_right (unionUnipotent_le_posUnipotent (D.mem_fixedUnipotent.1 hu).1))

theorem bijOn_mul_fixedCell
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) {x : adjointGroup τ k}
    (hx : D.IsOrbitLift (x : ModGL τ k) w) (hxF : D.F x = x) :
    Set.BijOn (fun p : ModGL τ k × ModGL τ k => p.1 * x * p.2)
      ((D.orbitBorel : Set (ModGL τ k)) ×ˢ
        (Subtype.val '' (D.fixedRootSpan (D.inversionRootsJ w) : Set (adjointGroup τ k))))
      (D.fixedCell x) := by
  have hwJ := D.mem_unionWeylGroup_of_mem_fixedWeyl hw
  have hbij := bijOn_mul_unionCell D.rootWeylOne_union_spec hwJ
    (D.mem_unionLifts_of_isOrbitLift hx)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨b, _⟩ ⟨hb, ⟨v, hv, rfl⟩⟩
    exact D.mem_fixedCell.2 ⟨b, hb, _, D.mem_orbitBorel_of_fixedRootSpan hw hv, rfl⟩
  · rintro ⟨b, _⟩ ⟨hb, ⟨v, hv, rfl⟩⟩ ⟨b', _⟩ ⟨hb', ⟨v', hv', rfl⟩⟩ h
    refine hbij.injOn ⟨D.orbitBorel_le_unionBorel hb, ?_⟩
      ⟨D.orbitBorel_le_unionBorel hb', ?_⟩ h
    · rw [← D.inversionRootsJ_eq hwJ]
      exact (D.mem_fixedRootSpan.1 hv).1
    · rw [← D.inversionRootsJ_eq hwJ]
      exact (D.mem_fixedRootSpan.1 hv').1
  · intro g hg
    obtain ⟨b, hb, v, hv, e⟩ := D.exists_orbitBorel_mul_of_mem hw hx hxF
      (D.fixedCell_subset_orbitGroup hx hg) (D.fixedCell_subset_unionCell hx hg)
    exact ⟨(b, v), ⟨hb, ⟨v, hv, rfl⟩⟩, e⟩

theorem coe_orbitGroup_eq_iUnion
    {nw : WeylGroup τ → adjointGroup τ k}
    (hnw : ∀ w ∈ D.fixedWeyl, D.IsOrbitLift (nw w : ModGL τ k) w ∧ D.F (nw w) = nw w) :
    (D.orbitGroup : Set (ModGL τ k)) = ⋃ w ∈ D.fixedWeyl, D.fixedCell (nw w) := by
  ext c
  simp only [Set.mem_iUnion, exists_prop, SetLike.mem_coe]
  constructor
  · intro hc
    obtain ⟨w, hw, hcw⟩ := D.exists_fixedWeyl_mem_unionCell
      (D.orbitGroupC_le_fixedGroup (D.mk_mem_orbitGroupC hc))
    obtain ⟨b, hb, v, hv, e⟩ := D.exists_orbitBorel_mul_of_mem hw (hnw w hw).1 (hnw w hw).2 hc hcw
    exact ⟨w, hw, D.mem_fixedCell.2 ⟨b, hb, _, D.mem_orbitBorel_of_fixedRootSpan hw hv, e⟩⟩
  · rintro ⟨w, hw, hc⟩
    exact D.fixedCell_subset_orbitGroup (hnw w hw).1 hc

theorem disjoint_fixedCell
    {nw : WeylGroup τ → adjointGroup τ k}
    (hnw : ∀ w ∈ D.fixedWeyl, D.IsOrbitLift (nw w : ModGL τ k) w)
    {w w' : WeylGroup τ} (hw : w ∈ D.fixedWeyl) (hw' : w' ∈ D.fixedWeyl) (hne : w ≠ w') :
    Disjoint (D.fixedCell (nw w)) (D.fixedCell (nw w')) :=
  (disjoint_unionCell D.rootWeylOne_union_spec hne).mono (D.fixedCell_subset_unionCell (hnw w hw))
    (D.fixedCell_subset_unionCell (hnw w' hw'))

theorem orbitGroup_eq_closure :
    D.orbitGroup = Subgroup.closure ((D.orbitBorel : Set (ModGL τ k)) ∪
      {g | ∃ O ∈ D.orbits, g = D.orbitN O}) := by
  refine le_antisymm (fun c hc => ?_) ((Subgroup.closure_le _).2 ?_)
  · obtain ⟨w, hw, hcw⟩ := D.exists_fixedWeyl_mem_unionCell
      (D.orbitGroupC_le_fixedGroup (D.mk_mem_orbitGroupC hc))
    obtain ⟨x, hx, hxF⟩ := D.exists_fixed_lift hw
    obtain ⟨b, hb, v, hv, rfl⟩ := D.exists_orbitBorel_mul_of_mem hw hx hxF hc hcw
    refine mul_mem (mul_mem (Subgroup.subset_closure (Or.inl hb)) ?_)
      (Subgroup.subset_closure (Or.inl (D.mem_orbitBorel_of_fixedRootSpan hw hv)))
    obtain ⟨l, hl, -, hxl⟩ := hx
    rw [hxl]
    exact Subgroup.list_prod_mem _ fun y hy => by
      obtain ⟨O, hO, rfl⟩ := List.mem_map.1 hy
      exact Subgroup.subset_closure (Or.inr ⟨O, hl O hO, rfl⟩)
  · rintro _ (hb | ⟨O, hO, rfl⟩)
    · exact hb.1
    · exact D.orbitMap_mem_orbitGroup hO _

end OrthogonalSemilinearFixedRootDatum

end CFSG.LieType.Chevalley
