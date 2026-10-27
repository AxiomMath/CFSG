module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LeviCatalogueCommutator
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LeviCatalogueParabolic
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootDefs
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot
open scoped commutatorElement

theorem C2E6Std_setA_eq_E6GraphLevi_setA :
    (C2E6Std.setA : Set (Fin TwistTag.E6.tag.rank)) = E6GraphLevi.setA := by
  ext i
  show i ∈ ({0, 2, 3, 4, 5} : Set (Fin 6)) ↔ i ∈ {j : Fin 6 | j ≠ 1}
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  revert i
  decide

section Word


@[expose] def twE6LeviHighestRootWord : List (Fin TwistTag.E6.foldedTag.rank) :=
  [3, 2, 1, 0, 2, 1, 2]

@[expose] def twE6LeviHighestRootWeyl : WeylGroup TwistTag.E6.tag :=
  (twE6LeviHighestRootWord.map TwistTag.E6.orbitReflection).prod

private theorem prod_orbitReflection_smul (l : List (Fin TwistTag.E6.foldedTag.rank))
    (v : Fin TwistTag.E6.tag.rank → ℤ) :
    (l.map TwistTag.E6.orbitReflection).prod • v =
      l.foldr (fun a w => (TwistTag.E6.orbitWord a).foldr (reflect TwistTag.E6.tag) w) v := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, mul_smul, ih, TwistTag.E6.orbitReflection_smul]

theorem twE6LeviHighestRootWeyl_smul :
    twE6LeviHighestRootWeyl • (Pi.single 1 1 : Fin TwistTag.E6.tag.rank → ℤ) = e6HighestRoot := by
  rw [twE6LeviHighestRootWeyl, prod_orbitReflection_smul]
  decide +kernel

theorem twE6LeviHighestRootWeyl_mem : twE6LeviHighestRootWeyl ∈ relWeylTwist TwistTag.E6 :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact TwistTag.E6.orbitReflection_mem a

variable {K : Type} [Field K]

private theorem xUnit_one_mem_graphFixedRootGroup (σ : K →+* K) :
    xUnit TwistTag.E6.tag K 1 1 ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have hP : xUnit TwistTag.E6.tag K 1 1 ∈ posUnipotent TwistTag.E6.tag K :=
    xUnit_mem_posUnipotent 1 1
  have hΓ : xUnit TwistTag.E6.tag K 1 1 ∈ twistedFixedGroup TwistTag.E6 K σ := by
    rw [mem_twistedFixedGroup_iff_twistHom]
    refine ⟨xUnit_mem_adjointGroup _ _, ?_⟩
    rw [twistHom_xUnit]
    have : TwistTag.E6.perm 1 = 1 := by decide
    rw [this, map_one]
  exact graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (Subgroup.mem_inf.2 ⟨hP, hΓ⟩)

private theorem yUnit_one_mem_graphFixedRootGroup (σ : K →+* K) :
    yUnit TwistTag.E6.tag K 1 1 ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have hP : yUnit TwistTag.E6.tag K 1 1 ∈ negUnipotent TwistTag.E6.tag K :=
    yUnit_mem_negUnipotent 1 1
  have hΓ : yUnit TwistTag.E6.tag K 1 1 ∈ twistedFixedGroup TwistTag.E6 K σ := by
    rw [mem_twistedFixedGroup_iff_twistHom]
    refine ⟨yUnit_mem_adjointGroup _ _, ?_⟩
    rw [twistHom_yUnit]
    have : TwistTag.E6.perm 1 = 1 := by decide
    rw [this, map_one]
  exact graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ (Subgroup.mem_inf.2 ⟨hP, hΓ⟩)

end Word

section Fixed


variable {K : Type} [Field K]

theorem exists_ne_one_mem_graphFixedRootGroup_inf_rootSubgroup (σ : K →+* K) :
    (∃ u ∈ graphFixedRootGroup TwistTag.E6 K σ,
      u ∈ rootSubgroup TwistTag.E6.tag K e6HighestRoot ∧ u ≠ 1) ∧
    ∃ v ∈ graphFixedRootGroup TwistTag.E6 K σ,
      v ∈ rootSubgroup TwistTag.E6.tag K (-e6HighestRoot) ∧ v ≠ 1 := by
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) K twE6LeviHighestRootWeyl with hn_def
  have hn : n ∈ graphFixedRootGroup TwistTag.E6 K σ :=
    canonicalRep_mem_graphFixedRootGroup twE6LeviHighestRootWeyl_mem
  have hconj : ∀ x : ModGL TwistTag.E6.tag K, n * x * n⁻¹ = 1 → x = 1 := fun x h => by
    have e : x = n⁻¹ * (n * x * n⁻¹) * n := by group
    rw [e, h]
    group
  refine ⟨⟨n * xUnit TwistTag.E6.tag K 1 1 * n⁻¹,
    mul_mem (mul_mem hn (xUnit_one_mem_graphFixedRootGroup σ)) (inv_mem hn), ?_, fun h => ?_⟩,
    ⟨n * yUnit TwistTag.E6.tag K 1 1 * n⁻¹,
    mul_mem (mul_mem hn (yUnit_one_mem_graphFixedRootGroup σ)) (inv_mem hn), ?_, fun h => ?_⟩⟩
  · have h := (canonical_weyl_root_transport TwistTag.E6.tag K).2.1 twE6LeviHighestRootWeyl
      (Pi.single 1 1) (isRoot_single _ _)
    rw [twE6LeviHighestRootWeyl_smul] at h
    rw [← h]
    exact Subgroup.mem_map_of_mem _ (mem_rootSubgroup.2 ⟨1, pinnedX_single _ _ _ _⟩)
  · have h1 := hconj _ h
    rw [← pinnedX_single, ← pinnedX_zero TwistTag.E6.tag K (Pi.single 1 1)] at h1
    exact one_ne_zero (pinnedX_injective _ _ _ h1)
  · have h := (canonical_weyl_root_transport TwistTag.E6.tag K).2.1 twE6LeviHighestRootWeyl
      (-Pi.single 1 1) (isRoot_neg_single _ _)
    rw [smul_neg, twE6LeviHighestRootWeyl_smul] at h
    rw [← h]
    exact Subgroup.mem_map_of_mem _ (mem_rootSubgroup.2 ⟨1, pinnedX_neg_single _ _ _ _⟩)
  · have h1 := hconj _ h
    rw [← pinnedX_neg_single, ← pinnedX_zero TwistTag.E6.tag K (-Pi.single 1 1)] at h1
    exact one_ne_zero (pinnedX_injective _ _ _ h1)

theorem subsystemGroup_le_centralizer_rootSubgroup_e6HighestRoot :
    subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≤
      Subgroup.centralizer (rootSubgroup TwistTag.E6.tag K e6HighestRoot :
        Set (ModGL TwistTag.E6.tag K)) := by
  rw [subsystemGroup, Subgroup.closure_le]
  rintro _ ⟨i, hi, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hu
    rw [← pinnedX_single]
    exact (E6GraphLevi.commute_simple_theta hi true true c d).symm.eq
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hu
    rw [← pinnedX_neg_single]
    exact (E6GraphLevi.commute_simple_theta hi false true c d).symm.eq

theorem subsystemGroup_le_centralizer_rootSubgroup_neg_e6HighestRoot :
    subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≤
      Subgroup.centralizer (rootSubgroup TwistTag.E6.tag K (-e6HighestRoot) :
        Set (ModGL TwistTag.E6.tag K)) := by
  rw [subsystemGroup, Subgroup.closure_le]
  rintro _ ⟨i, hi, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hu
    rw [← pinnedX_single]
    exact (E6GraphLevi.commute_simple_theta hi true false c d).symm.eq
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hu
    rw [← pinnedX_neg_single]
    exact (E6GraphLevi.commute_simple_theta hi false false c d).symm.eq

variable [Finite K] (σ : K ≃+* K)

theorem coe_mem_parabolicLevi_of_mem_centralizer_twE6LongRootSL2 {g : twistedE6RootGroup K σ}
    (hg : g ∈ Subgroup.centralizer (twE6LongRootSL2 (twE6RootSubgroup K σ e6HighestRoot)
      (twE6RootSubgroup K σ (-e6HighestRoot)) : Set (twistedE6RootGroup K σ))) :
    (g : ModGL TwistTag.E6.tag K) ∈ parabolicLevi TwistTag.E6.tag K E6GraphLevi.setA := by
  obtain ⟨⟨u, huG, hu, hu1⟩, ⟨v, hvG, hv, hv1⟩⟩ :=
    exists_ne_one_mem_graphFixedRootGroup_inf_rootSubgroup (K := K) σ.toRingHom
  have hgA : (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K :=
    (graphFixedRootGroup_le _ _ _ g.2).1
  refine mem_parabolicLevi_of_commute_rootElements hgA hu hu1 hv hv1 ?_ ?_
  · have h := Subgroup.mem_centralizer_iff.1 hg ⟨u, huG⟩ (Subgroup.subset_closure (Or.inl hu))
    have h' : u * (g : ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag K) * u :=
      congrArg Subtype.val h
    rw [← h']
    group
  · have h := Subgroup.mem_centralizer_iff.1 hg ⟨v, hvG⟩ (Subgroup.subset_closure (Or.inr hv))
    have h' : v * (g : ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag K) * v :=
      congrArg Subtype.val h
    rw [← h']
    group

theorem mem_centralizer_twE6LongRootSL2_of_coe_mem_subsystemGroup {x : twistedE6RootGroup K σ}
    (hx : (x : ModGL TwistTag.E6.tag K) ∈ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA) :
    x ∈ Subgroup.centralizer (twE6LongRootSL2 (twE6RootSubgroup K σ e6HighestRoot)
      (twE6RootSubgroup K σ (-e6HighestRoot)) : Set (twistedE6RootGroup K σ)) := by
  unfold twE6LongRootSL2
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro y (hy | hy)
  · exact Subtype.ext (Subgroup.mem_centralizer_iff.1
      (subsystemGroup_le_centralizer_rootSubgroup_e6HighestRoot hx) _ hy)
  · exact Subtype.ext (Subgroup.mem_centralizer_iff.1
      (subsystemGroup_le_centralizer_rootSubgroup_neg_e6HighestRoot hx) _ hy)

theorem twE6RootSubgroup_ne_bot :
    twE6RootSubgroup K σ e6HighestRoot ≠ ⊥ ∧ twE6RootSubgroup K σ (-e6HighestRoot) ≠ ⊥ := by
  obtain ⟨⟨u, huG, hu, hu1⟩, ⟨v, hvG, hv, hv1⟩⟩ :=
    exists_ne_one_mem_graphFixedRootGroup_inf_rootSubgroup (K := K) σ.toRingHom
  refine ⟨fun h => hu1 ?_, fun h => hv1 ?_⟩
  · have hmem : (⟨u, huG⟩ : twistedE6RootGroup K σ) ∈ twE6RootSubgroup K σ e6HighestRoot := hu
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · have hmem : (⟨v, hvG⟩ : twistedE6RootGroup K σ) ∈ twE6RootSubgroup K σ (-e6HighestRoot) := hv
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem

theorem twE6LongRootLevi_le_comap :
    twE6LongRootLevi (twE6RootSubgroup K σ e6HighestRoot) (twE6RootSubgroup K σ (-e6HighestRoot)) ≤
      (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊓
        twistedFixedGroup TwistTag.E6 K σ.toRingHom).comap (twistedE6RootGroup K σ).subtype := by
  unfold twE6LongRootLevi
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have h₁ := coe_mem_parabolicLevi_of_mem_centralizer_twE6LongRootSL2 σ hg₁
  have h₂ := coe_mem_parabolicLevi_of_mem_centralizer_twE6LongRootSL2 σ hg₂
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · exact commutator_parabolicLevi_le_subsystemGroup _ (Subgroup.commutator_mem_commutator h₁ h₂)
  · exact graphFixedRootGroup_le _ _ _ (⁅g₁, g₂⁆ : twistedE6RootGroup K σ).2

theorem twE6LongRootLevi_eq_subsystem {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hperf : ⁅subsystemGroup Tag.E6 K C2E6Std.setA ⊓ twistedFixedGroup TwistTag.E6 K σ.toRingHom,
      subsystemGroup Tag.E6 K C2E6Std.setA ⊓ twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ =
        subsystemGroup Tag.E6 K C2E6Std.setA ⊓ twistedFixedGroup TwistTag.E6 K σ.toRingHom) :
    subsystemGroup Tag.E6 K C2E6Std.setA ⊓ twistedFixedGroup TwistTag.E6 K σ.toRingHom ≤
        graphFixedRootGroup TwistTag.E6 K σ.toRingHom ∧
      twE6LongRootLevi (twE6RootSubgroup K σ e6HighestRoot)
          (twE6RootSubgroup K σ (-e6HighestRoot)) =
        (subsystemGroup Tag.E6 K C2E6Std.setA ⊓ twistedFixedGroup TwistTag.E6 K σ.toRingHom).comap
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype := by
  rw [C2E6Std_setA_eq_E6GraphLevi_setA] at hperf ⊢
  have hΓ := (finite_fixed_root_group_perfect TwistTag.E6 hp hf K hK σ.toRingHom hσ).2.2.1
  have hSG : subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊓
      twistedFixedGroup TwistTag.E6 K σ.toRingHom ≤
        graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
    have h := Subgroup.commutator_mono
      (inf_le_right : subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊓
        twistedFixedGroup TwistTag.E6 K σ.toRingHom ≤ twistedFixedGroup TwistTag.E6 K σ.toRingHom)
      (inf_le_right : subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊓
        twistedFixedGroup TwistTag.E6 K σ.toRingHom ≤ twistedFixedGroup TwistTag.E6 K σ.toRingHom)
    exact hperf.symm.le.trans (h.trans hΓ.le)
  refine ⟨hSG, le_antisymm (twE6LongRootLevi_le_comap σ) ?_⟩
  set T := (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊓
    twistedFixedGroup TwistTag.E6 K σ.toRingHom).comap (twistedE6RootGroup K σ).subtype with hT
  have hmap : T.map (twistedE6RootGroup K σ).subtype =
      subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊓
        twistedFixedGroup TwistTag.E6 K σ.toRingHom := by
    rw [hT, Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_eq_right.2 hSG
  have hTT : ⁅T, T⁆ = T := by
    apply Subgroup.map_injective (twistedE6RootGroup K σ).subtype_injective
    rw [Subgroup.map_commutator, hmap]
    exact hperf
  have hTC : T ≤ Subgroup.centralizer (twE6LongRootSL2 (twE6RootSubgroup K σ e6HighestRoot)
      (twE6RootSubgroup K σ (-e6HighestRoot)) : Set (twistedE6RootGroup K σ)) := fun x hx =>
    mem_centralizer_twE6LongRootSL2_of_coe_mem_subsystemGroup σ (Subgroup.mem_inf.1 hx).1
  have h := Subgroup.commutator_mono hTC hTC
  rw [hTT] at h
  exact h

end Fixed

end CFSG.LieType.SeitzGeneration.ExcWideThree
