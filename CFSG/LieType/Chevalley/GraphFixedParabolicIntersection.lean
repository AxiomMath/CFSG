module

public import CFSG.LieType.Chevalley.GraphFixedParabolicCells
public import CFSG.LieType.Chevalley.GraphFixedParabolicRootFactors
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem mem_orbitUnion_iff_orbitIndex {J : Set (Fin t.foldedTag.rank)} {i : Fin t.tag.rank} :
    i ∈ t.orbitUnion J ↔ t.orbitIndex i ∈ J := by
  rw [t.mem_orbitUnion]
  exact ⟨fun ⟨a, ha, hi⟩ => ((t.mem_orbit_iff).1 hi).symm ▸ ha,
    fun h => ⟨_, h, t.mem_orbit_orbitIndex i⟩⟩

theorem orbitReflection_mem_parabolicWeylGroup
    {J : Set (Fin t.foldedTag.rank)}
    {a : Fin t.foldedTag.rank} (ha : a ∈ J) :
    t.orbitReflection a ∈ parabolicWeylGroup t.tag (t.orbitUnion J) := by
  rw [TwistTag.orbitReflection, CoxeterSystem.wordProd]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨i, (t.mem_orbitUnion).2 ⟨a, ha, (t.mem_orbitWord).1 hi⟩, rfl⟩

theorem parabolicWeylGroup_inf_relWeylTwist
    (J : Set (Fin t.foldedTag.rank)) :
    parabolicWeylGroup t.tag (t.orbitUnion J) ⊓ relWeylTwist t = foldedParabolicWeylGroup t J := by
  refine le_antisymm (fun w hw => ?_) (le_inf ((Subgroup.closure_le _).2 ?_)
    (foldedParabolicWeylGroup_le t J))
  · obtain ⟨hwA, hwρ⟩ := Subgroup.mem_inf.1 hw
    have hfix : ∀ u : Fin t.foldedTag.rank → ℤ, ∀ b ∉ J,
        (foldedWeylEquiv t ⟨w, hwρ⟩ • u) b = u b := by
      intro u b hb
      obtain ⟨i, rfl⟩ := t.exists_orbitIndex_eq b
      have hi : i ∉ t.orbitUnion J := fun h => hb (mem_orbitUnion_iff_orbitIndex.1 h)
      rw [← t.foldMap_apply_apply (foldedWeylEquiv t ⟨w, hwρ⟩ • u), ← smul_foldMap_foldedWeylEquiv,
        smul_apply_of_mem_parabolicWeylGroup hwA _ hi, t.foldMap_apply_apply]
    have hwJ := (mem_parabolicWeylGroup_of_coord _ _ rfl hfix).1
    have hle : parabolicWeylGroup t.foldedTag J ≤
        ((foldedParabolicWeylGroup t J).comap (relWeylTwist t).subtype).map
          (foldedWeylEquiv t).toMonoidHom := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨b, hb, rfl⟩
      exact ⟨⟨t.orbitReflection b, t.orbitReflection_mem b⟩,
        Subgroup.subset_closure ⟨b, hb, rfl⟩, foldedWeylEquiv_orbitReflection t b⟩
    obtain ⟨x, hx, hxw⟩ := hle hwJ
    have e : x = ⟨w, hwρ⟩ := (foldedWeylEquiv t).injective hxw
    rw [e] at hx
    exact hx
  · rintro _ ⟨a, ha, rfl⟩
    exact orbitReflection_mem_parabolicWeylGroup ha

theorem canonicalRep_orbitReflection_mem_parabolicSubgroup
    {J : Set (Fin t.foldedTag.rank)}
    {a : Fin t.foldedTag.rank} (ha : a ∈ J) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
      parabolicSubgroup t.tag K (t.orbitUnion J) := by
  rw [canonicalRep_orbitReflection]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact weylElt_mem_parabolicSubgroup ((t.mem_orbitUnion).2 ⟨a, ha, (t.mem_orbitWord).1 hi⟩)

theorem graphFixedParabolic_le_parabolicSubgroup
    (J : Set (Fin t.foldedTag.rank)) :
    graphFixedParabolic t K σ J ≤ parabolicSubgroup t.tag K (t.orbitUnion J) :=
  sup_le (fun _ hb => borelGroup_le_parabolicSubgroup _
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb).1).1)
    ((Subgroup.closure_le _).2 fun _ ⟨_, ha, he⟩ =>
      he ▸ canonicalRep_orbitReflection_mem_parabolicSubgroup ha)

theorem parabolicSubgroup_inf_graphFixedRootGroup
    (hσ : Function.Surjective σ)
    (J : Set (Fin t.foldedTag.rank)) :
    parabolicSubgroup t.tag K (t.orbitUnion J) ⊓ graphFixedRootGroup t K σ =
      graphFixedParabolic t K σ J := by
  refine le_antisymm (fun g hg => ?_) (le_inf (graphFixedParabolic_le_parabolicSubgroup J)
    (graphFixedParabolic_le t K σ J))
  obtain ⟨hgP, hgC⟩ := Subgroup.mem_inf.1 hg
  have hgC' : g ∈ (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) := hgC
  rw [graphFixedRootGroup_eq_iUnion hσ] at hgC'
  obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hgC'
  have hgB : g ∈ bruhatCell t.tag K w :=
    graphFixedBruhatCell_subset_bruhatCell w (graphFixedRootBruhatCell_subset w hgw)
  have hgP' : g ∈ parabolicCells t.tag K (t.orbitUnion J) := by
    rw [← parabolicSubgroup_eq_parabolicCells]
    exact hgP
  obtain ⟨v, hv, hgv⟩ := mem_parabolicCells.1 hgP'
  have hwv : w = v := by
    by_contra h
    exact Set.disjoint_left.1 (disjoint_bruhatCell h) hgB hgv
  have hwJ : w ∈ foldedParabolicWeylGroup t J := by
    rw [← parabolicWeylGroup_inf_relWeylTwist]
    exact Subgroup.mem_inf.2 ⟨hwv ▸ hv, hw⟩
  exact graphFixedParabolicCells_subset J ⟨w, hwJ, hgw⟩

theorem permLattice_mem_parabolicPosRoots
    {J : Set (Fin t.foldedTag.rank)}
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ parabolicPosRoots t.tag (t.orbitUnion J)) :
    permLattice t.perm α ∈ parabolicPosRoots t.tag (t.orbitUnion J) := by
  obtain ⟨⟨hr, hz⟩, -, hp⟩ := hα
  have hr' := hr.permLattice t.cartan_perm
  refine ⟨⟨hr', fun i hi => ?_⟩, hr', by rwa [height_permLattice]⟩
  have hi' : t.perm.symm i ∉ t.orbitUnion J := fun h => hi (by
    rw [mem_orbitUnion_iff_orbitIndex] at h ⊢
    rwa [← t.orbitIndex_perm, Equiv.apply_symm_apply] at h)
  exact hz _ hi'

theorem permLattice_symm_mem_parabolicPosRoots
    {J : Set (Fin t.foldedTag.rank)}
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ parabolicPosRoots t.tag (t.orbitUnion J)) :
    permLattice t.perm.symm α ∈ parabolicPosRoots t.tag (t.orbitUnion J) := by
  obtain ⟨⟨hr, hz⟩, -, hp⟩ := hα
  have hr' := hr.permLattice (cartan_perm_symm t.cartan_perm)
  refine ⟨⟨hr', fun i hi => ?_⟩, hr', by rwa [height_permLattice]⟩
  have hi' : t.perm i ∉ t.orbitUnion J := fun h => hi (by
    rw [mem_orbitUnion_iff_orbitIndex] at h ⊢
    rwa [t.orbitIndex_perm] at h)
  change α (t.perm.symm.symm i) = 0
  rw [Equiv.symm_symm]
  exact hz _ hi'

theorem weylTwist_mem_parabolicWeylGroup
    {J : Set (Fin t.foldedTag.rank)} {w : WeylGroup t.tag}
    (hw : w ∈ parabolicWeylGroup t.tag (t.orbitUnion J)) :
    weylTwist t w ∈ parabolicWeylGroup t.tag (t.orbitUnion J) := by
  have hle : parabolicWeylGroup t.tag (t.orbitUnion J) ≤
      (parabolicWeylGroup t.tag (t.orbitUnion J)).comap (weylTwist t).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    change weylTwist t (simple t.tag i) ∈ parabolicWeylGroup t.tag (t.orbitUnion J)
    rw [weylTwist_simple]
    refine Subgroup.subset_closure ⟨t.perm i, ?_, rfl⟩
    rw [mem_orbitUnion_iff_orbitIndex] at hi ⊢
    rwa [t.orbitIndex_perm]
  exact hle hw

theorem weylTwist_eq_of_image_parabolicPosRoots
    {J : Set (Fin t.foldedTag.rank)}
    {wA : WeylGroup t.tag} (hwA : wA ∈ parabolicWeylGroup t.tag (t.orbitUnion J))
    (himg : (fun α => wA • α) '' parabolicPosRoots t.tag (t.orbitUnion J) =
      (fun α => -α) '' parabolicPosRoots t.tag (t.orbitUnion J)) :
    weylTwist t wA = wA := by
  obtain ⟨-, -, -, huniq⟩ := parabolic_Weyl_coordinate_stabilizer t.tag (t.orbitUnion J)
  refine huniq.unique ⟨weylTwist_mem_parabolicWeylGroup hwA, ?_⟩ ⟨hwA, himg⟩
  have hδ : ∀ α, weylTwist t wA • α = permLattice t.perm (wA • permLattice t.perm.symm α) := by
    intro α
    rw [← weylTwist_smul_permLattice, permLattice_permLattice_symm]
  ext γ
  constructor
  · rintro ⟨α, hα, rfl⟩
    obtain ⟨β, hβ, hβe⟩ : wA • permLattice t.perm.symm α ∈
        (fun α => -α) '' parabolicPosRoots t.tag (t.orbitUnion J) :=
      himg ▸ ⟨_, permLattice_symm_mem_parabolicPosRoots hα, rfl⟩
    refine ⟨permLattice t.perm β, permLattice_mem_parabolicPosRoots hβ, ?_⟩
    simp only at hβe ⊢
    rw [hδ, ← hβe, permLattice_neg]
  · rintro ⟨β, hβ, rfl⟩
    obtain ⟨α, hα, hαe⟩ : -permLattice t.perm.symm β ∈
        (fun α => wA • α) '' parabolicPosRoots t.tag (t.orbitUnion J) :=
      himg.symm ▸ ⟨_, permLattice_symm_mem_parabolicPosRoots hβ, rfl⟩
    refine ⟨permLattice t.perm α, permLattice_mem_parabolicPosRoots hα, ?_⟩
    simp only at hαe ⊢
    rw [hδ, permLattice_symm_permLattice, hαe, permLattice_neg, permLattice_permLattice_symm]

theorem diagram_fixed_parabolic_intersection
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K)
    (J : Set (Fin t.foldedTag.rank)) :
    parabolicWeylGroup t.tag (t.orbitUnion J) ⊓ relWeylTwist t = foldedParabolicWeylGroup t J ∧
    parabolicSubgroup t.tag K (t.orbitUnion J) ⊓ graphFixedRootGroup t K σ.toRingHom =
      graphFixedParabolic t K σ.toRingHom J ∧
    parabolicLevi t.tag K (t.orbitUnion J) ⊓ graphFixedParabolic t K σ.toRingHom J =
      graphFixedParabolicLevi t K σ.toRingHom J ⊓ graphFixedParabolic t K σ.toRingHom J ∧
    (∃! wA : WeylGroup t.tag, wA ∈ parabolicWeylGroup t.tag (t.orbitUnion J) ∧
      (fun α => wA • α) '' parabolicPosRoots t.tag (t.orbitUnion J) =
        (fun α => -α) '' parabolicPosRoots t.tag (t.orbitUnion J)) ∧
    ∀ wA ∈ parabolicWeylGroup t.tag (t.orbitUnion J),
      (fun α => wA • α) '' parabolicPosRoots t.tag (t.orbitUnion J) =
          (fun α => -α) '' parabolicPosRoots t.tag (t.orbitUnion J) →
        weylTwist t wA = wA ∧
        canonicalRep (coxeterSystem t.tag) K wA ∈
          parabolicLevi t.tag K (t.orbitUnion J) ⊓ graphFixedParabolic t K σ.toRingHom J ∧
        canonicalRep (coxeterSystem t.tag) K wA ∈
          Subgroup.normalizer (torusGroup t.tag K : Set (ModGL t.tag K)) ∧
        (parabolicLeviUnipotent t.tag K (t.orbitUnion J)).map
            (MulAut.conj (canonicalRep (coxeterSystem t.tag) K wA)).toMonoidHom =
          rootSpan t.tag K ((fun α => -α) '' parabolicPosRoots t.tag (t.orbitUnion J)) := by
  obtain ⟨-, -, -, huniq⟩ := parabolic_Weyl_coordinate_stabilizer t.tag (t.orbitUnion J)
  have hPC : graphFixedParabolic t K σ.toRingHom J ≤ graphFixedRootGroup t K σ.toRingHom :=
    graphFixedParabolic_le t K σ.toRingHom J
  refine ⟨parabolicWeylGroup_inf_relWeylTwist J,
    parabolicSubgroup_inf_graphFixedRootGroup σ.surjective J, ?_, huniq,
    fun wA hwA himg => ?_⟩
  · rw [graphFixedParabolicLevi, inf_assoc, inf_eq_right.2 hPC]
  · have hδ := weylTwist_eq_of_image_parabolicPosRoots hwA himg
    have hwJ : wA ∈ foldedParabolicWeylGroup t J := by
      rw [← parabolicWeylGroup_inf_relWeylTwist]
      exact Subgroup.mem_inf.2 ⟨hwA, (mem_relWeylTwist t).2 hδ⟩
    refine ⟨hδ, Subgroup.mem_inf.2 ⟨canonicalRep_mem_parabolicLevi hwA,
      canonicalRep_mem_graphFixedParabolic hwJ⟩, (canonical_weyl_root_transport t.tag K).2.2 wA,
      ?_⟩
    rw [parabolicLeviUnipotent, (canonical_weyl_root_transport t.tag K).1 wA _
      fun α hα => hα.2.1, himg]

end CFSG.LieType.Chevalley
