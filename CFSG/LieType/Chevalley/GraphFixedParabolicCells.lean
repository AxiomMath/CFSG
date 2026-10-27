module

public import CFSG.LieType.Chevalley.GraphFixedReducedWord
public import CFSG.LieType.Chevalley.GraphFixedStandardParabolic
public import CFSG.LieType.Chevalley.StandardParabolicCells

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem exists_foldedWeylEquiv_mem_parabolicWeylGroup
    {J : Set (Fin t.foldedTag.rank)}
    {w : WeylGroup t.tag} (hw : w ∈ foldedParabolicWeylGroup t J) :
    ∃ x : relWeylTwist t, (x : WeylGroup t.tag) = w ∧
      foldedWeylEquiv t x ∈ parabolicWeylGroup t.foldedTag J := by
  have hle : foldedParabolicWeylGroup t J ≤
      ((parabolicWeylGroup t.foldedTag J).comap (foldedWeylEquiv t).toMonoidHom).map
        (relWeylTwist t).subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨⟨t.orbitReflection b, t.orbitReflection_mem b⟩, ?_, rfl⟩
    change foldedWeylEquiv t ⟨t.orbitReflection b, t.orbitReflection_mem b⟩ ∈
      parabolicWeylGroup t.foldedTag J
    rw [foldedWeylEquiv_orbitReflection]
    exact Subgroup.subset_closure ⟨b, hb, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hle hw
  exact ⟨x, rfl, hx⟩

theorem orbitReflection_mem_foldedParabolicWeylGroup_iff
    {J : Set (Fin t.foldedTag.rank)}
    {a : Fin t.foldedTag.rank} : t.orbitReflection a ∈ foldedParabolicWeylGroup t J ↔ a ∈ J := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure ⟨a, h, rfl⟩⟩
  obtain ⟨x, hx, hxJ⟩ := exists_foldedWeylEquiv_mem_parabolicWeylGroup h
  have e : x = ⟨t.orbitReflection a, t.orbitReflection_mem a⟩ := Subtype.ext hx
  rw [e, foldedWeylEquiv_orbitReflection] at hxJ
  exact simple_mem_parabolicWeylGroup_iff.1 hxJ

variable (t K σ) in
@[expose] def graphFixedParabolicCells
    (J : Set (Fin t.foldedTag.rank)) : Set (ModGL t.tag K) :=
  {x | ∃ w ∈ foldedParabolicWeylGroup t J, x ∈ graphFixedRootBruhatCell t K σ w}

theorem mem_graphFixedParabolicCells
    {J : Set (Fin t.foldedTag.rank)} {x : ModGL t.tag K} :
    x ∈ graphFixedParabolicCells t K σ J ↔
      ∃ w ∈ foldedParabolicWeylGroup t J, x ∈ graphFixedRootBruhatCell t K σ w :=
  Iff.rfl

theorem canonicalRep_mem_graphFixedParabolic
    {J : Set (Fin t.foldedTag.rank)}
    {w : WeylGroup t.tag} (hw : w ∈ foldedParabolicWeylGroup t J) :
    canonicalRep (coxeterSystem t.tag) K w ∈ graphFixedParabolic t K σ J := by
  have hHP : ∀ h ∈ graphFixedRootTorus t K σ, h ∈ graphFixedParabolic t K σ J := fun h hh =>
    graphFixedRootBorel_le_graphFixedParabolic t K σ J
      (graphFixedRootTorus_le_graphFixedRootBorel hh)
  let T : Subgroup (WeylGroup t.tag) :=
    { carrier := {v | v ∈ relWeylTwist t ∧
        canonicalRep (coxeterSystem t.tag) K v ∈ graphFixedParabolic t K σ J}
      one_mem' := ⟨one_mem _, by rw [canonicalRep_one]; exact one_mem _⟩
      mul_mem' := fun {u v} hu hv => by
        refine ⟨mul_mem hu.1 hv.1, ?_⟩
        obtain ⟨h, hh, hrep⟩ := exists_canonicalRep_mul_eq (K := K) (σ := σ) hu.1 hv.1
        rw [eq_mul_inv_iff_mul_eq.2 hrep.symm]
        exact mul_mem (mul_mem hu.2 hv.2) (inv_mem (hHP h hh))
      inv_mem' := fun {v} hv => by
        refine ⟨inv_mem hv.1, ?_⟩
        obtain ⟨h, hh, hrep⟩ := exists_canonicalRep_inv_eq (K := K) (σ := σ) hv.1
        rw [eq_mul_inv_iff_mul_eq.2 hrep.symm]
        exact mul_mem (inv_mem hv.2) (inv_mem (hHP h hh)) }
  have hle : foldedParabolicWeylGroup t J ≤ T := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨t.orbitReflection_mem a, Subgroup.mem_sup_right (Subgroup.subset_closure ⟨a, ha, rfl⟩)⟩
  exact (hle hw).2

theorem graphFixedParabolicCells_subset
    (J : Set (Fin t.foldedTag.rank)) :
    graphFixedParabolicCells t K σ J ⊆ (graphFixedParabolic t K σ J : Set (ModGL t.tag K)) := by
  rintro x ⟨w, hw, hx⟩
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hx
  exact mul_mem (mul_mem (graphFixedRootBorel_le_graphFixedParabolic t K σ J hb)
    (canonicalRep_mem_graphFixedParabolic hw))
    (graphFixedRootBorel_le_graphFixedParabolic t K σ J hb')

variable (hσ : Function.Surjective σ)
include hσ

theorem canonicalRep_orbitReflection_mul_mem_graphFixedParabolicCells
    {J : Set (Fin t.foldedTag.rank)} {a : Fin t.foldedTag.rank} (ha : a ∈ J) {x : ModGL t.tag K}
    (hx : x ∈ graphFixedParabolicCells t K σ J) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * x ∈
      graphFixedParabolicCells t K σ J := by
  obtain ⟨w, hw, hxw⟩ := hx
  have hwρ := foldedParabolicWeylGroup_le t J hw
  have hrw : t.orbitReflection a * w ∈ foldedParabolicWeylGroup t J :=
    mul_mem (Subgroup.subset_closure ⟨a, ha, rfl⟩) hw
  have hmem : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * x ∈
      graphFixedRootBruhatCell t K σ (t.orbitReflection a) * graphFixedRootBruhatCell t K σ w :=
    Set.mul_mem_mul (by
      have h := mul_canonicalRep_mul_mem_graphFixedRootBruhatCell (K := K) (σ := σ)
        (w := t.orbitReflection a) (one_mem _) (one_mem _)
      rwa [one_mul, mul_one] at h) hxw
  rcases forall_height_pos_or_forall_height_neg (inv_mem hwρ) a with hp | hn
  · rw [mul_graphFixedRootBruhatCell_of_pos hσ hwρ (by simpa using hp)] at hmem
    exact ⟨_, hrw, hmem⟩
  · rw [mul_graphFixedRootBruhatCell_of_neg hσ hwρ (by simpa using hn)] at hmem
    rcases hmem with hmem | hmem
    · exact ⟨_, hrw, hmem⟩
    · exact ⟨w, hw, hmem⟩

theorem graphFixedParabolic_subset_cells
    (J : Set (Fin t.foldedTag.rank)) :
    (graphFixedParabolic t K σ J : Set (ModGL t.tag K)) ⊆ graphFixedParabolicCells t K σ J := by
  let M : Subgroup (ModGL t.tag K) :=
    { carrier := {g | (∀ x ∈ graphFixedParabolicCells t K σ J,
          g * x ∈ graphFixedParabolicCells t K σ J) ∧
        ∀ x ∈ graphFixedParabolicCells t K σ J, g⁻¹ * x ∈ graphFixedParabolicCells t K σ J}
      one_mem' := ⟨fun x hx => by rwa [one_mul], fun x hx => by rwa [inv_one, one_mul]⟩
      mul_mem' := fun {g g'} hg hg' => ⟨fun x hx => by
          rw [mul_assoc]
          exact hg.1 _ (hg'.1 x hx), fun x hx => by
          rw [mul_inv_rev, mul_assoc]
          exact hg'.2 _ (hg.2 x hx)⟩
      inv_mem' := fun {g} hg => ⟨hg.2, fun x hx => by rw [inv_inv]; exact hg.1 x hx⟩ }
  have hB : ∀ b ∈ graphFixedRootBorel t K σ, ∀ x ∈ graphFixedParabolicCells t K σ J,
      b * x ∈ graphFixedParabolicCells t K σ J := by
    rintro b hb x ⟨w, hw, hx⟩
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_graphFixedRootBruhatCell.1 hx
    refine ⟨w, hw, ?_⟩
    rw [← mul_assoc, ← mul_assoc]
    exact mul_canonicalRep_mul_mem_graphFixedRootBruhatCell (mul_mem hb hb₁) hb₂
  have hBM : graphFixedRootBorel t K σ ≤ M := fun b hb =>
    ⟨hB b hb, hB _ (inv_mem hb)⟩
  have hnM : ∀ a ∈ J, canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ M := by
    intro a ha
    refine ⟨fun x hx => canonicalRep_orbitReflection_mul_mem_graphFixedParabolicCells hσ ha hx,
      fun x hx => ?_⟩
    obtain ⟨h, hh, hinv⟩ := exists_canonicalRep_inv_eq (K := K) (σ := σ) (t.orbitReflection_mem a)
    rw [t.orbitReflection_inv] at hinv
    rw [hinv, mul_assoc]
    exact canonicalRep_orbitReflection_mul_mem_graphFixedParabolicCells hσ ha
      (hB h (graphFixedRootTorus_le_graphFixedRootBorel hh) x hx)
  have hle : graphFixedParabolic t K σ J ≤ M :=
    sup_le hBM ((Subgroup.closure_le _).2 fun _ ⟨a, ha, he⟩ => he ▸ hnM a ha)
  intro g hg
  have h1 : (1 : ModGL t.tag K) ∈ graphFixedParabolicCells t K σ J := by
    refine ⟨1, one_mem _, ?_⟩
    have h := mul_canonicalRep_mul_mem_graphFixedRootBruhatCell (K := K) (σ := σ)
      (w := (1 : WeylGroup t.tag)) (one_mem _) (one_mem _)
    rwa [canonicalRep_one, one_mul, one_mul] at h
  simpa using (hle hg).1 1 h1

theorem graphFixedParabolic_eq_cells
    (J : Set (Fin t.foldedTag.rank)) :
    (graphFixedParabolic t K σ J : Set (ModGL t.tag K)) = graphFixedParabolicCells t K σ J :=
  Set.Subset.antisymm (graphFixedParabolic_subset_cells hσ J) (graphFixedParabolicCells_subset J)

theorem canonicalRep_orbitReflection_mem_graphFixedParabolic_iff
    {J : Set (Fin t.foldedTag.rank)}
    {a : Fin t.foldedTag.rank} :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ graphFixedParabolic t K σ J ↔
      a ∈ J := by
  refine ⟨fun h => ?_, fun h => Subgroup.mem_sup_right (Subgroup.subset_closure ⟨a, h, rfl⟩)⟩
  have h' : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
      graphFixedParabolicCells t K σ J := by
    rw [← graphFixedParabolic_eq_cells hσ]
    exact h
  obtain ⟨w, hw, hmem⟩ := h'
  have hself := mul_canonicalRep_mul_mem_graphFixedRootBruhatCell (K := K) (σ := σ)
    (w := t.orbitReflection a) (one_mem _) (one_mem _)
  rw [one_mul, mul_one] at hself
  by_cases hwa : w = t.orbitReflection a
  · rw [hwa] at hw
    exact orbitReflection_mem_foldedParabolicWeylGroup_iff.1 hw
  · exact absurd hself (Set.disjoint_left.1 (disjoint_graphFixedRootBruhatCell hwa) hmem)

omit hσ

theorem fixed_standard_parabolic_cells
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K) :
    (∀ J : Set (Fin t.foldedTag.rank),
      (graphFixedParabolic t K σ.toRingHom J : Set (ModGL t.tag K)) =
        ⋃ w : foldedParabolicWeylGroup t J, graphFixedRootBruhatCell t K σ.toRingHom w) ∧
    (∀ w w' : WeylGroup t.tag, w ≠ w' →
      Disjoint (graphFixedRootBruhatCell t K σ.toRingHom w)
        (graphFixedRootBruhatCell t K σ.toRingHom w')) ∧
    (∀ (J : Set (Fin t.foldedTag.rank)) (a : Fin t.foldedTag.rank),
      canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
          graphFixedParabolic t K σ.toRingHom J ↔ a ∈ J) ∧
    (∀ J J' : Set (Fin t.foldedTag.rank),
      graphFixedParabolic t K σ.toRingHom J ≤ graphFixedParabolic t K σ.toRingHom J' ↔ J ⊆ J') ∧
    graphFixedParabolic t K σ.toRingHom ∅ = graphFixedRootBorel t K σ.toRingHom ∧
    graphFixedParabolic t K σ.toRingHom Set.univ = graphFixedRootGroup t K σ.toRingHom := by
  have hσ := σ.surjective
  refine ⟨fun J => ?_, fun _ _ h => disjoint_graphFixedRootBruhatCell h,
    fun J a => canonicalRep_orbitReflection_mem_graphFixedParabolic_iff hσ,
    fun J J' => ⟨fun h a ha => (canonicalRep_orbitReflection_mem_graphFixedParabolic_iff hσ).1
      (h ((canonicalRep_orbitReflection_mem_graphFixedParabolic_iff hσ).2 ha)),
      fun h => sup_le_sup_left (Subgroup.closure_mono (Set.image_mono h)) _⟩,
    graphFixedParabolic_empty t K σ.toRingHom, ?_⟩
  · rw [graphFixedParabolic_eq_cells hσ]
    ext x
    simp only [mem_graphFixedParabolicCells, Set.mem_iUnion, Subtype.exists, exists_prop]
  · refine le_antisymm (graphFixedParabolic_le t K σ.toRingHom Set.univ) ?_
    rw [graphFixedRootGroup_eq_sup_closure hσ, graphFixedParabolic, Set.image_univ]

end CFSG.LieType.Chevalley
