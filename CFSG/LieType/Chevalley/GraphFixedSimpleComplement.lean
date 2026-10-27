module

public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

section TwoBlocks

variable {τ : Tag} (R : Type) [CommRing R]

theorem list_map_prod_pinnedX_mem_rootSpan
    {S : Set (Fin τ.rank → ℤ)} {l : List (Fin τ.rank → ℤ)}
    (hl : ∀ α ∈ l, α ∈ S) (c : (Fin τ.rank → ℤ) → R) :
    (l.map fun α => pinnedX τ R α (c α)).prod ∈ rootSpan τ R S :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem (hl α hα)
      (Subgroup.subset_closure ⟨c α, rfl⟩))

theorem exists_list_of_finite {S : Set (Fin τ.rank → ℤ)} (hS : S.Finite) :
    ∃ l : List (Fin τ.rank → ℤ), l.Nodup ∧ ∀ α, α ∈ l ↔ α ∈ S :=
  ⟨hS.toFinset.toList, Finset.nodup_toList _, fun α => by
    rw [Finset.mem_toList, Set.Finite.mem_toFinset]⟩

variable {S₁ S₂ : Set (Fin τ.rank → ℤ)}
  (hS₁ : ∀ α ∈ S₁, IsRoot τ α ∧ 0 < height α) (hS₂ : ∀ α ∈ S₂, IsRoot τ α ∧ 0 < height α)
  (hdisj : Disjoint S₁ S₂)
include hS₁ hS₂ hdisj

theorem exists_mul_rootSpan_eq
    (hclosed : ∀ α ∈ S₁ ∪ S₂, ∀ β ∈ S₁ ∪ S₂, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • α + b • β) → a • α + b • β ∈ S₁ ∪ S₂)
    {g : (Module.End R (RootModule τ R))ˣ} (hg : g ∈ rootSpan τ R (S₁ ∪ S₂)) :
    ∃ u₁ ∈ rootSpan τ R S₁, ∃ u₂ ∈ rootSpan τ R S₂, u₁ * u₂ = g := by
  obtain ⟨l₁, hl₁, hm₁⟩ := exists_list_of_finite
    ((finite_setOf_isRoot τ).subset fun α hα => (hS₁ α hα).1)
  obtain ⟨l₂, hl₂, hm₂⟩ := exists_list_of_finite
    ((finite_setOf_isRoot τ).subset fun α hα => (hS₂ α hα).1)
  have hnd : (l₁ ++ l₂).Nodup := List.nodup_append.2 ⟨hl₁, hl₂, fun α h₁ β h₂ h =>
    Set.disjoint_left.1 hdisj ((hm₁ α).1 h₁) (h ▸ (hm₂ β).1 h₂)⟩
  have hS : ∀ α ∈ S₁ ∪ S₂, IsRoot τ α ∧ 0 < height α := fun α hα =>
    hα.elim (hS₁ α) (hS₂ α)
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq R hS hclosed hnd
    (fun α => by rw [List.mem_append, hm₁, hm₂, Set.mem_union]) hg
  rw [List.map_append, List.prod_append] at hc
  exact ⟨_, list_map_prod_pinnedX_mem_rootSpan R (fun α hα => (hm₁ α).1 hα) c, _,
    list_map_prod_pinnedX_mem_rootSpan R (fun α hα => (hm₂ α).1 hα) c, hc⟩

theorem eq_of_mul_rootSpan_eq
    (hcl₁ : ∀ α ∈ S₁, ∀ β ∈ S₁, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S₁)
    (hcl₂ : ∀ α ∈ S₂, ∀ β ∈ S₂, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S₂)
    {u₁ u₁' u₂ u₂' : (Module.End R (RootModule τ R))ˣ} (hu₁ : u₁ ∈ rootSpan τ R S₁)
    (hu₁' : u₁' ∈ rootSpan τ R S₁) (hu₂ : u₂ ∈ rootSpan τ R S₂) (hu₂' : u₂' ∈ rootSpan τ R S₂)
    (h : u₁ * u₂ = u₁' * u₂') : u₁ = u₁' ∧ u₂ = u₂' := by
  classical
  obtain ⟨l₁, hl₁, hm₁⟩ := exists_list_of_finite
    ((finite_setOf_isRoot τ).subset fun α hα => (hS₁ α hα).1)
  obtain ⟨l₂, hl₂, hm₂⟩ := exists_list_of_finite
    ((finite_setOf_isRoot τ).subset fun α hα => (hS₂ α hα).1)
  obtain ⟨c₁, hc₁⟩ := exists_list_prod_pinnedX_eq R hS₁ hcl₁ hl₁ hm₁ hu₁
  obtain ⟨c₁', hc₁'⟩ := exists_list_prod_pinnedX_eq R hS₁ hcl₁ hl₁ hm₁ hu₁'
  obtain ⟨c₂, hc₂⟩ := exists_list_prod_pinnedX_eq R hS₂ hcl₂ hl₂ hm₂ hu₂
  obtain ⟨c₂', hc₂'⟩ := exists_list_prod_pinnedX_eq R hS₂ hcl₂ hl₂ hm₂ hu₂'
  have hnd : (l₁ ++ l₂).Nodup := List.nodup_append.2 ⟨hl₁, hl₂, fun α h₁ β h₂ h =>
    Set.disjoint_left.1 hdisj ((hm₁ α).1 h₁) (h ▸ (hm₂ β).1 h₂)⟩
  have hcomb : ∀ d₁ d₂ : (Fin τ.rank → ℤ) → R, ∃ c : (Fin τ.rank → ℤ) → R,
      (∀ α ∈ S₁, c α = d₁ α) ∧ ∀ α ∈ S₂, c α = d₂ α := fun d₁ d₂ =>
    ⟨fun α => if α ∈ S₁ then d₁ α else d₂ α, fun α hα => ite_eq_left_iff.2 fun h => absurd hα h,
      fun α hα => ite_eq_right_iff.2 fun h => absurd h (Set.disjoint_right.1 hdisj hα)⟩
  obtain ⟨c, hcS₁, hcS₂⟩ := hcomb c₁ c₂
  obtain ⟨c', hcS₁', hcS₂'⟩ := hcomb c₁' c₂'
  have e : ∀ (l : List (Fin τ.rank → ℤ)) (d d' : (Fin τ.rank → ℤ) → R), (∀ α ∈ l, d α = d' α) →
      (l.map fun α => pinnedX τ R α (d α)).prod = (l.map fun α => pinnedX τ R α (d' α)).prod :=
    fun l d d' h => congrArg List.prod (List.map_congr_left fun α hα => by rw [h α hα])
  have hu₁c : (l₁.map fun α => pinnedX τ R α (c α)).prod = u₁ := by
    rw [← hc₁]
    exact e l₁ c c₁ fun α hα => hcS₁ α ((hm₁ α).1 hα)
  have hu₁c' : (l₁.map fun α => pinnedX τ R α (c' α)).prod = u₁' := by
    rw [← hc₁']
    exact e l₁ c' c₁' fun α hα => hcS₁' α ((hm₁ α).1 hα)
  have hu₂c : (l₂.map fun α => pinnedX τ R α (c α)).prod = u₂ := by
    rw [← hc₂]
    exact e l₂ c c₂ fun α hα => hcS₂ α ((hm₂ α).1 hα)
  have hu₂c' : (l₂.map fun α => pinnedX τ R α (c' α)).prod = u₂' := by
    rw [← hc₂']
    exact e l₂ c' c₂' fun α hα => hcS₂' α ((hm₂ α).1 hα)
  have hL : ∀ α ∈ l₁ ++ l₂, IsRoot τ α ∧ 0 < height α := fun α hα =>
    (List.mem_append.1 hα).elim (fun h => hS₁ α ((hm₁ α).1 h)) fun h => hS₂ α ((hm₂ α).1 h)
  have heq := pinnedX_list_prod_injective (l₁ ++ l₂) hnd hL c c' (by
    rw [List.map_append, List.prod_append, List.map_append, List.prod_append, hu₁c, hu₂c, hu₁c',
      hu₂c', h])
  refine ⟨?_, ?_⟩
  · rw [← hu₁c, ← hu₁c']
    exact e l₁ c c' fun α hα => heq α (List.mem_append_left _ hα)
  · rw [← hu₂c, ← hu₂c']
    exact e l₂ c c' fun α hα => heq α (List.mem_append_right _ hα)

end TwoBlocks

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem twistHom_mem_rootSpan
    (hσ : Function.Surjective σ) {S : Set (Fin t.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot t.tag α) (hSρ : ∀ α ∈ S, permLattice t.perm α ∈ S)
    {g : ModGL t.tag K} (hg : g ∈ rootSpan t.tag K S) : twistHom t K σ g ∈ rootSpan t.tag K S := by
  have h := Subgroup.mem_map_of_mem (twistHom t K σ) hg
  rw [map_twistHom_rootSpan t K hσ hS] at h
  exact rootSpan_mono (by rintro _ ⟨β, hβ, rfl⟩; exact hSρ β hβ) h

variable {S₁ S₂ : Set (Fin t.tag.rank → ℤ)}
  (hS₁ : ∀ α ∈ S₁, IsRoot t.tag α ∧ 0 < height α) (hS₂ : ∀ α ∈ S₂, IsRoot t.tag α ∧ 0 < height α)
  (hdisj : Disjoint S₁ S₂)
  (hcl₁ : ∀ α ∈ S₁, ∀ β ∈ S₁, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot t.tag (a • α + b • β) →
    a • α + b • β ∈ S₁)
  (hcl₂ : ∀ α ∈ S₂, ∀ β ∈ S₂, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot t.tag (a • α + b • β) →
    a • α + b • β ∈ S₂)
include hS₁ hS₂ hdisj hcl₁ hcl₂

theorem exists_mul_graphFixed_eq
    (hσ : Function.Surjective σ)
    (hρ₁ : ∀ α ∈ S₁, permLattice t.perm α ∈ S₁) (hρ₂ : ∀ α ∈ S₂, permLattice t.perm α ∈ S₂)
    (hclosed : ∀ α ∈ S₁ ∪ S₂, ∀ β ∈ S₁ ∪ S₂, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot t.tag (a • α + b • β) → a • α + b • β ∈ S₁ ∪ S₂)
    {g : ModGL t.tag K} (hg : g ∈ rootSpan t.tag K (S₁ ∪ S₂) ⊓ twistedFixedGroup t K σ) :
    ∃ u₁ ∈ rootSpan t.tag K S₁ ⊓ twistedFixedGroup t K σ,
      ∃ u₂ ∈ rootSpan t.tag K S₂ ⊓ twistedFixedGroup t K σ, u₁ * u₂ = g := by
  obtain ⟨hgS, hgΓ⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := exists_mul_rootSpan_eq K hS₁ hS₂ hdisj hclosed hgS
  have hfix := ((mem_twistedFixedGroup_iff_twistHom t K σ).1 hgΓ).2
  rw [map_mul] at hfix
  obtain ⟨h₁, h₂⟩ := eq_of_mul_rootSpan_eq K hS₁ hS₂ hdisj hcl₁ hcl₂
    (twistHom_mem_rootSpan hσ (fun α hα => (hS₁ α hα).1) hρ₁ hu₁) hu₁
    (twistHom_mem_rootSpan hσ (fun α hα => (hS₂ α hα).1) hρ₂ hu₂) hu₂ hfix
  exact ⟨u₁, Subgroup.mem_inf.2 ⟨hu₁, (mem_twistedFixedGroup_iff_twistHom t K σ).2
      ⟨rootSpan_le_adjointGroup K _ hu₁, h₁⟩⟩,
    u₂, Subgroup.mem_inf.2 ⟨hu₂, (mem_twistedFixedGroup_iff_twistHom t K σ).2
      ⟨rootSpan_le_adjointGroup K _ hu₂, h₂⟩⟩, rfl⟩

omit hcl₁ hcl₂ hS₁ hS₂ hdisj

variable (t) in
@[expose] def simpleOrbitRoots (a : Fin t.foldedTag.rank) : Set (Fin t.tag.rank → ℤ) :=
  (fun i => (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)

variable (t) in
@[expose] def simpleComplementRoots (a : Fin t.foldedTag.rank) : Set (Fin t.tag.rank → ℤ) :=
  {α | IsRoot t.tag α ∧ 0 < height α} \ simpleOrbitRoots t a

variable (t K σ) in
@[expose] def graphFixedSimpleComplement
    (a : Fin t.foldedTag.rank) : Subgroup (ModGL t.tag K) :=
  rootSpan t.tag K (simpleComplementRoots t a) ⊓ twistedFixedGroup t K σ

theorem simpleOrbitRoots_pos
    (a : Fin t.foldedTag.rank) :
    ∀ α ∈ simpleOrbitRoots t a, IsRoot t.tag α ∧ 0 < height α := by
  rintro _ ⟨i, -, rfl⟩
  exact ⟨isRoot_single _ i, by rw [height_single]; exact one_pos⟩

theorem simpleComplementRoots_pos (a : Fin t.foldedTag.rank) :
    ∀ α ∈ simpleComplementRoots t a, IsRoot t.tag α ∧ 0 < height α :=
  fun _ h => h.1

theorem disjoint_simpleComplementRoots (a : Fin t.foldedTag.rank) :
    Disjoint (simpleComplementRoots t a) (simpleOrbitRoots t a) :=
  Set.disjoint_sdiff_left

theorem simpleComplementRoots_union
    (a : Fin t.foldedTag.rank) :
    simpleComplementRoots t a ∪ simpleOrbitRoots t a = {α | IsRoot t.tag α ∧ 0 < height α} :=
  Set.sdiff_union_of_subset fun α h => simpleOrbitRoots_pos a α h

theorem nsmul_add_nsmul_mem_simpleComplementRoots
    (a : Fin t.foldedTag.rank)
    {α β : Fin t.tag.rank → ℤ} (hα : 0 < height α) (hβ : 0 < height β) {m n : ℕ} (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hr : IsRoot t.tag (m • α + n • β)) :
    m • α + n • β ∈ simpleComplementRoots t a := by
  have hh : 2 ≤ height (m • α + n • β) := by
    rw [height_nsmul_add_nsmul]
    have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
  refine ⟨⟨hr, by omega⟩, ?_⟩
  rintro ⟨i, -, hi⟩
  rw [← hi, height_single] at hh
  omega

theorem simpleComplementRoots_closed
    (a : Fin t.foldedTag.rank) :
    ∀ α ∈ simpleComplementRoots t a, ∀ β ∈ simpleComplementRoots t a, ∀ m n : ℕ, 1 ≤ m →
      1 ≤ n → IsRoot t.tag (m • α + n • β) → m • α + n • β ∈ simpleComplementRoots t a :=
  fun _ hα _ hβ _ _ hm hn hr =>
    nsmul_add_nsmul_mem_simpleComplementRoots a hα.1.2 hβ.1.2 hm hn hr

theorem simpleOrbitRoots_eq (a : Fin t.foldedTag.rank) :
    simpleOrbitRoots t a = (t.diagramOrbit (Pi.single (t.orbitMin a) 1) : Set _) := by
  rw [t.diagramOrbit_single, t.orbitIndex_orbitMin, Finset.coe_image]
  rfl

theorem simpleOrbitRoots_closed
    (a : Fin t.foldedTag.rank) :
    ∀ α ∈ simpleOrbitRoots t a, ∀ β ∈ simpleOrbitRoots t a, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      IsRoot t.tag (m • α + n • β) → m • α + n • β ∈ simpleOrbitRoots t a := by
  intro α hα β hβ m n hm hn hr
  rw [simpleOrbitRoots_eq] at hα hβ
  exact absurd hr (t.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit (isRoot_single _ _) hα hβ hm hn)

theorem simpleOrbitRoots_perm (a : Fin t.foldedTag.rank) :
    ∀ α ∈ simpleOrbitRoots t a, permLattice t.perm α ∈ simpleOrbitRoots t a := by
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨t.perm i, t.perm_mem_orbit hi, (permLattice_single _ i).symm⟩

theorem simpleComplementRoots_perm
    (a : Fin t.foldedTag.rank) :
    ∀ α ∈ simpleComplementRoots t a, permLattice t.perm α ∈ simpleComplementRoots t a := by
  rintro α ⟨hα, hαE⟩
  refine ⟨?_, fun h => hαE ?_⟩
  · rw [← image_permLattice_posRoots t]
    exact ⟨α, hα, rfl⟩
  · obtain ⟨i, hi, hiα⟩ := h
    refine ⟨t.perm.symm i, t.perm_symm_mem_orbit hi, ?_⟩
    dsimp only at hiα ⊢
    rw [← permLattice_single, hiα, permLattice_symm_permLattice]

theorem orbitReflection_smul_mem_simpleComplementRoots
    {a : Fin t.foldedTag.rank}
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ simpleComplementRoots t a) :
    t.orbitReflection a • α ∈ simpleComplementRoots t a := by
  obtain ⟨⟨hαr, hαp⟩, hαE⟩ := hα
  have hr := IsRoot.smul hαr (t.orbitReflection a)
  refine ⟨⟨hr, ?_⟩, ?_⟩
  · rcases IsRoot.height_pos_or_neg hr with h | h
    · exact h
    · obtain ⟨j, hj, rfl⟩ := t.eq_single_of_height_orbitReflection_smul_neg hαr hαp h
      exact absurd ⟨j, hj, rfl⟩ hαE
  · rintro ⟨j, hj, hjα⟩
    dsimp only at hjα
    have h : α = -(Pi.single j 1 : Fin t.tag.rank → ℤ) := by
      rw [← t.orbitReflection_smul_single hj, hjα, ← mul_smul, t.orbitReflection_mul_self,
        one_smul]
    rw [h, height_neg, height_single] at hαp
    omega

theorem image_orbitReflection_simpleComplementRoots
    (a : Fin t.foldedTag.rank) :
    (fun α => t.orbitReflection a • α) '' simpleComplementRoots t a =
      simpleComplementRoots t a := by
  refine Set.Subset.antisymm ?_ fun α hα => ⟨_, orbitReflection_smul_mem_simpleComplementRoots hα,
    by simp only [← mul_smul, t.orbitReflection_mul_self, one_smul]⟩
  rintro _ ⟨α, hα, rfl⟩
  exact orbitReflection_smul_mem_simpleComplementRoots hα

variable (σ) in
theorem mem_rootSpan_simpleOrbitRoots_iff
    (a : Fin t.foldedTag.rank) {g : ModGL t.tag K} :
    g ∈ rootSpan t.tag K (simpleOrbitRoots t a) ⊓ twistedFixedGroup t K σ ↔
      ∃ c : orbitField t K σ a, (orbitX t K σ a c : ModGL t.tag K) = g := by
  refine ⟨fun hg => ?_, ?_⟩
  · obtain ⟨c, hc⟩ := (orbitXHom_bijective t σ a).2 ⟨g, hg⟩
    exact ⟨c.toAdd, congrArg Subtype.val hc⟩
  · rintro ⟨c, rfl⟩
    exact orbitX_mem t σ a c

theorem graphFixedSimpleComplement_le
    (a : Fin t.foldedTag.rank) :
    graphFixedSimpleComplement t K σ a ≤ graphFixedPosUnipotent t K σ :=
  inf_le_inf_right _ (rootSpan_mono fun _ h => h.1)

theorem graphFixedSimpleComplement_subgroupOf_normal
    (a : Fin t.foldedTag.rank) :
    ((graphFixedSimpleComplement t K σ a).subgroupOf (graphFixedPosUnipotent t K σ)).Normal := by
  have hN := (positive_root_ideal_normality t.tag K (J := simpleComplementRoots t a)
    (S := {α | IsRoot t.tag α ∧ 0 < height α}) (fun _ h => h.1) (fun _ h => h)
    fun _ hα _ hβ _ _ hm hn hr =>
      nsmul_add_nsmul_mem_simpleComplementRoots a hα.2 hβ.1.2 hm hn hr).2
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnS, hnΓ⟩ := Subgroup.mem_inf.1 hn
  obtain ⟨hgU, hgΓ⟩ := Subgroup.mem_inf.1 g.2
  obtain ⟨hnU, -⟩ := Subgroup.mem_inf.1 n.2
  refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hgΓ hnΓ) (inv_mem hgΓ)⟩
  have h := hN.conj_mem ⟨n, hnU⟩ (Subgroup.mem_subgroupOf.2 hnS) ⟨g, hgU⟩
  exact Subgroup.mem_subgroupOf.1 h

variable (hσ : Function.Surjective σ)
include hσ

theorem exists_mul_orbitX_eq
    (a : Fin t.foldedTag.rank) {g : ModGL t.tag K}
    (hg : g ∈ graphFixedPosUnipotent t K σ) :
    ∃ v ∈ graphFixedSimpleComplement t K σ a, ∃ c : orbitField t K σ a,
      v * (orbitX t K σ a c : ModGL t.tag K) = g := by
  have hg' : g ∈ rootSpan t.tag K (simpleComplementRoots t a ∪ simpleOrbitRoots t a) ⊓
      twistedFixedGroup t K σ := by
    rw [simpleComplementRoots_union]
    exact hg
  obtain ⟨v, hv, u, hu, rfl⟩ := exists_mul_graphFixed_eq (simpleComplementRoots_pos a)
    (simpleOrbitRoots_pos a) (disjoint_simpleComplementRoots a) (simpleComplementRoots_closed a)
    (simpleOrbitRoots_closed a) hσ (simpleComplementRoots_perm a) (simpleOrbitRoots_perm a)
    (by rw [simpleComplementRoots_union]; exact fun α hα β hβ m n hm hn hr =>
      ⟨hr, (nsmul_add_nsmul_mem_simpleComplementRoots a hα.2 hβ.2 hm hn hr).1.2⟩) hg'
  obtain ⟨c, rfl⟩ := (mem_rootSpan_simpleOrbitRoots_iff σ a).1 hu
  exact ⟨v, hv, c, rfl⟩

theorem exists_orbitX_mul_eq
    (a : Fin t.foldedTag.rank) {g : ModGL t.tag K}
    (hg : g ∈ graphFixedPosUnipotent t K σ) :
    ∃ c : orbitField t K σ a, ∃ v ∈ graphFixedSimpleComplement t K σ a,
      (orbitX t K σ a c : ModGL t.tag K) * v = g := by
  have hg' : g ∈ rootSpan t.tag K (simpleOrbitRoots t a ∪ simpleComplementRoots t a) ⊓
      twistedFixedGroup t K σ := by
    rw [Set.union_comm, simpleComplementRoots_union]
    exact hg
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_graphFixed_eq (simpleOrbitRoots_pos a)
    (simpleComplementRoots_pos a) (disjoint_simpleComplementRoots a).symm
    (simpleOrbitRoots_closed a) (simpleComplementRoots_closed a) hσ (simpleOrbitRoots_perm a)
    (simpleComplementRoots_perm a)
    (by rw [Set.union_comm, simpleComplementRoots_union]; exact fun α hα β hβ m n hm hn hr =>
      ⟨hr, (nsmul_add_nsmul_mem_simpleComplementRoots a hα.2 hβ.2 hm hn hr).1.2⟩) hg'
  obtain ⟨c, rfl⟩ := (mem_rootSpan_simpleOrbitRoots_iff σ a).1 hu
  exact ⟨c, v, hv, rfl⟩

omit hσ

theorem eq_of_mul_orbitX_eq
    {a : Fin t.foldedTag.rank} {v v' : ModGL t.tag K}
    (hv : v ∈ graphFixedSimpleComplement t K σ a) (hv' : v' ∈ graphFixedSimpleComplement t K σ a)
    {c c' : orbitField t K σ a}
    (h : v * (orbitX t K σ a c : ModGL t.tag K) = v' * orbitX t K σ a c') : v = v' ∧ c = c' := by
  obtain ⟨h₁, h₂⟩ := eq_of_mul_rootSpan_eq K (simpleComplementRoots_pos a) (simpleOrbitRoots_pos a)
    (disjoint_simpleComplementRoots a) (simpleComplementRoots_closed a) (simpleOrbitRoots_closed a)
    (Subgroup.mem_inf.1 hv).1 (Subgroup.mem_inf.1 hv').1
    (Subgroup.mem_inf.1 (orbitX_mem t σ a c)).1 (Subgroup.mem_inf.1 (orbitX_mem t σ a c')).1 h
  exact ⟨h₁, orbitX_injective σ a (Subtype.ext h₂)⟩

theorem eq_of_orbitX_mul_eq
    {a : Fin t.foldedTag.rank} {v v' : ModGL t.tag K}
    (hv : v ∈ graphFixedSimpleComplement t K σ a) (hv' : v' ∈ graphFixedSimpleComplement t K σ a)
    {c c' : orbitField t K σ a}
    (h : (orbitX t K σ a c : ModGL t.tag K) * v = orbitX t K σ a c' * v') : c = c' ∧ v = v' := by
  obtain ⟨h₁, h₂⟩ := eq_of_mul_rootSpan_eq K (simpleOrbitRoots_pos a) (simpleComplementRoots_pos a)
    (disjoint_simpleComplementRoots a).symm (simpleOrbitRoots_closed a)
    (simpleComplementRoots_closed a) (Subgroup.mem_inf.1 (orbitX_mem t σ a c)).1
    (Subgroup.mem_inf.1 (orbitX_mem t σ a c')).1 (Subgroup.mem_inf.1 hv).1
    (Subgroup.mem_inf.1 hv').1 h
  exact ⟨orbitX_injective σ a (Subtype.ext h₁), h₂⟩

theorem eq_one_of_mem_graphFixedSimpleComplement
    {a : Fin t.foldedTag.rank} {c : orbitField t K σ a}
    (h : (orbitX t K σ a c : ModGL t.tag K) ∈ graphFixedSimpleComplement t K σ a) :
    (orbitX t K σ a c : ModGL t.tag K) = 1 := by
  have h0 : (orbitX t K σ a 0 : ModGL t.tag K) = 1 := by rw [orbitX_zero]; rfl
  have key := eq_of_mul_orbitX_eq h (one_mem _) (c := 0) (c' := c) (by rw [h0, mul_one, one_mul])
  rw [key.2] at h0
  exact h0

theorem canonicalRep_orbitReflection_mem_normalizer_graphFixedSimpleComplement
    (a : Fin t.foldedTag.rank) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
      Subgroup.normalizer (graphFixedSimpleComplement t K σ a : Set (ModGL t.tag K)) := by
  set n := canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)
  have hn : n ∈ twistedFixedGroup t K σ :=
    canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 (t.orbitReflection_mem a))
  have hmap := (canonical_weyl_root_transport t.tag K).1 (t.orbitReflection a)
    (simpleComplementRoots t a) fun α hα => hα.1.1
  rw [image_orbitReflection_simpleComplementRoots] at hmap
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨hgS, hgΓ⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hn hgΓ) (inv_mem hn)⟩
    rw [← hmap]
    exact ⟨g, hgS, rfl⟩
  · intro hg
    obtain ⟨hgS, hgΓ⟩ := Subgroup.mem_inf.1 hg
    rw [← hmap] at hgS
    obtain ⟨g', hg', hgg'⟩ := hgS
    have e : g = g' := by
      have hgg'' : n * g' * n⁻¹ = n * g * n⁻¹ := hgg'
      rwa [mul_left_inj, mul_right_inj, eq_comm] at hgg''
    refine Subgroup.mem_inf.2 ⟨e ▸ hg', ?_⟩
    have e' : g = n⁻¹ * (n * g * n⁻¹) * n := by group
    rw [e']
    exact mul_mem (mul_mem (inv_mem hn) hgΓ) hn

theorem canonicalRep_orbitReflection_mem_normalizer_graphFixedRootTorus
    (a : Fin t.foldedTag.rank) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
      Subgroup.normalizer (graphFixedRootTorus t K σ : Set (ModGL t.tag K)) := by
  have hN := graphFixedRootTorus_subgroupOf_normal t K σ
  have hn := canonicalRep_mem_graphFixedRootMonomial t K σ (t.orbitReflection_mem a)
  have hHN : graphFixedRootTorus t K σ ≤ graphFixedRootMonomial t K σ :=
    inf_le_inf_right _ (graphFixedTorus_le_graphFixedMonomial t K σ)
  have hconj : ∀ m ∈ graphFixedRootMonomial t K σ, ∀ h ∈ graphFixedRootTorus t K σ,
      m * h * m⁻¹ ∈ graphFixedRootTorus t K σ := fun m hm h hh =>
    Subgroup.mem_subgroupOf.1 (hN.conj_mem ⟨h, hHN hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨m, hm⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hconj _ hn h, fun hh => ?_⟩
  have := hconj _ (inv_mem hn) _ hh
  rwa [show (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))⁻¹ *
    (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * h *
      (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))⁻¹) *
    (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))⁻¹⁻¹ = h by group] at this

variable (σ) in
theorem image_conj_orbitX
    (a : Fin t.foldedTag.rank) :
    (fun g => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * g *
        (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))⁻¹) ''
      Set.range (fun c : orbitField t K σ a => (orbitX t K σ a c : ModGL t.tag K)) =
      Set.range (fun c : orbitField t K σ a => (orbitY t K σ a c : ModGL t.tag K)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨-c, ?_⟩
    simp only
    rw [← canonicalRep_orbitReflection_conj_orbitX t σ a (-c), neg_neg]
  · rintro _ ⟨c, rfl⟩
    exact ⟨_, ⟨-c, rfl⟩, canonicalRep_orbitReflection_conj_orbitX t σ a c⟩

theorem fixed_simple_positive_complement
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K)
    (a : Fin t.foldedTag.rank) :
    graphFixedSimpleComplement t K σ.toRingHom a ≤ graphFixedPosUnipotent t K σ.toRingHom ∧
    ((graphFixedSimpleComplement t K σ.toRingHom a).subgroupOf
      (graphFixedPosUnipotent t K σ.toRingHom)).Normal ∧
    (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K)) =
      (graphFixedSimpleComplement t K σ.toRingHom a : Set (ModGL t.tag K)) *
        Set.range (fun c : orbitField t K σ.toRingHom a =>
          (orbitX t K σ.toRingHom a c : ModGL t.tag K)) ∧
    (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K)) =
      Set.range (fun c : orbitField t K σ.toRingHom a =>
          (orbitX t K σ.toRingHom a c : ModGL t.tag K)) *
        (graphFixedSimpleComplement t K σ.toRingHom a : Set (ModGL t.tag K)) ∧
    (graphFixedSimpleComplement t K σ.toRingHom a : Set (ModGL t.tag K)) ∩
        Set.range (fun c : orbitField t K σ.toRingHom a =>
          (orbitX t K σ.toRingHom a c : ModGL t.tag K)) = {1} ∧
    (∀ v ∈ graphFixedSimpleComplement t K σ.toRingHom a,
      ∀ v' ∈ graphFixedSimpleComplement t K σ.toRingHom a, ∀ c c' : orbitField t K σ.toRingHom a,
        v * (orbitX t K σ.toRingHom a c : ModGL t.tag K) =
          v' * orbitX t K σ.toRingHom a c' → v = v' ∧ c = c') ∧
    (∀ v ∈ graphFixedSimpleComplement t K σ.toRingHom a,
      ∀ v' ∈ graphFixedSimpleComplement t K σ.toRingHom a, ∀ c c' : orbitField t K σ.toRingHom a,
        (orbitX t K σ.toRingHom a c : ModGL t.tag K) * v =
          orbitX t K σ.toRingHom a c' * v' → c = c' ∧ v = v') ∧
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
      Subgroup.normalizer (graphFixedSimpleComplement t K σ.toRingHom a : Set (ModGL t.tag K)) ∧
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
      Subgroup.normalizer (graphFixedRootTorus t K σ.toRingHom : Set (ModGL t.tag K)) ∧
    (fun g => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * g *
        (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a))⁻¹) ''
      Set.range (fun c : orbitField t K σ.toRingHom a =>
        (orbitX t K σ.toRingHom a c : ModGL t.tag K)) =
      Set.range (fun c : orbitField t K σ.toRingHom a =>
        (orbitY t K σ.toRingHom a c : ModGL t.tag K)) := by
  have hle := graphFixedSimpleComplement_le (K := K) (σ := σ.toRingHom) a
  have hx : ∀ c : orbitField t K σ.toRingHom a,
      (orbitX t K σ.toRingHom a c : ModGL t.tag K) ∈ graphFixedPosUnipotent t K σ.toRingHom :=
    orbitX_mem_graphFixedPosUnipotent t σ.toRingHom a
  refine ⟨hle, graphFixedSimpleComplement_subgroupOf_normal a,
    Set.Subset.antisymm (fun g hg => ?_) ?_, Set.Subset.antisymm (fun g hg => ?_) ?_, ?_,
    fun v hv v' hv' c c' h => eq_of_mul_orbitX_eq hv hv' h,
    fun v hv v' hv' c c' h => eq_of_orbitX_mul_eq hv hv' h,
    canonicalRep_orbitReflection_mem_normalizer_graphFixedSimpleComplement a,
    canonicalRep_orbitReflection_mem_normalizer_graphFixedRootTorus a,
    image_conj_orbitX σ.toRingHom a⟩
  · obtain ⟨v, hv, c, rfl⟩ := exists_mul_orbitX_eq σ.surjective a hg
    exact ⟨v, hv, _, ⟨c, rfl⟩, rfl⟩
  · rintro _ ⟨v, hv, _, ⟨c, rfl⟩, rfl⟩
    exact mul_mem (hle hv) (hx c)
  · obtain ⟨c, v, hv, rfl⟩ := exists_orbitX_mul_eq σ.surjective a hg
    exact ⟨_, ⟨c, rfl⟩, v, hv, rfl⟩
  · rintro _ ⟨_, ⟨c, rfl⟩, v, hv, rfl⟩
    exact mul_mem (hx c) (hle hv)
  · refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨hv, ⟨c, rfl⟩⟩
      exact eq_one_of_mem_graphFixedSimpleComplement hv
    · rintro _ rfl
      refine ⟨one_mem _, 0, ?_⟩
      show (orbitX t K σ.toRingHom a 0 : ModGL t.tag K) = 1
      rw [orbitX_zero]
      rfl

end CFSG.LieType.Chevalley
