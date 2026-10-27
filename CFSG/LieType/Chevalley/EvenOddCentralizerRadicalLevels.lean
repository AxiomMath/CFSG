module

public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public noncomputable section

namespace CFSG.LieType.Chevalley.EvenOddRadical

open CFSG.Blueprint.Chevalley
open scoped commutatorElement

variable {τ : Tag}

variable (τ) in
@[expose] def levelRoots (J : Set (Fin τ.rank)) (d : ℤ) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ 0 < height α ∧ d ≤ parabolicDegree τ J α}

theorem levelRoots_pos {J : Set (Fin τ.rank)} {d : ℤ} {α : Fin τ.rank → ℤ}
    (hα : α ∈ levelRoots τ J d) : IsRoot τ α ∧ 0 < height α :=
  ⟨hα.1, hα.2.1⟩

theorem parabolicDegree_nonneg_of_pos
    {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hpos : 0 < height α) : 0 ≤ parabolicDegree τ J α :=
  parabolicDegree_nonneg ((IsRoot.height_pos_iff hα).1 hpos)

theorem nsmul_add_nsmul_mem_levelRoots
    {J : Set (Fin τ.rank)} {d : ℤ} {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α ∧ 0 < height α) (hβ : β ∈ levelRoots τ J d) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hr : IsRoot τ (a • α + b • β)) : a • α + b • β ∈ levelRoots τ J d := by
  have hα0 := parabolicDegree_nonneg_of_pos (J := J) hα.1 hα.2
  have hβ0 := parabolicDegree_nonneg_of_pos (J := J) hβ.1 hβ.2.1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨hr, ?_, ?_⟩
  · rw [height_nsmul_add_nsmul]
    nlinarith [hα.2, hβ.2.1]
  · rw [parabolicDegree_add, parabolicDegree_nsmul, parabolicDegree_nsmul]
    nlinarith [hβ.2.2]

theorem nsmul_add_nsmul_mem_levelRoots_add
    {J : Set (Fin τ.rank)} {d e : ℤ}
    {α β : Fin τ.rank → ℤ} (hα : α ∈ levelRoots τ J d) (hβ : β ∈ levelRoots τ J e) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : IsRoot τ (a • α + b • β)) :
    a • α + b • β ∈ levelRoots τ J (d + e) := by
  have hα0 := parabolicDegree_nonneg_of_pos (J := J) hα.1 hα.2.1
  have hβ0 := parabolicDegree_nonneg_of_pos (J := J) hβ.1 hβ.2.1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨hr, ?_, ?_⟩
  · rw [height_nsmul_add_nsmul]
    nlinarith [hα.2.1, hβ.2.1]
  · rw [parabolicDegree_add, parabolicDegree_nsmul, parabolicDegree_nsmul]
    nlinarith [hα.2.2, hβ.2.2]

theorem levelRoots_anti {J : Set (Fin τ.rank)} {d d' : ℤ} (h : d ≤ d') :
    levelRoots τ J d' ⊆ levelRoots τ J d :=
  fun _ hα => ⟨hα.1, hα.2.1, h.trans hα.2.2⟩

theorem levelRoots_one
    (J : Set (Fin τ.rank)) : levelRoots τ J 1 = parabolicRadicalRoots τ J := by
  ext α
  constructor
  · intro hα
    exact mem_parabolicRadicalRoots_of_degree hα.1 hα.2.1 (by have := hα.2.2; omega)
  · intro hα
    exact ⟨hα.1.1, hα.1.2, one_le_parabolicDegree_of_mem hα⟩

theorem reflect_mem_levelRoots
    {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J) {d : ℤ} (hd : 1 ≤ d)
    {α : Fin τ.rank → ℤ} (hα : α ∈ levelRoots τ J d) : reflect τ j α ∈ levelRoots τ J d := by
  have hR : α ∈ parabolicRadicalRoots τ J := by
    rw [← levelRoots_one]
    exact levelRoots_anti hd hα
  obtain ⟨⟨hroot, hpos⟩, -⟩ := reflect_mem_parabolicRadicalRoots hj hR
  exact ⟨hroot, hpos, by rw [parabolicDegree_reflect hj]; exact hα.2.2⟩

theorem image_reflect_levelRoots
    {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J) {d : ℤ} (hd : 1 ≤ d) :
    reflect τ j '' levelRoots τ J d = levelRoots τ J d := by
  refine Set.Subset.antisymm ?_ fun α hα => ⟨reflect τ j α,
    reflect_mem_levelRoots hj hd hα, reflect_reflect τ j α⟩
  rintro _ ⟨α, hα, rfl⟩
  exact reflect_mem_levelRoots hj hd hα

theorem exists_levelRoots_eq_empty (J : Set (Fin τ.rank)) :
    ∃ D : ℤ, ∀ d, D ≤ d → levelRoots τ J d = ∅ := by
  obtain ⟨B, hB⟩ := (((finite_setOf_isRoot τ).subset fun _ (hα : IsRoot τ _ ∧ 0 < height _) =>
    hα.1).image (parabolicDegree τ J)).bddAbove
  refine ⟨B + 1, fun d hd => Set.eq_empty_of_forall_notMem fun α hα => ?_⟩
  have := hB ⟨α, ⟨hα.1, hα.2.1⟩, rfl⟩
  have := hα.2.2
  omega

variable (τ) (K : Type) [Field K]

@[expose] def levelRadical
    (J : Set (Fin τ.rank)) (d : ℤ) : Subgroup (ModGL τ K) :=
  rootSpan τ K (levelRoots τ J d)

variable {τ K}

theorem levelRadical_eq_closure
    (J : Set (Fin τ.rank)) (d : ℤ) :
    levelRadical τ K J d =
      Subgroup.closure {g | ∃ α ∈ levelRoots τ J d, ∃ c : K, pinnedX τ K α c = g} :=
  rootSpan_eq_closure K _

theorem pinnedX_mem_levelRadical
    {J : Set (Fin τ.rank)} {d : ℤ} {α : Fin τ.rank → ℤ} (hα : α ∈ levelRoots τ J d) (c : K) :
    pinnedX τ K α c ∈ levelRadical τ K J d :=
  pinnedX_mem_rootSpan hα c

theorem levelRadical_anti
    (J : Set (Fin τ.rank)) {d d' : ℤ} (h : d ≤ d') :
    levelRadical τ K J d' ≤ levelRadical τ K J d :=
  rootSpan_mono (levelRoots_anti h)

theorem levelRadical_one
    (J : Set (Fin τ.rank)) : levelRadical τ K J 1 = parabolicRadical τ K J := by
  rw [levelRadical, levelRoots_one, parabolicRadical]

theorem levelRadical_le_parabolicRadical
    (J : Set (Fin τ.rank)) {d : ℤ} (hd : 1 ≤ d) :
    levelRadical τ K J d ≤ parabolicRadical τ K J := by
  rw [← levelRadical_one]
  exact levelRadical_anti J hd

theorem levelRadical_le_posUnipotent
    (J : Set (Fin τ.rank)) (d : ℤ) : levelRadical τ K J d ≤ posUnipotent τ K :=
  rootSpan_le_posUnipotent fun _ hα => levelRoots_pos hα

theorem levelRadical_eq_bot
    {J : Set (Fin τ.rank)} {d : ℤ} (h : levelRoots τ J d = ∅) : levelRadical τ K J d = ⊥ := by
  rw [levelRadical, h]
  exact iSup₂_eq_bot.2 fun _ hα => absurd hα (Set.notMem_empty _)

theorem borelGroup_le_normalizer
    (J : Set (Fin τ.rank)) (d : ℤ) :
    borelGroup τ K ≤ Subgroup.normalizer (levelRadical τ K J d : Set (ModGL τ K)) :=
  sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1)
    (posUnipotent_le_normalizer_of_absorbs (fun _ hα => levelRoots_pos hα)
      fun _ hα _ hβ _ _ ha hb hr => nsmul_add_nsmul_mem_levelRoots hα hβ ha hb hr)

theorem weylElt_mem_normalizer
    {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J) {d : ℤ} (hd : 1 ≤ d) :
    weylElt τ K j 1 ∈ Subgroup.normalizer (levelRadical τ K J d : Set (ModGL τ K)) := by
  refine mem_normalizer_of_map_eq ?_
  rw [levelRadical, map_conj_weylElt_rootSpan K j 1 fun _ hα => hα.1,
    image_reflect_levelRoots hj hd]

theorem parabolicSubgroup_le_normalizer
    (J : Set (Fin τ.rank)) {d : ℤ}
    (hd : 1 ≤ d) :
    parabolicSubgroup τ K J ≤ Subgroup.normalizer (levelRadical τ K J d : Set (ModGL τ K)) :=
  sup_le (borelGroup_le_normalizer J d) ((Subgroup.closure_le _).2
    fun _ ⟨_, hj, he⟩ => he ▸ weylElt_mem_normalizer hj hd)

theorem parabolicLevi_le_normalizer
    (J : Set (Fin τ.rank)) {d : ℤ}
    (hd : 1 ≤ d) :
    parabolicLevi τ K J ≤ Subgroup.normalizer (levelRadical τ K J d : Set (ModGL τ K)) :=
  (parabolicLevi_le_parabolicSubgroup J).trans (parabolicSubgroup_le_normalizer J hd)

theorem commutator_levelRadical_le
    (J : Set (Fin τ.rank)) (d e : ℤ) :
    ⁅levelRadical τ K J d, levelRadical τ K J e⁆ ≤ levelRadical τ K J (d + e) := by
  have hs := levelRadical_le_posUnipotent (K := K) J d
  have ht := levelRadical_le_posUnipotent (K := K) J e
  have hN : posUnipotent τ K ≤
      Subgroup.normalizer (levelRadical τ K J (d + e) : Set (ModGL τ K)) :=
    le_sup_right.trans (borelGroup_le_normalizer J (d + e))
  rw [levelRadical_eq_closure] at hs ht ⊢
  rw [levelRadical_eq_closure J e]
  refine commutator_closure_le_of_le_normalizer hs ht hN ?_
  rintro _ ⟨α, hα, c, rfl⟩ _ ⟨β, hβ, d', rfl⟩
  by_cases hab : α = β
  · subst hab
    rw [commutatorElement_def, rootSubgroup_mul_comm K (Subgroup.subset_closure ⟨c, rfl⟩)
      (Subgroup.subset_closure ⟨d', rfl⟩), mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hmem := commutator_rootSubgroup_le K hα.1 hβ.1 hα.2.1 hβ.2.1 hab
    (Subgroup.commutator_mem_commutator (Subgroup.subset_closure ⟨c, rfl⟩)
      (Subgroup.subset_closure ⟨d', rfl⟩))
  have hle : (⨆ (γ : Fin τ.rank → ℤ) (_ : IsRoot τ γ ∧
      ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • α + b • β), rootSubgroup τ K γ) ≤
      rootSpan τ K (levelRoots τ J (d + e)) := by
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγr, a, b, ha, hb, rfl⟩ := hγ
    exact le_iSup₂_of_le _ (nsmul_add_nsmul_mem_levelRoots_add hα hβ ha hb hγr) le_rfl
  exact hle hmem

theorem card_levelRadical
    (J : Set (Fin τ.rank)) (d : ℤ) :
    Nat.card (levelRadical τ K J d) = Nat.card K ^ (levelRoots τ J d).ncard :=
  card_rootSpan (fun _ hα => levelRoots_pos hα) fun _ hα _ hβ _ _ ha hb hr =>
    nsmul_add_nsmul_mem_levelRoots (levelRoots_pos hα) hβ ha hb hr

end CFSG.LieType.Chevalley.EvenOddRadical
