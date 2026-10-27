module

public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

abbrev D4Vec : Type := Fin Tag.D4.rank → ℤ

abbrev D4Idx : Type := Fin Tag.D4.rank

instance (n : ℕ) : OfNat D4Idx n := inferInstanceAs (OfNat (Fin 4) n)

theorem d4_height_add (u v : D4Vec) : height (u + v) = height u + height v := by
  simp [height, Finset.sum_add_distrib]

section Coord

variable {K : Type} [Field K]


set_option linter.unusedSectionVars false

theorem d4_no_double : ∀ γ ∈ rootFinset Tag.D4, γ + γ ∉ rootFinset Tag.D4 := by decide +kernel

theorem d4_not_isRoot_double {γ : D4Vec} (hγ : IsRoot Tag.D4 γ) : ¬ IsRoot Tag.D4 (γ + γ) :=
  fun h => d4_no_double γ (mem_rootFinset.2 hγ) (mem_rootFinset.2 h)

@[expose] def d4RootsFrom (h : ℤ) : Finset D4Vec :=
  (rootFinset Tag.D4).filter fun β => 0 < height β ∧ h ≤ height β

@[expose] def d4RootsAt (h : ℤ) : Finset D4Vec :=
  (rootFinset Tag.D4).filter fun β => height β = h

theorem mem_d4RootsFrom {h : ℤ} {β : D4Vec} :
    β ∈ d4RootsFrom h ↔ IsRoot Tag.D4 β ∧ 0 < height β ∧ h ≤ height β := by
  rw [d4RootsFrom, Finset.mem_filter, mem_rootFinset]

theorem mem_d4RootsAt {h : ℤ} {β : D4Vec} :
    β ∈ d4RootsAt h ↔ IsRoot Tag.D4 β ∧ height β = h := by
  rw [d4RootsAt, Finset.mem_filter, mem_rootFinset]

theorem exists_coords_d4 (h : ℤ) {z : ModGL Tag.D4 K} (hz : z ∈ heightSeries Tag.D4 K h) :
    ∃ (l : List D4Vec) (c : D4Vec → K), l.Nodup ∧ (∀ γ, γ ∈ l ↔ γ ∈ d4RootsFrom h) ∧
      z = (l.map fun γ => pinnedX Tag.D4 K γ (c γ)).prod := by
  classical
  let e := (d4RootsFrom h).equivFin
  let α : Fin (d4RootsFrom h).card → D4Vec := fun j => (e.symm j : _)
  have hα : Function.Injective α := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hαS : ∀ j, IsRoot Tag.D4 (α j) ∧ 0 < height (α j) ∧ h ≤ height (α j) :=
    fun j => mem_d4RootsFrom.1 (e.symm j).2
  have hrange : Set.range α =
      {β | IsRoot Tag.D4 β ∧ 0 < height β ∧ h ≤ height β} := by
    ext β
    constructor
    · rintro ⟨j, rfl⟩
      exact hαS j
    · intro hβ
      exact ⟨e ⟨β, mem_d4RootsFrom.2 hβ⟩, by simp [α]⟩
  obtain ⟨c', -, hc'⟩ := ((positive_root_collection Tag.D4 K).1 _
    (fun β hβ => ⟨hβ.1, hβ.2.1⟩) heightSeriesSet_closed α hα hrange).2.2 hz
  refine ⟨List.ofFn α, fun γ => ∑ j, if α j = γ then c' j else 0, List.nodup_ofFn.2 hα,
    fun γ => ?_, ?_⟩
  · rw [List.mem_ofFn]
    constructor
    · rintro ⟨j, rfl⟩
      exact mem_d4RootsFrom.2 (hαS j)
    · intro hγ
      have h3 : γ ∈ Set.range α := by rw [hrange]; exact mem_d4RootsFrom.1 hγ
      exact h3
  · have hsum : ∀ j, (∑ k, if α k = α j then c' k else 0) = c' j := fun j => by
      rw [Finset.sum_eq_single j (fun k _ hk => if_neg (fun h => hk (hα h)))
        (fun hj => absurd (Finset.mem_univ j) hj), if_pos rfl]
    rw [← hc']
    simp only [List.map_ofFn]
    congr 2
    funext j
    simp only [Function.comp_apply, hsum]

theorem d4_height_pos_of_mem {h : ℤ} (hh : 0 < h) {γ : D4Vec} (hγ : γ ∈ d4RootsAt h) :
    γ ∈ d4RootsFrom h := by
  obtain ⟨h1, h2⟩ := mem_d4RootsAt.1 hγ
  exact mem_d4RootsFrom.2 ⟨h1, by omega, by omega⟩

open Classical in
@[expose] noncomputable def pc [Finite K] (γ : D4Vec) (g : ModGL Tag.D4 K) : K :=
  if h : IsRoot Tag.D4 γ ∧ 0 < height γ then rootCoord h g else 0

theorem pc_of_pos [Finite K] {γ : D4Vec} (hγ : IsRoot Tag.D4 γ ∧ 0 < height γ)
    (g : ModGL Tag.D4 K) : pc γ g = rootCoord hγ g := by
  rw [pc, dif_pos hγ]

theorem list_sum_ite_eq (l : List D4Vec) (hl : l.Nodup) (f : D4Vec → K) {γ : D4Vec} (hγ : γ ∈ l) :
    (l.map fun δ => if δ = γ then f δ else 0).sum = f γ := by
  classical
  rw [← List.sum_toFinset _ hl]
  simp [Finset.sum_ite_eq', hγ]

theorem rootCoord_prod_d4 [Finite K] (l : List D4Vec) (c : D4Vec → K) {γ : D4Vec}
    (hγ : IsRoot Tag.D4 γ ∧ 0 < height γ)
    (hα : ∀ δ ∈ l, IsRoot Tag.D4 δ ∧ 0 < height δ ∧ height γ ≤ height δ) :
    rootCoord hγ (l.map fun δ => pinnedX Tag.D4 K δ (c δ)).prod =
      (l.map fun δ => if δ = γ then c δ else 0).sum := by
  classical
  rw [rootCoord_list_prod hγ _ (fun g hg => ?_), List.map_map]
  · congr 1
    refine List.map_congr_left fun δ hδ => ?_
    simp only [Function.comp_apply]
    split_ifs with hδγ
    · subst hδγ
      exact rootCoord_self hγ (c δ)
    · exact rootCoord_pinnedX_of_ne hγ ⟨(hα δ hδ).1, (hα δ hδ).2.1⟩ (hα δ hδ).2.2 hδγ (c δ)
  · obtain ⟨δ, hδ, rfl⟩ := List.mem_map.1 hg
    exact pinnedX_mem_rootSpan
      (S := {β | IsRoot Tag.D4 β ∧ 0 < height β ∧ height γ ≤ height β}) (hα δ hδ) (c δ)

theorem rootCoord_commutator_pinnedX_d4 [Finite K] {γ δ β : D4Vec}
    (hγ : IsRoot Tag.D4 γ ∧ 0 < height γ) (hδ : IsRoot Tag.D4 δ ∧ 0 < height δ)
    (hβ : IsRoot Tag.D4 β ∧ 0 < height β) (hh : height β ≤ height γ + height δ) (c d : K) :
    rootCoord hβ ⁅pinnedX Tag.D4 K γ c, pinnedX Tag.D4 K δ d⁆ =
      if γ + δ = β then (commConst Tag.D4 γ δ (1, 1) : K) * c * d else 0 := by
  have hτ : Tag.D4 = .D4 ∨ Tag.D4 = .E6 ∨ Tag.D4 = .E7 ∨ Tag.D4 = .E8 := Or.inl rfl
  by_cases hγδ : γ = δ
  · subst hγδ
    have h1 : ⁅pinnedX Tag.D4 K γ c, pinnedX Tag.D4 K γ d⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm, ← pinnedX_add, ← pinnedX_add, add_comm]
    rw [h1, rootCoord_one, if_neg]
    intro h
    exact d4_not_isRoot_double hγ.1 (h ▸ hβ.1)
  · have hneg : γ ≠ -δ := fun h => by
      have h1 := hγ.2
      have h2 := hδ.2
      rw [h, height_neg] at h1
      omega
    obtain ⟨h1, h2⟩ := simply_laced_root_commutator_unit Tag.D4 hτ hγ.1 hδ.1 hγδ hneg
    by_cases hr : IsRoot Tag.D4 (γ + δ)
    · obtain ⟨-, hF⟩ := h1 hr
      rw [hF K c d]
      have hht : height β ≤ height (γ + δ) := by rw [d4_height_add]; exact hh
      by_cases hb : γ + δ = β
      · rw [if_pos hb]
        subst hb
        exact rootCoord_self hβ _
      · rw [if_neg hb]
        exact rootCoord_pinnedX_of_ne hβ ⟨hr, by rw [d4_height_add]; omega⟩ hht hb _
    · have hcomm := h2 hr K _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)
      rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm.eq, rootCoord_one, if_neg]
      intro hb
      exact hr (hb ▸ hβ.1)

theorem pc_prod_d4 [Finite K] {h : ℤ} (hh : 0 < h) {l : List D4Vec} (hl : l.Nodup)
    (hm : ∀ γ, γ ∈ l ↔ γ ∈ d4RootsFrom h) (c : D4Vec → K) {γ : D4Vec} (hγ : γ ∈ d4RootsAt h) :
    pc γ (l.map fun δ => pinnedX Tag.D4 K δ (c δ)).prod = c γ := by
  obtain ⟨h1, h2⟩ := mem_d4RootsAt.1 hγ
  have hpos : IsRoot Tag.D4 γ ∧ 0 < height γ := ⟨h1, by omega⟩
  rw [pc_of_pos hpos, rootCoord_prod_d4 l c hpos (fun δ hδ => by
    obtain ⟨a, b, e⟩ := mem_d4RootsFrom.1 ((hm δ).1 hδ)
    exact ⟨a, b, by omega⟩)]
  exact list_sum_ite_eq l hl c ((hm γ).2 (d4_height_pos_of_mem hh hγ))

theorem sum_roots_from_eq_at {M : Type*} [AddCommMonoid M] (h : ℤ) (f : D4Vec → M) (hf : ∀ γ ∈ d4RootsFrom h, γ ∉ d4RootsAt h → f γ = 0) (hh : 0 < h) :
    ∑ γ ∈ d4RootsFrom h, f γ = ∑ γ ∈ d4RootsAt h, f γ := by
  symm
  refine Finset.sum_subset (fun γ hγ => d4_height_pos_of_mem hh hγ) fun γ hγ hn => hf γ hγ hn

theorem rootCoord_commutator_pair [Finite K] {h k : ℤ} (hh : 0 < h) (hk : 0 < k)
    {z w : ModGL Tag.D4 K} (hz : z ∈ heightSeries Tag.D4 K h) (hw : w ∈ heightSeries Tag.D4 K k)
    {β : D4Vec} (hβ : IsRoot Tag.D4 β ∧ 0 < height β) (hβh : height β = h + k) :
    rootCoord hβ ⁅z, w⁆ = ∑ γ ∈ d4RootsAt h, ∑ δ ∈ d4RootsAt k,
      if γ + δ = β then (commConst Tag.D4 γ δ (1, 1) : K) * pc γ z * pc δ w else 0 := by
  classical
  obtain ⟨l₁, c₁, hn₁, hm₁, rfl⟩ := exists_coords_d4 h hz
  obtain ⟨l₂, c₂, hn₂, hm₂, rfl⟩ := exists_coords_d4 k hw
  have hzj : ∀ γ ∈ l₁, pinnedX Tag.D4 K γ (c₁ γ) ∈ heightSeries Tag.D4 K h := fun γ hγ =>
    pinnedX_mem_rootSpan (S := {β | IsRoot Tag.D4 β ∧ 0 < height β ∧ h ≤ height β})
      (mem_d4RootsFrom.1 ((hm₁ γ).1 hγ)) (c₁ γ)
  have hwj : ∀ δ ∈ l₂, pinnedX Tag.D4 K δ (c₂ δ) ∈ heightSeries Tag.D4 K k := fun δ hδ =>
    pinnedX_mem_rootSpan (S := {β | IsRoot Tag.D4 β ∧ 0 < height β ∧ k ≤ height β})
      (mem_d4RootsFrom.1 ((hm₂ δ).1 hδ)) (c₂ δ)
  obtain ⟨-, hπ⟩ := commutator_prod_mem_and_coord (U := posUnipotent Tag.D4 K)
    (M := heightSeries Tag.D4 K (height β)) (heightSeries_le_normalizer K _)
    (rootCoord hβ) (fun x hx y hy => rootCoord_mul hβ hx hy)
    (fun g hg x hx => rootCoord_conj hβ hg hx)
    (l₁.map fun γ => pinnedX Tag.D4 K γ (c₁ γ)) (l₂.map fun δ => pinnedX Tag.D4 K δ (c₂ δ))
    (fun g hg => by
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hg
      exact heightSeries_le_posUnipotent h (hzj γ hγ))
    (fun g hg => by
      obtain ⟨δ, hδ, rfl⟩ := List.mem_map.1 hg
      exact heightSeries_le_posUnipotent k (hwj δ hδ))
    (fun g hg g' hg' => by
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hg
      obtain ⟨δ, hδ, rfl⟩ := List.mem_map.1 hg'
      rw [hβh]
      exact commutator_heightSeries_le K h k (Subgroup.commutator_mem_commutator (hzj γ hγ)
        (hwj δ hδ)))
  have hterm : ∀ γ ∈ l₁, ∀ δ ∈ l₂, rootCoord hβ ⁅pinnedX Tag.D4 K γ (c₁ γ), pinnedX Tag.D4 K δ (c₂ δ)⁆ =
      if γ + δ = β then (commConst Tag.D4 γ δ (1, 1) : K) * c₁ γ * c₂ δ else 0 := by
    intro γ hγ δ hδ
    obtain ⟨a1, b1, e1⟩ := mem_d4RootsFrom.1 ((hm₁ γ).1 hγ)
    obtain ⟨a2, b2, e2⟩ := mem_d4RootsFrom.1 ((hm₂ δ).1 hδ)
    exact rootCoord_commutator_pinnedX_d4 ⟨a1, b1⟩ ⟨a2, b2⟩ hβ (by omega) _ _
  have e1 : ((l₁.map fun γ => pinnedX Tag.D4 K γ (c₁ γ)).map fun z =>
      ((l₂.map fun δ => pinnedX Tag.D4 K δ (c₂ δ)).map fun w => rootCoord hβ ⁅z, w⁆).sum).sum =
      (l₁.map fun γ => (l₂.map fun δ => if γ + δ = β then
        (commConst Tag.D4 γ δ (1, 1) : K) * c₁ γ * c₂ δ else 0).sum).sum := by
    simp only [List.map_map]
    congr 1
    refine List.map_congr_left fun γ hγ => ?_
    simp only [Function.comp_apply]
    congr 1
    refine List.map_congr_left fun δ hδ => ?_
    exact hterm γ hγ δ hδ
  rw [hπ, e1]
  have e2 : ∀ (l : List D4Vec) (hl : l.Nodup) (h' : ℤ) (hm : ∀ γ, γ ∈ l ↔ γ ∈ d4RootsFrom h')
      (f : D4Vec → K), (l.map f).sum = ∑ γ ∈ d4RootsFrom h', f γ := by
    intro l hl h' hm f
    rw [← List.sum_toFinset f hl]
    congr 1
    ext γ
    rw [List.mem_toFinset, hm]
  rw [e2 l₁ hn₁ h hm₁, Finset.sum_congr rfl fun γ _ => e2 l₂ hn₂ k hm₂ _]
  rw [sum_roots_from_eq_at h _ _ hh]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [sum_roots_from_eq_at k _ _ hk]
    · refine Finset.sum_congr rfl fun δ hδ => ?_
      rw [pc_prod_d4 hh hn₁ hm₁ c₁ hγ, pc_prod_d4 hk hn₂ hm₂ c₂ hδ]
    · intro δ hδ hδ'
      rw [if_neg]
      intro hb
      obtain ⟨-, hγh⟩ := mem_d4RootsAt.1 hγ
      obtain ⟨-, -, hδ2⟩ := mem_d4RootsFrom.1 hδ
      have : height δ ≠ k := fun e => hδ' (mem_d4RootsAt.2 ⟨(mem_d4RootsFrom.1 hδ).1, e⟩)
      have := congrArg height hb
      rw [d4_height_add] at this
      omega
  · intro γ hγ hγ'
    refine Finset.sum_eq_zero fun δ hδ => ?_
    rw [if_neg]
    intro hb
    obtain ⟨-, -, hγ2⟩ := mem_d4RootsFrom.1 hγ
    obtain ⟨-, -, hδ2⟩ := mem_d4RootsFrom.1 hδ
    have : height γ ≠ h := fun e => hγ' (mem_d4RootsAt.2 ⟨(mem_d4RootsFrom.1 hγ).1, e⟩)
    have := congrArg height hb
    rw [d4_height_add] at this
    omega

end Coord

end CFSG.LocalAnalysis.GLTheoremA
