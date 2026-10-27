module

public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer

public section

namespace CFSG.LargeExtraspecial.S14.TwoE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

variable {K : Type} [Field K]

theorem height_add_e6 (u v : Fin TwistTag.E6.tag.rank → ℤ) :
    height (u + v) = height u + height v := by
  simp [height, Finset.sum_add_distrib]

theorem height_sub_e6 (u v : Fin TwistTag.E6.tag.rank → ℤ) :
    height (u - v) = height u - height v := by
  simp [height, Finset.sum_sub_distrib]

theorem not_isRoot_single_add_single (i : Fin TwistTag.E6.tag.rank) :
    ¬IsRoot TwistTag.E6.tag (Pi.single i 1 + Pi.single i 1) := by
  intro h
  have e : (Pi.single i 1 + Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      (2 : ℤ) • Pi.single i 1 := by
    rw [two_smul]
  rw [e, isRoot_smul_single_iff] at h
  omega

theorem exists_cartan_eq_neg_one {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (hpos : 0 < height γ) (hne : γ ≠ e6HighestRoot) :
    ∃ i : Fin TwistTag.E6.tag.rank, ∑ j, TwistTag.E6.tag.cartan i j * γ j = -1 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hγ
  have h : (List.range TwistTag.E6.tag.rootCertificate.roots.length).all fun k =>
      decide (0 < height (TwistTag.E6.tag.rootCertificate.root k) →
        TwistTag.E6.tag.rootCertificate.root k ≠ e6HighestRoot →
          ∃ i : Fin TwistTag.E6.tag.rank,
            ∑ j, TwistTag.E6.tag.cartan i j * TwistTag.E6.tag.rootCertificate.root k j = -1) := by
    decide
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h k hk hpos hne

theorem isRoot_add_single_of_ne {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) (hpos : 0 < height γ) (hne : γ ≠ e6HighestRoot) :
    ∃ i : Fin TwistTag.E6.tag.rank, IsRoot TwistTag.E6.tag (γ + Pi.single i 1) := by
  obtain ⟨i, hi⟩ := exists_cartan_eq_neg_one hγ hpos hne
  refine ⟨i, ?_⟩
  have e : reflect TwistTag.E6.tag i γ = γ + Pi.single i 1 := by
    rw [reflect, hi, neg_smul, one_smul, sub_neg_eq_add]
  exact e ▸ IsRoot.reflect i hγ

@[expose] def rootsFrom (h : ℤ) : Finset (Fin TwistTag.E6.tag.rank → ℤ) :=
  (rootFinset TwistTag.E6.tag).filter fun β => 0 < height β ∧ h ≤ height β

theorem mem_rootsFrom {h : ℤ} {β : Fin TwistTag.E6.tag.rank → ℤ} :
    β ∈ rootsFrom h ↔ IsRoot TwistTag.E6.tag β ∧ 0 < height β ∧ h ≤ height β := by
  rw [rootsFrom, Finset.mem_filter, mem_rootFinset]

theorem exists_coords
    (h : ℤ) {z : ModGL TwistTag.E6.tag K} (hz : z ∈ heightSeries TwistTag.E6.tag K h) :
    ∃ (m : ℕ) (α : Fin m → Fin TwistTag.E6.tag.rank → ℤ) (c : Fin m → K),
      Function.Injective α ∧
      (∀ j, IsRoot TwistTag.E6.tag (α j) ∧ 0 < height (α j) ∧ h ≤ height (α j)) ∧
      z = (List.ofFn fun j => pinnedX TwistTag.E6.tag K (α j) (c j)).prod := by
  classical
  let e := (rootsFrom h).equivFin
  let α : Fin (rootsFrom h).card → Fin TwistTag.E6.tag.rank → ℤ := fun j => (e.symm j : _)
  have hα : Function.Injective α := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hαS : ∀ j, IsRoot TwistTag.E6.tag (α j) ∧ 0 < height (α j) ∧ h ≤ height (α j) :=
    fun j => mem_rootsFrom.1 (e.symm j).2
  have hrange : Set.range α =
      {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β ∧ h ≤ height β} := by
    ext β
    constructor
    · rintro ⟨j, rfl⟩
      exact hαS j
    · intro hβ
      exact ⟨e ⟨β, mem_rootsFrom.2 hβ⟩, by simp [α]⟩
  obtain ⟨c, -, hc⟩ := ((positive_root_collection TwistTag.E6.tag K).1 _
    (fun β hβ => ⟨hβ.1, hβ.2.1⟩) heightSeriesSet_closed α hα hrange).2.2 hz
  exact ⟨_, α, c, hα, hαS, hc.symm⟩

theorem rootCoord_prod [Finite K]
    {m : ℕ} {α : Fin m → Fin TwistTag.E6.tag.rank → ℤ} {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ ∧ 0 < height γ)
    (hα : ∀ j, IsRoot TwistTag.E6.tag (α j) ∧ 0 < height (α j) ∧ height γ ≤ height (α j))
    (c : Fin m → K) :
    rootCoord hγ (List.ofFn fun j => pinnedX TwistTag.E6.tag K (α j) (c j)).prod =
      ∑ j, if α j = γ then c j else 0 := by
  classical
  rw [rootCoord_list_prod hγ _ (fun g hg => ?_), List.map_ofFn, List.sum_ofFn]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply]
    split_ifs with hj
    · subst hj
      exact rootCoord_self hγ (c j)
    · exact rootCoord_pinnedX_of_ne hγ ⟨(hα j).1, (hα j).2.1⟩ (hα j).2.2 hj (c j)
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
    exact pinnedX_mem_rootSpan
      (S := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β ∧ height γ ≤ height β}) (hα j) (c j)

theorem mem_heightSeries_succ [Finite K]
    {h : ℤ} {z : ModGL TwistTag.E6.tag K} (hz : z ∈ heightSeries TwistTag.E6.tag K h)
    (h0 : ∀ γ (hγ : IsRoot TwistTag.E6.tag γ ∧ 0 < height γ), height γ = h →
      rootCoord hγ z = 0) :
    z ∈ heightSeries TwistTag.E6.tag K (h + 1) := by
  classical
  obtain ⟨m, α, c, hinj, hα, rfl⟩ := exists_coords h hz
  refine list_prod_mem fun g hg => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
  rcases (hα j).2.2.lt_or_eq with hlt | hh
  · exact pinnedX_mem_rootSpan
      (S := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β ∧ h + 1 ≤ height β})
      ⟨(hα j).1, (hα j).2.1, by omega⟩ (c j)
  · have hc := h0 (α j) ⟨(hα j).1, (hα j).2.1⟩ hh.symm
    rw [rootCoord_prod _ (fun k => ⟨(hα k).1, (hα k).2.1, hh.symm.le.trans (hα k).2.2⟩) c,
      Finset.sum_eq_single j (fun k _ hk => ite_eq_right fun h => hk (hinj h))
        (fun hj => absurd (Finset.mem_univ j) hj), ite_eq_left rfl] at hc
    rw [hc, pinnedX_zero]
    exact Subgroup.one_mem _

theorem rootCoord_commutator_pinnedX [Finite K] [CharP K 2]
    {γ β : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ ∧ 0 < height γ)
    (hβ : IsRoot TwistTag.E6.tag β ∧ 0 < height β) (hh : height β ≤ height γ + 1)
    (i : Fin TwistTag.E6.tag.rank) (c e : K) :
    rootCoord hβ ⁅pinnedX TwistTag.E6.tag K γ c, pinnedX TwistTag.E6.tag K (Pi.single i 1) e⁆ =
      if γ + Pi.single i 1 = β then c * e else 0 := by
  have hτ : TwistTag.E6.tag = .D4 ∨ TwistTag.E6.tag = .E6 ∨ TwistTag.E6.tag = .E7 ∨
      TwistTag.E6.tag = .E8 := .inr (.inl rfl)
  have hi := isRoot_single TwistTag.E6.tag i
  have hneg : γ ≠ -Pi.single i 1 := fun h => by
    have := hγ.2
    rw [h, height_neg, height_single] at this
    omega
  by_cases hγi : γ = Pi.single i 1
  · subst hγi
    have h1 : ⁅pinnedX TwistTag.E6.tag K (Pi.single i 1) c,
        pinnedX TwistTag.E6.tag K (Pi.single i 1) e⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm, ← pinnedX_add, ← pinnedX_add, add_comm]
    rw [h1, rootCoord_one, ite_eq_right]
    intro h
    exact not_isRoot_single_add_single i (h ▸ hβ.1)
  · obtain ⟨h1, h2⟩ := simply_laced_root_commutator_unit TwistTag.E6.tag hτ hγ.1 hi hγi hneg
    by_cases hr : IsRoot TwistTag.E6.tag (γ + Pi.single i 1)
    · obtain ⟨hC, hF⟩ := h1 hr
      have hC' : ((commConst TwistTag.E6.tag γ (Pi.single i 1) (1, 1) : ℤ) : K) = 1 := by
        rcases hC with h | h <;> rw [h]
        · exact Int.cast_one
        · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq]
      rw [hF K c e, hC', one_mul]
      have hht : height β ≤ height (γ + Pi.single i 1) := by
        rw [height_add_e6, height_single]
        exact hh
      by_cases hb : γ + Pi.single i 1 = β
      · rw [ite_eq_left hb]
        subst hb
        exact rootCoord_self hβ (c * e)
      · rw [ite_eq_right hb]
        exact rootCoord_pinnedX_of_ne hβ ⟨hr, by rw [height_add_e6, height_single]; omega⟩
          hht hb (c * e)
    · have hcomm := h2 hr K _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨e, rfl⟩)
      rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm.eq, rootCoord_one, ite_eq_right]
      intro hb
      exact hr (hb ▸ hβ.1)

theorem commutator_single_mem
    {h : ℤ} {z : ModGL TwistTag.E6.tag K} (hz : z ∈ heightSeries TwistTag.E6.tag K h)
    (i : Fin TwistTag.E6.tag.rank) (e : K) :
    ⁅z, pinnedX TwistTag.E6.tag K (Pi.single i 1) e⁆ ∈ heightSeries TwistTag.E6.tag K (h + 1) :=
  commutator_heightSeries_le K h 1 (Subgroup.commutator_mem_commutator hz
    (pinnedX_mem_rootSpan (S := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β ∧ 1 ≤ height β})
      ⟨isRoot_single _ i, by rw [height_single]; norm_num, by rw [height_single]⟩ e))

theorem rootCoord_commutator_prod [Finite K] [CharP K 2]
    {h : ℤ} {m : ℕ} {α : Fin m → Fin TwistTag.E6.tag.rank → ℤ}
    (hα : ∀ j, IsRoot TwistTag.E6.tag (α j) ∧ 0 < height (α j) ∧ h ≤ height (α j))
    (c : Fin m → K) (i : Fin TwistTag.E6.tag.rank) (e : K) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β ∧ 0 < height β) (hβh : height β = h + 1) :
    rootCoord hβ ⁅(List.ofFn fun j => pinnedX TwistTag.E6.tag K (α j) (c j)).prod,
        pinnedX TwistTag.E6.tag K (Pi.single i 1) e⁆ =
      ∑ j, if α j + Pi.single i 1 = β then c j * e else 0 := by
  have hzj : ∀ j, pinnedX TwistTag.E6.tag K (α j) (c j) ∈ heightSeries TwistTag.E6.tag K h :=
    fun j => pinnedX_mem_rootSpan
      (S := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β ∧ h ≤ height β}) (hα j) (c j)
  have hw : pinnedX TwistTag.E6.tag K (Pi.single i 1) e ∈ posUnipotent TwistTag.E6.tag K :=
    pinnedX_mem_rootSpan (S := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β})
      ⟨isRoot_single _ i, by rw [height_single]; norm_num⟩ e
  obtain ⟨-, hπ⟩ := commutator_prod_mem_and_coord (U := posUnipotent TwistTag.E6.tag K)
    (M := heightSeries TwistTag.E6.tag K (height β)) (heightSeries_le_normalizer K _)
    (rootCoord hβ) (fun x hx y hy => rootCoord_mul hβ hx hy)
    (fun g hg x hx => rootCoord_conj hβ hg hx)
    (List.ofFn fun j => pinnedX TwistTag.E6.tag K (α j) (c j))
    [pinnedX TwistTag.E6.tag K (Pi.single i 1) e]
    (fun g hg => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
      exact heightSeries_le_posUnipotent h (hzj j))
    (fun w hw' => by
      rw [List.mem_singleton] at hw'
      exact hw' ▸ hw)
    (fun g hg w hw' => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
      rw [List.mem_singleton] at hw'
      rw [hw', hβh]
      exact commutator_single_mem (hzj j) i e)
  rw [List.prod_singleton] at hπ
  rw [hπ, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp_apply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  exact rootCoord_commutator_pinnedX ⟨(hα j).1, (hα j).2.1⟩ hβ
    (by rw [hβh]; linarith [(hα j).2.2]) i (c j) e

theorem rootCoord_commutator_single [Finite K] [CharP K 2]
    {h : ℤ} {z : ModGL TwistTag.E6.tag K} (hz : z ∈ heightSeries TwistTag.E6.tag K h)
    (i : Fin TwistTag.E6.tag.rank) (e : K) {β γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β ∧ 0 < height β) (hβh : height β = h + 1)
    (hγ : IsRoot TwistTag.E6.tag γ ∧ 0 < height γ) (hγβ : γ + Pi.single i 1 = β) :
    rootCoord hβ ⁅z, pinnedX TwistTag.E6.tag K (Pi.single i 1) e⁆ = rootCoord hγ z * e := by
  obtain ⟨m, α, c, -, hα, rfl⟩ := exists_coords h hz
  have hγh : height γ = h := by
    rw [← hγβ, height_add_e6, height_single] at hβh
    omega
  rw [rootCoord_commutator_prod hα c i e hβ hβh,
    rootCoord_prod hγ (fun j => ⟨(hα j).1, (hα j).2.1, hγh ▸ (hα j).2.2⟩) c, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : α j = γ
  · rw [ite_eq_left (by rw [hj, hγβ]), ite_eq_left hj]
  · rw [ite_eq_right (fun h => hj (add_right_cancel (h.trans hγβ.symm))), ite_eq_right hj,
      zero_mul]

theorem rootCoord_commutator_single_of_not_isRoot [Finite K] [CharP K 2]
    {h : ℤ} {z : ModGL TwistTag.E6.tag K} (hz : z ∈ heightSeries TwistTag.E6.tag K h)
    (i : Fin TwistTag.E6.tag.rank) (e : K) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β ∧ 0 < height β) (hβh : height β = h + 1)
    (hγ : ¬IsRoot TwistTag.E6.tag (β - Pi.single i 1)) :
    rootCoord hβ ⁅z, pinnedX TwistTag.E6.tag K (Pi.single i 1) e⁆ = 0 := by
  obtain ⟨m, α, c, -, hα, rfl⟩ := exists_coords h hz
  rw [rootCoord_commutator_prod hα c i e hβ hβh]
  refine Finset.sum_eq_zero fun j _ => ite_eq_right fun hj => hγ ?_
  rw [← hj, add_sub_cancel_right]
  exact (hα j).1

end CFSG.LargeExtraspecial.S14.TwoE6
