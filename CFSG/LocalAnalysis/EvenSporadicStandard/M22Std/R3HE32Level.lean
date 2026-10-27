module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsS0b
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3HE32Check

public section

namespace CFSG.EvenSporadicStandard.M22Std.E32Check

open CFSG.EvenSporadicStandard.M22Std.TabCheck

theorem mem_extCands {I L : List Tab} {x : Tab} :
    x ∈ extCands I L ↔ x ∈ I ∧ x ∉ L ∧ ∀ z ∈ L, comm x z = true := by
  simp only [extCands, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]

theorem mem_elemStep {I : List Tab} {lv : List (List Tab)} {L' : List Tab} :
    L' ∈ elemStep I lv ↔ ∃ L ∈ lv, ∃ x ∈ extCands I L, sortTabs (ext L x) = L' := by
  simp only [elemStep, List.mem_dedup, List.mem_flatMap, List.mem_map]

theorem length_of_mem_elemLevel (T : List Tab) :
    ∀ k, ∀ L ∈ elemLevel T k, L.length = 2 ^ k := by
  intro k
  induction k with
  | zero =>
    intro L hL
    rw [elemLevel, List.mem_singleton] at hL
    rw [hL]
    rfl
  | succ k ih =>
    intro L hL
    obtain ⟨L0, hL0, x, -, rfl⟩ := mem_elemStep.1 hL
    rw [sortTabs, List.length_mergeSort, ext, List.length_append, List.length_map, ih L0 hL0,
      pow_succ]
    omega

end CFSG.EvenSporadicStandard.M22Std.E32Check

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.E32Check CFSG.Blueprint.NativeSporadic


@[expose] def TabsIn (E : Subgroup (MulAut (Carrier .M22))) (L : List Tab) : Prop :=
  ∀ l ∈ L, ∃ e ∈ E, autTab e = l

theorem exists_not_mem_tabs (E : Subgroup (MulAut (Carrier .M22))) (L : List Tab)
    (h : L.length < Nat.card E) : ∃ e ∈ E, autTab e ∉ L := by
  classical
  by_contra hcon'
  have hcon : ∀ e ∈ E, autTab e ∈ L := fun e he => by_contra fun hn => hcon' ⟨e, he, hn⟩
  have hsub : autTab '' (E : Set (MulAut (Carrier .M22))) ⊆ ↑L.toFinset := by
    rintro _ ⟨e, he, rfl⟩
    simpa using hcon e he
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_image_of_injective _ autTab_injective, Set.ncard_coe_finset,
    ← Nat.card_coe_set_eq] at h1
  exact absurd (h1.trans (List.toFinset_card_le L)) (not_le.2 h)

theorem mem_iff_autTab_mem {E : Subgroup (MulAut (Carrier .M22))} {L : List Tab}
    (hnd : L.Nodup) (hlen : L.length = Nat.card E) (hL : TabsIn E L)
    (a : MulAut (Carrier .M22)) : a ∈ E ↔ autTab a ∈ L := by
  have hsub : {b | autTab b ∈ L} ⊆ (E : Set (MulAut (Carrier .M22))) := by
    intro b hb
    obtain ⟨e, he, hel⟩ := hL _ hb
    rw [← autTab_injective hel]
    exact he
  have hncard : {b | autTab b ∈ L}.ncard = L.length :=
    ncard_preimage_mem_tabs autTab autTab_injective L hnd fun l hl =>
      (hL l hl).imp fun e he => he.2
  have heq : {b | autTab b ∈ L} = (E : Set (MulAut (Carrier .M22))) :=
    Set.eq_of_subset_of_ncard_le hsub
      (by rw [hncard, hlen]; exact (Nat.card_coe_set_eq (E : Set (MulAut (Carrier .M22)))).symm.le)
      (Set.toFinite _)
  rw [← SetLike.mem_coe, ← heq]
  rfl


theorem elemStep_cover {E : Subgroup (MulAut (Carrier .M22))} (hE : E ≤ s0)
    (hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α) (hsq : ∀ α ∈ E, α * α = 1)
    {lv : List (List Tab)} {L : List Tab} (hL : L ∈ lv) (hLE : TabsIn E L)
    (hlt : L.length < Nat.card E) :
    ∃ L' ∈ elemStep (invTabs s0Tabs) lv, TabsIn E L' := by
  obtain ⟨e, he, hne⟩ := exists_not_mem_tabs E L hlt
  have hx : autTab e ∈ extCands (invTabs s0Tabs) L := by
    rw [mem_extCands, invTabs, List.mem_filter]
    refine ⟨⟨(mem_s0_iff e).1 (hE he), ?_⟩, hne, fun z hz => ?_⟩
    · simp only [decide_eq_true_eq]
      rw [← autTab_mul, hsq e he, autTab_one]
    · obtain ⟨f, hf, rfl⟩ := hLE z hz
      simp only [TabCheck.comm, decide_eq_true_eq]
      rw [← autTab_mul, ← autTab_mul, hc e he f hf]
  refine ⟨sortTabs (TabCheck.ext L (autTab e)), mem_elemStep.2 ⟨L, hL, autTab e, hx, rfl⟩, ?_⟩
  intro l hl
  rw [sortTabs, List.mem_mergeSort, TabCheck.ext, List.mem_append, List.mem_map] at hl
  rcases hl with hl | ⟨z, hz, rfl⟩
  · exact hLE l hl
  · obtain ⟨f, hf, rfl⟩ := hLE z hz
    exact ⟨e * f, E.mul_mem he hf, autTab_mul e f⟩

theorem elemLevel_cover {E : Subgroup (MulAut (Carrier .M22))} (hE : E ≤ s0)
    (hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α) (hsq : ∀ α ∈ E, α * α = 1) :
    ∀ k, 2 ^ k ≤ Nat.card E → ∃ L ∈ elemLevel s0Tabs k, TabsIn E L := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[idTab], List.mem_singleton_self _, fun l hl => ⟨1, E.one_mem, ?_⟩⟩
    rw [List.mem_singleton.1 hl, autTab_one]
  | succ k ih =>
    intro hk
    obtain ⟨L, hL, hLE⟩ := ih (le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)) hk)
    refine elemStep_cover hE hc hsq hL hLE ?_
    rw [length_of_mem_elemLevel s0Tabs k L hL]
    exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)) hk

end CFSG.EvenSporadicStandard.M22Std
