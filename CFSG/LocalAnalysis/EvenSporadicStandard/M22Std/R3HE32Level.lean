module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsS0b
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3HE32Check

public section

namespace CFSG.EvenSporadicStandard.M22Std.E32Check

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck

theorem mem_extCands {I L : List Tab} {x : Tab} :
    x ∈ extCands I L ↔ x ∈ I ∧ x ∉ L ∧ ∀ z ∈ L, comm x z = true := by
  simp only [extCands, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]

theorem lvIdx_getD_of {k : Nat} (hk : 4 ≤ k) : lvIdx.getD k [] = [] := by
  have h : lvIdx.length = 4 := rfl
  exact List.getD_eq_default _ _ (by omega)

theorem elemLevel_eq_nil {T : List Tab} {k : Nat} (hk : 5 ≤ k) : elemLevel T k = [] := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [elemLevel, lvIdx_getD_of (by omega), List.map_nil]

theorem length_of_mem_elemLevel (hstep : ∀ k < 5, StepOK s0Tabs k) :
    ∀ k, ∀ L ∈ elemLevel s0Tabs k, L.length = 2 ^ (k + 1)
  | 0, L, hL => by
    rw [elemLevel, List.mem_singleton] at hL
    rw [hL]
    rfl
  | k + 1, L, hL => by
    rcases Nat.lt_or_ge k 5 with hk | hk
    · exact (hstep k hk).2 L hL
    · rw [elemLevel, lvIdx_getD_of (by omega)] at hL
      simp at hL

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
    {L : List Tab} (hLE : TabsIn E L) (hlt : L.length < Nat.card E) :
    ∃ x ∈ extCands (invTabs s0Tabs) L, TabsIn E (sortTabs (TabCheck.ext L x)) := by
  obtain ⟨e, he, hne⟩ := exists_not_mem_tabs E L hlt
  have hx : autTab e ∈ extCands (invTabs s0Tabs) L := by
    rw [mem_extCands, invTabs, List.mem_filter]
    refine ⟨⟨(mem_s0_iff e).1 (hE he), ?_⟩, hne, fun z hz => ?_⟩
    · simp only [decide_eq_true_eq]
      rw [← autTab_mul, hsq e he, autTab_one]
    · obtain ⟨f, hf, rfl⟩ := hLE z hz
      simp only [TabCheck.comm, decide_eq_true_eq]
      rw [← autTab_mul, ← autTab_mul, hc e he f hf]
  refine ⟨autTab e, hx, ?_⟩
  intro l hl
  rw [sortTabs, List.mem_mergeSort, TabCheck.ext, List.mem_append, List.mem_map] at hl
  rcases hl with hl | ⟨z, hz, rfl⟩
  · exact hLE l hl
  · obtain ⟨f, hf, rfl⟩ := hLE z hz
    exact ⟨e * f, E.mul_mem he hf, autTab_mul e f⟩

theorem elemLevel_cover (hstep : ∀ k < 5, StepOK s0Tabs k)
    {E : Subgroup (MulAut (Carrier .M22))} (hE : E ≤ s0)
    (hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α) (hsq : ∀ α ∈ E, α * α = 1)
    {τ : MulAut (Carrier .M22)} (hτ : τ ∈ E) (hτt : autTab τ = FusionCheck.tTab) :
    ∀ k, 2 ^ (k + 1) ≤ Nat.card E → ∃ L ∈ elemLevel s0Tabs k, TabsIn E L := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[idTab, FusionCheck.tTab], List.mem_singleton_self _, fun l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact ⟨1, E.one_mem, autTab_one⟩
    · exact ⟨τ, hτ, hτt⟩
  | succ k ih =>
    intro hk
    obtain ⟨L, hL, hLE⟩ :=
      ih (le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ (k + 1))) hk)
    have hlt : L.length < Nat.card E := by
      rw [length_of_mem_elemLevel hstep k L hL]
      exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self (k + 1))) hk
    obtain ⟨x, hx, hxE⟩ := elemStep_cover hE hc hsq hLE hlt
    rcases Nat.lt_or_ge k 5 with hk5 | hk5
    · exact ⟨_, (hstep k hk5).1 L hL x hx, hxE⟩
    · rw [elemLevel_eq_nil hk5] at hL
      exact absurd hL (List.not_mem_nil)

end CFSG.EvenSporadicStandard.M22Std
