module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsTab

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.EvenSporadicStandard.M22Std.TabCheck

namespace TabMap

variable {G : Type*} [Group G] {τ : TabMap G} {S : Subgroup G} {L : List Tab}

theorem isTabsOf_of_exists (τ : TabMap G) (S : Subgroup G) [Finite S] (L : List Tab)
    (hex : ∀ l ∈ L, ∃ x ∈ S, τ.tb x = l) (hnd : L.Nodup) (hcard : L.length = Nat.card S) :
    τ.IsTabsOf S L := by
  classical
  refine ⟨fun x hx => ?_, hex⟩
  set T : Set Tab := Set.range (fun x : S => τ.tb x) with hT
  have hTcard : T.ncard = L.length := by
    rw [hcard, hT, ← Set.image_univ, Set.ncard_image_of_injective _
      (fun a b h => Subtype.ext (τ.inj h)), Set.ncard_univ]
  have hsub : (↑L.toFinset : Set Tab) ⊆ T := by
    intro l hl
    obtain ⟨x, hx, rfl⟩ := hex l (List.mem_toFinset.1 hl)
    exact ⟨⟨x, hx⟩, rfl⟩
  have hLcard : (↑L.toFinset : Set Tab).ncard = L.length := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hTcard, hLcard]) (Set.finite_range _)
  have hxT : τ.tb x ∈ T := ⟨⟨x, hx⟩, rfl⟩
  rw [← heq] at hxT
  exact List.mem_toFinset.1 hxT

theorem IsTabsOf.card_subtype (h : τ.IsTabsOf S L) (hnd : L.Nodup) (P : S → Prop) (Q : Tab → Bool)
    (hPQ : ∀ x : S, P x ↔ Q (τ.tb x) = true) : Nat.card {x : S // P x} = L.countP Q := by
  rw [List.countP_eq_length_filter, ← natCard_subtype_mem _ (hnd.filter Q)]
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : {x : S // P x} => (⟨τ.tb x.1, List.mem_filter.2 ⟨h.mem x.1 x.1.2,
      (hPQ x.1).1 x.2⟩⟩ : {l : Tab // l ∈ L.filter Q})) ⟨fun a b hab => ?_, fun b => ?_⟩)
  · exact Subtype.ext (Subtype.ext (τ.inj (congrArg Subtype.val hab)))
  · obtain ⟨hbL, hbQ⟩ := List.mem_filter.1 b.2
    obtain ⟨x, hx, hxb⟩ := h.exists_mem b.1 hbL
    refine ⟨⟨⟨x, hx⟩, (hPQ ⟨x, hx⟩).2 (by rw [hxb]; exact hbQ)⟩, Subtype.ext hxb⟩

end TabMap

end CFSG.EvenSporadicStandard.M22Std
