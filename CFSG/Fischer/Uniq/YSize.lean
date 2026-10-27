module

public import CFSG.Fischer.Uniq.MuSets

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

@[expose] def ySet (E : Set X) (e x : X) : Set X := {y | y ∈ E ∧ muSet E e x ⊆ LocalClass E y}

theorem mem_ySet {e x y : X} : y ∈ ySet E e x ↔ y ∈ E ∧ muSet E e x ⊆ LocalClass E y :=
  Iff.rfl

theorem Pair.subset_ySet (hP : Pair X E) {e x : X} (he : e ∈ E) (hx : x ∈ E)
    (hex : e * x ≠ x * e) : ({e, x, e * x * e} : Set X) ⊆ ySet E e x := by
  rintro y (rfl | rfl | rfl)
  · exact ⟨he, fun s hs => hs.1⟩
  · exact ⟨hx, fun s hs => hs.2⟩
  · refine ⟨Pair.mul_mul_mem hP he hx, fun s hs => ?_⟩
    rw [Pair.muSet_eq_inter hP he hx fun h => hex h.symm] at hs
    exact hs.2

theorem Pair.ncard_line (hP : Pair X E) {e x : X} (he : e ∈ E) (hex : e * x ≠ x * e) :
    ({e, x, e * x * e} : Set X).ncard = 3 := by
  rw [Set.ncard_insert_of_notMem, Set.ncard_pair (Pair.mul_mul_ne_right hP he hex).symm]
  rintro (h | h)
  · exact hex (by rw [h])
  · exact Pair.mul_mul_ne_left hP he hex h.symm

theorem Pair.ySet_eq_of_card (hP : Pair X E) {e x : X} (he : e ∈ E) (hx : x ∈ E)
    (hex : e * x ≠ x * e) (h : Nat.card (ySet E e x) = 3) : ySet E e x = {e, x, e * x * e} := by
  have := Pair.finite hP
  rw [Nat.card_coe_set_eq] at h
  exact (Set.eq_of_subset_of_ncard_le (Pair.subset_ySet hP he hx hex)
    (by rw [h, Pair.ncard_line hP he hex])).symm

theorem mem_ySet_iff_adj {e x y : E} : (y : X) ∈ ySet E e x ↔
    ∀ a : E, (commGraph E).Adj a e → (commGraph E).Adj a x → (commGraph E).Adj a y := by
  constructor
  · rintro ⟨-, h⟩ a hae hax
    exact mem_localClass_iff_adj.1 (h ⟨mem_localClass_iff_adj.2 hae, mem_localClass_iff_adj.2 hax⟩)
  · refine fun h => ⟨y.2, fun s hs => ?_⟩
    exact mem_localClass_iff_adj.2
      (h ⟨s, hs.1.1⟩ (mem_localClass_iff_adj.1 hs.1) (mem_localClass_iff_adj.1 hs.2))

theorem mem_ySet_map (β : commGraph E ≃g commGraph F) {e x y : E} (h : (y : X) ∈ ySet E e x) :
    (β y : Y) ∈ ySet F (β e) (β x) := by
  rw [mem_ySet_iff_adj] at h ⊢
  intro a hae hax
  obtain ⟨a, rfl⟩ := β.surjective a
  rw [β.map_adj_iff] at hae hax ⊢
  exact h a hae hax

theorem Pair.tau_of_graphIso (hE : Pair X E) (hF : Pair Y F) (β : commGraph E ≃g commGraph F)
    (hY : ∀ e x : Y, e ∈ F → x ∈ F → e * x ≠ x * e → ySet F e x ⊆ {e, x, e * x * e})
    (e f : E) : β (tauE hE e f) = tauE hF (β e) (β f) := by
  by_cases hef : (e : X) * f = f * e
  · rw [(Pair.tauE_eq_self_iff hE e f).2 hef, eq_comm, Pair.tauE_eq_self_iff hF]
    rcases commGraph_eq_or_adj hef with h | h
    · rw [h]
    · exact (β.map_adj_iff.2 h).2
  · have hne : β e ≠ β f := β.injective.ne fun h => hef (by rw [h])
    have hβef : (β e : Y) * β f ≠ β f * β e := fun h =>
      hef (β.map_adj_iff.1 ⟨hne, h⟩).2
    have hmem : (β (tauE hE e f) : Y) ∈ ySet F (β e) (β f) :=
      mem_ySet_map β (Pair.subset_ySet hE e.2 f.2 hef (by simp))
    rcases hY _ _ (β e).2 (β f).2 hβef hmem with h | h | h
    · have h' := congrArg Subtype.val (β.injective (Subtype.ext h))
      exact absurd h' (Pair.mul_mul_ne_left hE e.2 hef)
    · have h' := congrArg Subtype.val (β.injective (Subtype.ext h))
      exact absurd h' (Pair.mul_mul_ne_right hE e.2 hef)
    · exact Subtype.ext h

theorem Pair.mulEquiv_of_graphIso (hE : Pair X E) (hF : Pair Y F)
    (hZE : Subgroup.center X = ⊥) (hZF : Subgroup.center Y = ⊥) (β : commGraph E ≃g commGraph F)
    (hY : ∀ e x : Y, e ∈ F → x ∈ F → e * x ≠ x * e → ySet F e x ⊆ {e, x, e * x * e}) :
    ∃ φ : X ≃* Y, φ '' E = F :=
  exists_mulEquiv_of_tau hE hF hZE hZF β.toEquiv (Pair.tau_of_graphIso hE hF β hY)

end CFSG.Fischer
