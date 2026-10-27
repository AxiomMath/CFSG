module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.TabGroup

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.EvenSporadicStandard.M22Std.TabCheck

structure TabMap (G : Type*) [Group G] where
  tb : G → Tab
  mul : ∀ g h, tb (g * h) = tmul (tb g) (tb h)
  one : tb 1 = idTab
  inj : Function.Injective tb

namespace TabMap

variable {G : Type*} [Group G] (τ : TabMap G)

theorem tb_spanE (gs : List G) : (spanE gs).map τ.tb = span (gs.map τ.tb) := by
  induction gs with
  | nil => simp only [spanE, span, List.map_cons, τ.one, List.map]
  | cons g gs ih =>
    simp only [spanE, List.map_cons, span, TabCheck.ext, List.map_append, ← ih]
    congr 1
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun x _ => τ.mul g x

structure IsTabsOf (S : Subgroup G) (L : List Tab) : Prop where
  mem : ∀ x ∈ S, τ.tb x ∈ L
  exists_mem : ∀ l ∈ L, ∃ x ∈ S, τ.tb x = l

variable {τ} {S : Subgroup G} {L : List Tab}

theorem IsTabsOf.mem_iff (h : τ.IsTabsOf S L) (x : G) : x ∈ S ↔ τ.tb x ∈ L := by
  refine ⟨h.mem x, fun hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := h.exists_mem _ hx
  rw [← τ.inj hyx]
  exact hy

theorem IsTabsOf.card (h : τ.IsTabsOf S L) (hnd : L.Nodup) : Nat.card S = L.length := by
  rw [← natCard_subtype_mem L hnd]
  refine Nat.card_congr (Equiv.ofBijective (fun a : S => (⟨τ.tb a, h.mem a a.2⟩ : {x // x ∈ L}))
    ⟨fun a b hab => Subtype.ext (τ.inj (congrArg Subtype.val hab)), fun b => ?_⟩)
  obtain ⟨x, hx, hxb⟩ := h.exists_mem b.1 b.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxb⟩

theorem isTabsOf_closure [Finite G] (gs : List G)
    (hcl : ∀ l ∈ span (gs.map τ.tb), ∀ g ∈ gs, tmul l (τ.tb g) ∈ span (gs.map τ.tb)) :
    τ.IsTabsOf (Subgroup.closure {g | g ∈ gs}) (span (gs.map τ.tb)) := by
  refine ⟨fun x hx => ?_, fun l hl => ?_⟩
  · have hx' : x ∈ Submonoid.closure {g | g ∈ gs} := by
      rw [← Subgroup.closure_toSubmonoid_of_isOfFinOrder (fun x _ => isOfFinOrder_of_finite x)]
      exact hx
    have key : ∀ y ∈ Submonoid.closure {g | g ∈ gs},
        ∀ l : G, τ.tb l ∈ span (gs.map τ.tb) → τ.tb (l * y) ∈ span (gs.map τ.tb) := by
      intro y hy
      induction hy using Submonoid.closure_induction with
      | mem y hy =>
        intro l hl
        rw [τ.mul]
        exact hcl _ hl _ hy
      | one => intro l hl; rwa [mul_one]
      | mul y z _ _ hy hz => intro l hl; rw [← mul_assoc]; exact hz _ (hy l hl)
    have h1 : τ.tb (1 * x) ∈ span (gs.map τ.tb) := key x hx' 1 (by
      rw [τ.one]
      induction gs.map τ.tb with
      | nil => simp only [span, List.mem_singleton]
      | cons g gs ih => exact List.mem_append_left _ ih)
    rwa [one_mul] at h1
  · rw [← τ.tb_spanE, List.mem_map] at hl
    obtain ⟨x, hx, rfl⟩ := hl
    exact ⟨x, mem_of_mem_spanE _ (fun g hg => Subgroup.subset_closure hg) x hx, rfl⟩

end TabMap

end CFSG.EvenSporadicStandard.M22Std
