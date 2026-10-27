module

public import CFSG.Foundations.GilmanSolomonGrammar

public section

namespace CFSG.GSGrammar

variable {G : Type*} [Group G] {vertex : Subgroup G → Prop}
  {edge : G → Subgroup G → G → Subgroup G → Prop} {J L : Subgroup G}

theorem Reach.vertex_right (h : Reach vertex edge J L)
    (hedge : ∀ a J b L, edge a J b L → vertex L) : vertex L := by
  rcases h.2.cases_tail with rfl | ⟨M, -, a, b, hC⟩
  · exact h.1
  · exact hedge _ _ _ _ hC

theorem Reach.le {α : Type*} [Preorder α] {f : Subgroup G → α} (h : Reach vertex edge J L)
    (hf : ∀ a J b L, edge a J b L → f J ≤ f L) : f J ≤ f L := by
  obtain ⟨-, hR⟩ := h
  induction hR with
  | refl => exact le_rfl
  | tail _ hst ih =>
    obtain ⟨a, b, hC⟩ := hst
    exact ih.trans (hf _ _ _ _ hC)

variable {zstar : ∀ H : Subgroup G, Subgroup H} [∀ H : Subgroup G, (zstar H).Normal]

theorem maximalComponent_of_le {α : Type*} [PartialOrder α] (f : Subgroup G → α)
    (hf : ∀ a J b L, edge a J b L → f J ≤ f L)
    (hiso : ∀ a J b L, edge a J b L → f J = f L → Nonempty (J ⧸ zstar J ≃* L ⧸ zstar L))
    (hJ : vertex J) (hmax : ∀ L, Reach vertex edge J L → f L ≤ f J) :
    MaximalComponent vertex (Reach vertex edge) zstar J := by
  refine ⟨hJ, fun L hL => ?_⟩
  obtain ⟨-, hR⟩ := hL
  induction hR with
  | refl => exact ⟨MulEquiv.refl _⟩
  | @tail M N hR' hst ih =>
    obtain ⟨a, b, hC⟩ := hst
    have hM : Reach vertex edge J M := ⟨hJ, hR'⟩
    obtain ⟨e₁⟩ := ih
    obtain ⟨e₂⟩ := hiso _ _ _ _ hC
      (le_antisymm (hf _ _ _ _ hC) ((hmax N (hM.tail hC)).trans (hM.le hf)))
    exact ⟨e₁.trans e₂⟩

theorem MaximalComponent.of_rel {reach : Subgroup G → Subgroup G → Prop}
    (hJ : MaximalComponent vertex reach zstar J)
    (htrans : ∀ J L M, reach J L → reach L M → reach J M) (hL : reach J L) (hLv : vertex L) :
    MaximalComponent vertex reach zstar L := by
  refine ⟨hLv, fun M hM => ?_⟩
  obtain ⟨e₁⟩ := hJ.2 L hL
  obtain ⟨e₂⟩ := hJ.2 M (htrans _ _ _ hL hM)
  exact ⟨e₁.symm.trans e₂⟩

theorem MaximalComponent.of_reach (hJ : MaximalComponent vertex (Reach vertex edge) zstar J)
    (hedge : ∀ a J b L, edge a J b L → vertex L) (hL : Reach vertex edge J L) :
    MaximalComponent vertex (Reach vertex edge) zstar L :=
  hJ.of_rel (fun _ _ _ h₁ h₂ => h₁.trans h₂) hL (hL.vertex_right hedge)

end CFSG.GSGrammar
