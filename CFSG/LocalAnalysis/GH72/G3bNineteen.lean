module

public import CFSG.LocalAnalysis.GH72.DDStructure

public section

namespace CFSG.GH72

open Subgroup

variable {G : Type*} [Group G]

theorem HasProductFusion.swap {S₁ S₂ : Subgroup G} (h : HasProductFusion S₁ S₂) :
    HasProductFusion S₂ S₁ where
  conj₁ := h.conj₂
  conj₂ := h.conj₁
  conj₃ := fun x hx y hy hxS2 hxS1 hyS2 hyS1 hx2 hy2 => by
    rw [sup_comm] at hx hy
    exact h.conj₃ x hx y hy hxS1 hxS2 hyS1 hyS2 hx2 hy2
  separate := fun x hx y hy hx2 hc => by
    rw [sup_comm] at hx hy
    exact ⟨(h.separate x hx y hy hx2 hc).2, (h.separate x hx y hy hx2 hc).1⟩

namespace DDDecomp

theorem swap {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂) (h₁ : IsDihNonab S₁) :
    DDDecomp S S₂ S₁ where
  sup_eq := by rw [sup_comm]; exact hd.sup_eq
  inf_eq := by rw [inf_comm]; exact hd.inf_eq
  commute := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact (mem_centralizer_iff.mp (hd.commute hy) x hx).symm
  dih₁ := isDih_of_isDihNonab hd.dih₂
  dih₂ := h₁

end DDDecomp

end CFSG.GH72
