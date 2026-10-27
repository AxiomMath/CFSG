module


public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WeakClosureNaturality

open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem map_weaklyClosed (e : MulAut G) {P0 P : Subgroup G} (h : IsWeaklyClosedIn P0 P) :
    IsWeaklyClosedIn (P0.map e.toMonoidHom) (P.map e.toMonoidHom) := by
  have conjSubgroup_map (e : MulAut G) (A : Subgroup G) (g : G) :
      conjSubgroup (A.map e.toMonoidHom) g = (conjSubgroup A (e.symm g)).map e.toMonoidHom := by
    unfold conjSubgroup
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  intro g hg
  rw [conjSubgroup_map] at hg ⊢
  have h1 : conjSubgroup P0 (e.symm g) ≤ P := by
    intro x hx
    have := hg ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := this
    have : y = x := e.injective hyx
    exact this ▸ hy
  rw [h _ h1]

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WeakClosureNaturality
