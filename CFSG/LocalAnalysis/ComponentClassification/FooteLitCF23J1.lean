module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Base
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.J1Centralizer

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup


theorem oneClass_j1 : OneClass Blueprint.NativeSporadic.J1 := by
  have h : OneClass Sporadic.Schreier.j1P :=
    oneClass_of_rep (t := Sporadic.Schreier.j1A1) fun x hx hx2 => by
      obtain ⟨c, hc, rfl⟩ := Sporadic.Schreier.j1_involution_conj x hx hx2
      exact ⟨c⁻¹, inv_mem hc, by group⟩
  exact h.of_mulEquiv Sporadic.Schreier.j1PermEquiv

theorem j1 : CF23InnerFusionFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .J1 := by
  intro G _ _ N hN hC hY α J hα hJN hJα _ _ _ hZ _
  obtain ⟨e⟩ := hY
  have e' : ↥N ≃* Blueprint.NativeSporadic.J1 := e
  have hαN : α ∈ N := by
    refine mem_of_conjNormal_mem_inner hC (mem_inner_of_congr e' ?_)
    obtain ⟨g, hg⟩ :=
      Sporadic.Schreier.at_j1_schreier.2.1 (MulAut.congr e' (MulAut.conjNormal α))
    exact ⟨g, hg.symm⟩
  exact concl_of_coset hα hJN hJα hZ (coset_of_inner hα hαN (oneClass_j1.of_mulEquiv e'))

end CFSG.ComponentClassification.GSThmB.CF23I
