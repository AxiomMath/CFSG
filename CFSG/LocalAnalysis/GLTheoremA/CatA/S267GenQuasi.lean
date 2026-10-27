module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
public import CFSG.Assembly.InCatalogConverse
public import CFSG.LocalAnalysis.GLTheoremA.Pump

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup glaPComponent_isComponent_of_le_layer)

section Quasi


theorem genCompQuasiOn_holds : GenCompQuasiOn fun _ => True := by
  intro p T _ _ d h _ x hx hx1 J hJ
  obtain ⟨e⟩ := h.iso
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group := (CFSG.Assembly.lie_finite_simple d).2
  have hperf : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hnc : ∃ a b : T, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    apply CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hJ
    rw [← hperf, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro b _
    exact hc b a
  have hlayer := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent T
    e.isSimpleGroup hnc d ⟨e⟩ p h.prime h.odd h.ne x hx hx1
  exact (glaPComponent_isComponent_of_le_layer hJ (hlayer J hJ.1 hperf)).1

theorem genCompQuasiOn_holds' (Q : TauCeti.LieTypeIndex → Prop) : GenCompQuasiOn Q :=
  fun p T _ _ d h _ => genCompQuasiOn_holds p T d h trivial

end Quasi

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
