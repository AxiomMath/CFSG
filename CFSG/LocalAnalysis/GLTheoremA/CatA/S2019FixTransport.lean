module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalParts
import CFSG.GroupTheory.PLayer.CentralQuotient
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

variable {G G' : Type} [Group G] [Group G'] [Finite G]

theorem s2019FixCentralizes_of_congr {p : ℕ} (hp : p.Prime) (e : G ≃* G') (β : MulAut G)
    (h : S2019FixCentralizes p (MulAut.congr e β)) : S2019FixCentralizes p β := by
  haveI : Finite G' := Finite.of_equiv _ e.toEquiv
  intro L hL T hT hLT
  have hc : ∀ y ∈ fixSubgroup β ⊓ e.toMonoidHom.ker, ∀ x ∈ fixSubgroup β, x * y = y * x := by
    intro y hy x _
    have hy1 : y = 1 := e.injective (by rw [map_one]; exact (Subgroup.mem_inf.1 hy).2)
    rw [hy1, mul_one, one_mul]
  have hL' : GLAPComponent p (fixSubgroup (MulAut.congr e β)) (L.map e.toMonoidHom) := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr]
    exact (CFSG.glaPComponent_map_bijective_of_ker_le_center hp e.toMonoidHom hc).1 L hL
  have hT' : IsPGroup 2 (T.map e.toMonoidHom) := hT.map _
  have hLT' : L.map e.toMonoidHom ≤
      Subgroup.normalizer ((T.map e.toMonoidHom : Subgroup G') : Set G') :=
    (Subgroup.map_mono hLT).trans (Subgroup.le_normalizer_map _)
  have h1 := h _ hL' _ hT' hLT'
  rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h1
  exact h1

end CFSG.LocalAnalysis.GLTheoremA.S2019
