module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx65

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7
open scoped commutatorElement Pointwise

namespace Fused8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem exists_SL2 (h44 : II4_44) (hf : Fused8 G z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) (hdK : ¬ IsDoubleCoverOfAlt (HatT K) 7) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧
      Nonempty (↥(imgBar z K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hc : IsPCompIn 2 (Cz z) K := hf.std.comp_isPCompIn hK
  have := h44 G hf.std.simple z hf.std.orderOf_z K hc (hf.std.comp_pRank hK)
  rcases this.1 with ⟨F, hF, hFin, ⟨hodd, -⟩, he⟩ | h7
  · obtain ⟨e⟩ := he
    obtain ⟨ι⟩ := imgBar_equiv hc
    exact ⟨F, hF, hFin, hodd, ⟨ι.symm.trans (e.trans (specialLinearGroupEquivStatedSL 2 F).symm)⟩⟩
  · exact absurd h7 hdK

end Fused8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
