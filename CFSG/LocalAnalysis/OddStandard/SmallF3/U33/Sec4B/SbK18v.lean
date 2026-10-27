module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17E32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC17

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

theorem k18_E32_not_conj (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {w : G}
    (hw : w ∈ closure ({tau, om, lam} : Set G)) (g : G) : g * t * g⁻¹ ≠ w := by
  intro hgw
  obtain ⟨B, hB, hBe, hB32⟩ := l17_E32 hc
  have hwB : w ∈ B := hB hw
  haveI : IsMulCommutative ↥B := hBe.1
  have hBc : B ≤ centralizer ({g * t * g⁻¹} : Set G) := by
    intro b hb
    rw [hgw, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : B) ⟨w, hwB⟩)
  have h16 := c17_card_elemAbelian_conj_le hc.toCtx11.toCtx10 g hBc hBe
  omega

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
