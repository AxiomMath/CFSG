module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5g0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5e

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem omega_cases_B (ha : Ctx4P t L S x₁ x₂ lam rho tau) {B : Subgroup G} {ω : G}
    (hB : BData t x₁ x₂ lam rho tau B ω) :
    (∀ b ∈ B, b * b = 1) ∨ ∀ b ∈ B, b * b = 1 → b ∈ fourGrp x₁ x₂ :=
  have hc := ha.toCtx4L.toCtx4Q
  omega_one_cases B (fourGrp x₁ x₂) rho (rho_cubed hc) hB.V_le (card_fourGrp hc) hB.card
    (V_sq hc) hB.comm hB.rho_mem (fun b hb h => rho_fix_Q hc b (hB.le_Q hb) h)

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
