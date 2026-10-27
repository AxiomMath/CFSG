module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCNSCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ15G
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16O
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE17J
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18O
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACorA

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G]

theorem fzc_ns1_of
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (h : FzCCtx G t L S x₁ x₂ lam rho) (hA : CorAStatement)
    (hV : 2 ∣ (l41V S t x₁ x₂).index) (hV1 : 2 ∣ (l41V1 t x₁ x₂ rho lam).index) : False := by
  have p14 := fzc_ns_ph14 h hA hV
  have p15 : L41GPh15 t L S x₁ x₂ lam rho := ⟨p14, S4A.l41_q1_of p14 hV1⟩
  have p16 : L41GPh16 t L S x₁ x₂ lam rho := ⟨p15, S4A.l41_centq1_of p15⟩
  have p17 : L41GPh17 t L S x₁ x₂ lam rho := ⟨p16, S4A.l41_q1elem_of p16⟩
  exact S4A.l41_final_of p17 h.simple

section Closing


theorem fzc_ns1 : FzCNS1 := by
  intro G _ _ t L S x₁ x₂ lam rho h hV hV1
  exact fzc_ns1_of h corAStatement_of_certificates hV hV1

end Closing

end CFSG.OddStandard.SmallF3.FritzII
