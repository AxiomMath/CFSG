module

public import CFSG.ClassicalInvolution.Q3.Sec13StarM1
public import CFSG.ClassicalInvolution.Q3.Sec13StarM2

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

theorem dLeafStar_three (IH : ℕ → Prop) : DLeafStar 3 IH := by
  intro G _ _ Ω hc hZ _ hE4 K hK J hJ
  by_contra hJK
  obtain ⟨S, hKS⟩ := (hc.two K hK).exists_le_sylow
  obtain ⟨t, ht⟩ := (hc.hyp.omega1 J hJ).1
  have c : StarCex Ω K J t S := ⟨StarHyp.ofDCex hc hZ, hK, hJ, hJK, ht, hKS⟩
  by_cases hpair : ∀ L ∈ Ω, L ≤ (S : Subgroup G) → L = K ∨ L = conjSub t K
  · exact c.false_of_pair hE4 hpair
  · push_neg at hpair
    obtain ⟨K₁, hK₁, hK₁S, h₁, h₂⟩ := hpair
    exact c.false_of_third hK₁ hK₁S h₁ h₂

end CFSG.ClassicalInvolution.Q3.Sec13
