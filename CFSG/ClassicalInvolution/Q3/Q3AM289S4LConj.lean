module

public import CFSG.ClassicalInvolution.Generic.Induction

public section

namespace CFSG.ClassicalInvolution.Q3.Q3AM.S4L

open CFSG.ClassicalInvolution.Generic

theorem conjSub_mem_fundamentalSubgroups {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {K : Type}
    [Group K] (D : CFSG.LieType.Universal.UniversalRootDatum K) {R : Subgroup K}
    (hR : R ∈ fundamentalSubgroups t D) (g : K) : conjSub g R ∈ fundamentalSubgroups t D := by
  obtain ⟨g₀, γ, hγ, rfl⟩ := hR
  exact ⟨g * g₀, γ, hγ, by rw [conjSub_mul]⟩

end CFSG.ClassicalInvolution.Q3.Q3AM.S4L
