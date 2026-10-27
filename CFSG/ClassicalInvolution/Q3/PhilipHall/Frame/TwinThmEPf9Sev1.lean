module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscSix63
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64A
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

namespace TwinThmE

section Pre
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_kPerp_of_twin_gen (hΩ : HypOmegaGen Ω) {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω)
    {z : G} (hzK : IsUniqueInvolution K z) (hzL : IsUniqueInvolution L z) : K ∈ KPerp Ω L := by
  by_cases hKL : K = L
  · exact Set.mem_insert_iff.mpr (Or.inl hKL)
  · refine Set.mem_insert_iff.mpr (Or.inr ⟨hK, hKL, ?_⟩)
    obtain ⟨R, hR, hRK, -⟩ := exists_mem_RSet_ge hK (isPGroup_two_bot (G := G)) bot_le
    exact ⟨R, hR, hRK.1, fun x hx =>
      Sec6Gen.le_normalizer_of_twin hΩ hK hL hKL hzK hzL (hRK.1 hx)⟩

end Pre

section

open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem inf_S_eq_of_mem_RSet (hΩ : HypOmegaGen Ω) {S : Sylow 2 G}
    {M R' : Subgroup G} (hM : M ∈ Ω) (hR' : R' ∈ RSet Ω) (hR'M : R' ≤ M)
    (hR'S : R' ≤ (S : Subgroup G)) : M ⊓ (S : Subgroup G) = R' := by
  have hsyl : IsSylow2In R' M := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hM hR' hR'M
  exact hsyl.eq_of_le (S.isPGroup'.to_le inf_le_right) inf_le_left (le_inf hR'M hR'S)

end

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
