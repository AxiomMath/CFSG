module

public import CFSG.ClassicalInvolution.Q3.Q3TMFSSmall
public import CFSG.ClassicalInvolution.Q3.Q3TMFSBasic

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.Q3T.MFS

@[expose] def SmallOddLieTightMemberS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) → TwoSubgroupsFourGenerated (genFittingFStar G) →
    CFSG.Blueprint.OddLieType (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    ∀ t : G, t ∈ (S : Subgroup R).map R.subtype → orderOf t = 2 →
    R ≤ Subgroup.centralizer ({t} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal →
    IsPGroup 2 (R ⧸ classicalInvolutionOddCore R) →
    ∃ (z : G) (J : Subgroup G), IsClassicalMember3 J z

theorem smallRangeOuter_of_partsS (hGH : GH74SectionalModels) (hodd : SmallOddLieTightMemberS) :
    SmallRangeOuter := by
  intro Y _ _ T _ hsimp hnab hcent hF hfree h3 ⟨R, S, t, hD⟩
  obtain ⟨hFs, hFnab⟩ := genFittingFStar_simple ↥T hnab
  have hcase := Nobq.normalOddByQuaternionSmall_of_gh74' hGH ↥T hFnab R S hD.quat t hD.mem
    hD.order hD.cent hD.normal hD.twoGroup hF
  rcases hcase with h | h | h
  · obtain ⟨z', J, hJ⟩ := hodd ↥T hFnab hF h R S hD.quat t hD.mem hD.order hD.cent hD.normal
      hD.twoGroup
    exact hfree z' J hJ
  · exact false_of_sporadic_of_three_dvd_index T hnab hsimp hcent h3 (Or.inl h)
  · exact false_of_sporadic_of_three_dvd_index T hnab hsimp hcent h3 (Or.inr h)

end CFSG.ClassicalInvolution.Q3.TA3
