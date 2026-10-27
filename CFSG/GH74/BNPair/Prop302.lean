module

public import CFSG.GH74.BNPair.Statements
public import CFSG.GH74.BNPair.Parabolic

public section

namespace CFSG.GH74.BNPair

universe u

variable {X : Type*} [Group X] {B N : Subgroup X} [(cartan B N).Normal]
  {S : Finset (WeylGroup B N)}

theorem IsTitsSystem.proposition302 (h : IsTitsSystem B N S) : Proposition302 B N S where
  iUnion_dc := h.iUnion_dc
  pairwiseDisjoint_dc := h.pairwise_disjoint_dc
  parabolic_subgroup J hJ :=
    ⟨parabolic B N (J : Set (WeylGroup B N)), h.coe_parabolic hJ, h.le_parabolic hJ,
      h.normalizer_parabolic hJ⟩
  parabolic_le_iff _ _ hJ hK := h.parabolic_le_iff hJ hK
  exists_parabolic _ hBP := h.exists_parabolic hBP
  parabolic_empty := by simpa using parabolic_empty (B := B) (N := N)
  parabolic_univ := h.parabolic_univ
  refined _ _ hn hlt := h.refined hn hlt

theorem prop30_2 : Prop30_2.{u} :=
  fun _ _ _ _ _ _ h => h.proposition302

end CFSG.GH74.BNPair
