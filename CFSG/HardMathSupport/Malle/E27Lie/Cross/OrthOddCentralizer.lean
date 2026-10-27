module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthMain
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedRestrict
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.OrthOddPairs
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.OrthOddSL2

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.AGLEmbedding.ToralCensus

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem finrank_fixedSpace_lt (hx1 : x ≠ 1) : finrank K (fixedSpace x) < finrank K V := by
  refine lt_of_le_of_ne (Submodule.finrank_le _) fun h => hx1 ?_
  have htop : fixedSpace x = ⊤ := Submodule.eq_top_of_finrank_eq h
  ext v
  exact (mem_fixedSpace.1 (htop ▸ Submodule.mem_top : v ∈ fixedSpace x))

theorem perfectThreeIn_isometryCentralizer_odd (hx : OddOrderIsometry Q 3 x) (hx1 : x ≠ 1)
    (h2 : (2 : K) ≠ 0) (hn : 7 ≤ finrank K V) (hK : 4 ≤ Nat.card K) :
    PerfectThreeIn (isometryCentralizer Q x) := by
  by_cases h5 : 5 ≤ finrank K (fixedSpace x)
  · obtain ⟨P, hP⟩ := exists_two_hypPairs_odd h2 hx.polarBilin_fixed_nondegenerate h5
    refine (((perfectThreeIn_of_hypPairs_any hP hK).top_of_le le_rfl).map
      ((supportedBlock Q x (X - 1)).subtype.comp (fixedBlockEquiv hx).symm.toMonoidHom)
      ((Subgroup.subtype_injective _).comp (fixedBlockEquiv hx).symm.injective)).mono ?_
    rintro _ ⟨g, -, rfl⟩
    exact (supportedBlock_le_isometryCentralizer _) ((fixedBlockEquiv hx).symm g).2
  · obtain ⟨h, hh, hX, hrecX, hdeg, hdeg1, hsum⟩ :=
      exists_orth_factor hx (finrank_fixedSpace_lt hx1)
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hm : 2 ≤ primaryMultiplicity x.toLinearMap h := by omega
    refine ?_
    by_cases hself : h = reciprocalPolynomial h
    · exact (perfectThreeIn_orthSelfDual hx hh hX hself hdeg hm hK).mono
        (supportedBlock_le_isometryCentralizer _)
    · exact (perfectThreeIn_orthPaired hx hh hX hself hm hK).mono
        (supportedBlock_le_isometryCentralizer _)

end CFSG.HardMathSupport.Malle.E27Lie
